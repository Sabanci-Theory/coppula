import Std.Data.HashMap

namespace verif

open Std (HashMap)

/-!
# Hash-Consed N-ary Circuit DAG with Multiplicative Factoring
-/

-- ============================================================
-- Base types
-- ============================================================

inductive VarType
  | Secret : String → VarType
  | Random : String → VarType
  | Public : String → VarType
  deriving Repr, DecidableEq, Hashable, Inhabited

abbrev NodeId := Nat

/-- splitmix64 finalizer.  The raw state of a power-of-two-modulus LCG must not
    be used as PIT lanes directly: bit `k` of the state has period `2^(k+1)`
    (bit 0 alternates, bit 1 cycles with period 4, …), so the low lanes assign
    leaves highly structured, colliding values and carry almost no rejection
    power.  Mixing makes every output bit a pseudo-random function of the whole
    state, so all 64 lanes reject independently. -/
@[inline]
def mix64 (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- Single DAG node. -/
inductive NodeKind
  | xorNode  : Array NodeId → NodeKind
  | andNode  : Array NodeId → NodeKind
  | leaf     : VarType      → NodeKind
  | constVal : Bool         → NodeKind
  deriving Repr, DecidableEq, Hashable, Inhabited

-- ============================================================
-- DAG
-- ============================================================

/-- A hash-consed 𝔽₂-circuit DAG.

    Node ids are dense (`0 … nextId-1`), so per-node data lives in arrays indexed
    by id.  Nodes are immutable once allocated, so two syntactic facts about each
    node are computed once, from its children, when it is allocated:

    * `secretDep[n]` — some `Secret` leaf is reachable from `n`;
    * `rndSupp[n]`   — the set of `Random` leaves reachable from `n`, as a bitset
      (bit `i` ↔ `randoms[i]`).

    They turn the engine's reachability questions ("is this tuple secret-free?",
    "does `e` mention `r`?") into lookups.

    `valR[n]`/`valZ[n]` are the node's **base PIT values**: 64 parallel 𝔽₂
    evaluations with every leaf drawn from a fixed pseudo-random stream (the
    `i`-th draw goes to node `i`, so a leaf's value depends only on its id), and
    — in `valZ` — every secret set to 0.  The coupling extension's fast reject
    compares the two after relabelling (`Coupling.lean`). -/
structure DAG where
  nodes     : Array NodeKind          := #[]
  intern    : HashMap NodeKind NodeId := {}
  nextId    : NodeId                  := 0
  randoms   : Array NodeId            := #[]
  secrets   : Array NodeId            := #[]
  secretDep : Array Bool              := #[]
  rndSupp   : Array Nat               := #[]
  valR      : Array UInt64            := #[]
  valZ      : Array UInt64            := #[]
  pitSeed   : UInt64                  := 0xDEADBEEFCAFEBAB0
  deriving Inhabited

namespace DAG

-- sorted-array helpers

@[inline]
def lowerBound (arr : Array NodeId) (val : NodeId) : Nat :=
  Id.run do
    let mut lo : Nat := 0
    let mut hi : Nat := arr.size
    while lo < hi do
      let mid := (lo + hi) >>> 1
      if arr[mid]! < val then lo := mid + 1 else hi := mid
    return lo

@[inline]
def sortedMem (arr : Array NodeId) (val : NodeId) : Bool :=
  let i := lowerBound arr val
  i < arr.size && arr[i]! == val

@[inline]
def xorInsert (arr : Array NodeId) (val : NodeId) : Array NodeId :=
  let i := lowerBound arr val
  if i < arr.size && arr[i]! == val then arr.eraseIdx! i
  else arr.insertIdx! i val

@[inline]
def andInsert (arr : Array NodeId) (val : NodeId) : Array NodeId :=
  let i := lowerBound arr val
  if i < arr.size && arr[i]! == val then arr
  else arr.insertIdx! i val

-- allocation / interning

@[inline]
def kind? (dag : DAG) (id : NodeId) : Option NodeKind :=
  dag.nodes[id]?

/-- Allocate a fresh node (no interning check — see `internNode`).  Random and
    secret leaves are registered in `randoms`/`secrets` here, so that a random's
    bit index in `rndSupp` is its position in `randoms`. -/
def alloc (dag : DAG) (k : NodeKind) : DAG × NodeId :=
  let id := dag.nextId
  let (sd, sup) : Bool × Nat := match k with
    | NodeKind.leaf (VarType.Secret _) => (true, 0)
    | NodeKind.leaf (VarType.Random _) => (false, 1 <<< dag.randoms.size)
    | NodeKind.xorNode ch | NodeKind.andNode ch =>
      ch.foldl (fun (sd, sup) c => (sd || dag.secretDep[c]!, sup ||| dag.rndSupp[c]!)) (false, 0)
    | _ => (false, 0)
  let seed := dag.pitSeed * 6364136223846793005 + 1442695040888963407
  let (vr, vz) : UInt64 × UInt64 := match k with
    | NodeKind.leaf (VarType.Secret _) => (mix64 seed, 0)
    | NodeKind.leaf _                  => (mix64 seed, mix64 seed)
    | NodeKind.constVal b              => if b then (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF) else (0, 0)
    | NodeKind.xorNode ch =>
      ch.foldl (fun (r, z) c => (r ^^^ dag.valR[c]!, z ^^^ dag.valZ[c]!)) (0, 0)
    | NodeKind.andNode ch =>
      ch.foldl (fun (r, z) c => (r &&& dag.valR[c]!, z &&& dag.valZ[c]!))
        (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF)
  let dag := match k with
    | NodeKind.leaf (VarType.Random _) => { dag with randoms := dag.randoms.push id }
    | NodeKind.leaf (VarType.Secret _) => { dag with secrets := dag.secrets.push id }
    | _ => dag
  ({ dag with nodes     := dag.nodes.push k
              intern    := dag.intern.insert k id
              nextId    := id + 1
              secretDep := dag.secretDep.push sd
              rndSupp   := dag.rndSupp.push sup
              valR      := dag.valR.push vr
              valZ      := dag.valZ.push vz
              pitSeed   := seed }, id)

@[inline]
def internNode (dag : DAG) (k : NodeKind) : DAG × NodeId :=
  match dag.intern[k]? with
  | some id => (dag, id)
  | none    => dag.alloc k

@[inline]
def isSecretNode (dag : DAG) (id : NodeId) : Bool :=
  match dag.kind? id with
  | some (NodeKind.leaf (VarType.Secret _)) => true
  | _                                       => false

/-- Some secret leaf is reachable from `id` (syntactic dependence). -/
@[inline]
def dependsOnSecret (dag : DAG) (id : NodeId) : Bool :=
  dag.secretDep[id]!

/-- Bitset of the random leaves reachable from `id` (bit `i` ↔ `randoms[i]`). -/
@[inline]
def support (dag : DAG) (id : NodeId) : Nat :=
  dag.rndSupp[id]!

/-- `a` and `b` share no random leaf. -/
@[inline]
def disjointSupport (dag : DAG) (a b : NodeId) : Bool :=
  dag.support a &&& dag.support b == 0

-- flattening

def flattenXor (dag : DAG) (ids : Array NodeId) : Array NodeId :=
  ids.foldl (fun acc id =>
    match dag.kind? id with
    | some (NodeKind.constVal false) => acc                  -- 0 is the XOR identity
    | some (NodeKind.xorNode ch)     => ch.foldl xorInsert acc
    | _                              => xorInsert acc id)    -- 1 kept; cancels in pairs
    #[]

def flattenAnd (dag : DAG) (ids : Array NodeId) : Array NodeId × Bool :=
  ids.foldl (fun (acc, ann) id =>
    if ann then (acc, true)
    else match dag.kind? id with
    | some (NodeKind.constVal false) => (acc, true)
    | some (NodeKind.constVal true)  => (acc, ann)
    | some (NodeKind.andNode ch)     => (ch.foldl andInsert acc, ann)
    | _                              => (andInsert acc id, ann))
    (#[], false)

-- smart constructors

def mkConst (dag : DAG) (b : Bool) : DAG × NodeId :=
  dag.internNode (NodeKind.constVal b)

def mkLeaf (dag : DAG) (v : VarType) : DAG × NodeId :=
  dag.internNode (NodeKind.leaf v)

def mkXorCanon (dag : DAG) (ch : Array NodeId) : DAG × NodeId :=
  match ch.size with
  | 0 => dag.mkConst false
  | 1 => (dag, ch[0]!)
  | _ => dag.internNode (NodeKind.xorNode ch)

def mkAndCanon (dag : DAG) (ch : Array NodeId) (ann : Bool) : DAG × NodeId :=
  if ann then dag.mkConst false
  else match ch.size with
  | 0 => dag.mkConst true
  | 1 => (dag, ch[0]!)
  | _ => dag.internNode (NodeKind.andNode ch)

def mkXor (dag : DAG) (ids : Array NodeId) : DAG × NodeId :=
  dag.mkXorCanon (dag.flattenXor ids)

def mkAnd (dag : DAG) (ids : Array NodeId) : DAG × NodeId :=
  let (ch, ann) := dag.flattenAnd ids
  dag.mkAndCanon ch ann

-- factoring

def factorFreqs (dag : DAG) (xorCh : Array NodeId) : HashMap NodeId Nat :=
  xorCh.foldl (fun freq id =>
    match dag.kind? id with
    | some (NodeKind.andNode fac) => fac.foldl (fun m f => m.insert f (m[f]?.getD 0 + 1)) freq
    | _ => freq)
    {}

def bestFactor (freq : HashMap NodeId Nat) : Option NodeId :=
  (freq.fold (fun best fac cnt =>
    if cnt < 2 then best
    else match best with
         | none          => some (fac, cnt)
         | some (bf, bc) =>
           if cnt > bc || (cnt == bc && fac < bf) then some (fac, cnt)
           else best)
    none).map (·.fst)

def stripFactor (dag : DAG) (id factor : NodeId) : DAG × NodeId :=
  match dag.kind? id with
  | some (NodeKind.andNode fac) =>
    let i := lowerBound fac factor
    if i < fac.size && fac[i]! == factor
    then dag.mkAndCanon (fac.eraseIdx! i) false
    else (dag, id)
  | _ => (dag, id)

def applyFactor (dag : DAG) (xorCh : Array NodeId) (f : NodeId) : DAG × NodeId :=
  let (withF, without) := xorCh.partition (fun id =>
    match dag.kind? id with
    | some (NodeKind.andNode fac) => sortedMem fac f
    | _                           => false)
  let (dag, stripped) := withF.foldl (fun (d, acc) id =>
    let (d', s) := stripFactor d id f
    (d', acc.push s))
    (dag, #[])
  let (dag, innerXor) := dag.mkXor stripped
  let (dag, facTerm)  := dag.mkAnd #[f, innerXor]
  dag.mkXor (without.push facTerm)

partial def factorNode (dag : DAG) (id : NodeId) : DAG × NodeId :=
  match dag.kind? id with
  | some (NodeKind.xorNode xorCh) =>
    let (dag, xorCh') :=
      xorCh.foldl (fun (d, acc) cid =>
        let (d', cid') := factorNode d cid
        (d', acc.push cid'))
        (dag, #[])
    let (dag, id') := dag.mkXor xorCh'
    match dag.kind? id' with
    | some (NodeKind.xorNode ch) =>
      match bestFactor (factorFreqs dag ch) with
      | none   => (dag, id')
      | some f =>
        let (dag, id'') := applyFactor dag ch f
        factorNode dag id''
    | _ => (dag, id')
  | some (NodeKind.andNode andCh) =>
    let (dag, andCh') :=
      andCh.foldl (fun (d, acc) cid =>
        let (d', cid') := factorNode d cid
        (d', acc.push cid'))
        (dag, #[])
    dag.mkAnd andCh'
  | _ => (dag, id)

def factor (dag : DAG) (ids : Array NodeId) : DAG × Array NodeId :=
  ids.foldl (fun (d, roots) id =>
              let (d', id') := d.factorNode id
              (d', roots.push id'))
            (dag, #[])

-- pretty

partial def ppNode (dag : DAG) (id : NodeId) : String :=
  match dag.kind? id with
  | none                                    => s!"[invalid:{id}]"
  | some (NodeKind.constVal true)           => "1"
  | some (NodeKind.constVal false)          => "0"
  | some (NodeKind.leaf (VarType.Secret s)) => s
  | some (NodeKind.leaf (VarType.Random r)) => r
  | some (NodeKind.leaf (VarType.Public p)) => s!"p({p})"
  | some (NodeKind.xorNode ch)              =>
    "(" ++ String.intercalate " + " (ch.toList.map (ppNode dag)) ++ ")"
  | some (NodeKind.andNode ch)              =>
    "(" ++ String.intercalate " * " (ch.toList.map (ppNode dag)) ++ ")"

end DAG

end verif
