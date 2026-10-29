import Verif.ProbeClosure

namespace verif

open Std (HashMap)

/-!
# Cell search with stored safe sets

An alternative to the split search of `ProbeClosure.lean` (`checkDProbing`).
The probe space is still cut into **cells** — "pick `cᵢ` wires from part `Pᵢ`,
for every `i`" — and a cell is still split along a certified safe set by the
product-of-Vandermonde decomposition (the all-safe sub-cell is dropped).  What
changes:

* **No union attempts.**  The split search first discharges the union of all
  wires of a cell; that rarely succeeds and costs a large engine call.
* **Every safe set is kept.**  Each certified seed is extended over *all* wires
  of the circuit (not only the cell's), and the result is stored.  Before the
  engine is called on a cell's seed, the store is consulted: a seed inside a
  stored set needs no engine call, and the cell is split along that set.  A
  cell lying entirely inside one stored set is dropped outright.
* **Automorphisms (optional, `CellEnv.sym`).**  When no stored set contains a
  seed, and only then, the search asks whether some automorphism `h` maps the
  seed into a stored set `S` (`h⁻¹(seed) ⊆ S`, so `seed ⊆ h(S)`).  `h(S)` is
  safe, because an automorphism maps safe sets to safe sets; it is stored as an
  ordinary set and the cell is split along it (`findThroughSymmetry`).  The
  symmetric root cells come from `Symmetry.lean`.  Without automorphisms the
  search uses no symmetry at all (`checkDProbingCells`).

Soundness: every probe set of size `d` lies in a root cell, or (with the
symmetric root) is mapped into one by an automorphism, which preserves safety.
A cell's probe sets are either inside the set it is split along — a certified
safe set, or an automorphic image of one, so every subset is
secret-independent — or in one of its child cells.  The search
ends when no cell is left; it reports INSECURE only when the engine fails to
certify a concrete seed.  Never decide a cell by a *union* of stored sets: a
union of safe sets need not be safe (memo Theorem 3).
-/

-- ============================================================
-- Cells and relabellings
-- ============================================================

/-- A cell: probe sets with `count` wires from each part (wire indices). -/
abbrev Cell := Array (Nat × Array Nat)

/-- Relabellings of the wire set as index tables over `0 … n-1`:
    `look[t][w]` is the image of wire `w` under relabelling `t`, or `n` where
    `t` is not valid on `w`.  `look[0]` must be the identity. -/
abbrev Relabellings := Array (Array Nat)

def identityLook (n : Nat) : Relabellings := #[Array.range n]

def binomial (n k : Nat) : Nat :=
  if k > n then 0 else (List.range k).foldl (fun acc i => acc * (n - i) / (i + 1)) 1

/-- Number of probe sets in a cell.  (Not `Cell.size`: `Cell` abbreviates
    `Array`, so that name would capture `cell.size`.) -/
def probeCount (c : Cell) : Nat :=
  c.foldl (fun acc (k, ws) => acc * binomial ws.size k) 1

/-- A set of wires as a bitset (bit `w % 64` of word `w / 64`). -/
abbrev WireMask := Array UInt64

def WireMask.empty (n : Nat) : WireMask := Array.replicate ((n + 63) / 64) 0

@[inline] def WireMask.test (m : WireMask) (w : Nat) : Bool :=
  (m[w / 64]! >>> (UInt64.ofNat (w % 64))) &&& 1 != 0

@[inline] def WireMask.set (m : WireMask) (w : Nat) : WireMask :=
  m.modify (w / 64) (· ||| ((1 : UInt64) <<< (UInt64.ofNat (w % 64))))

def WireMask.ofArray (n : Nat) (ws : Array Nat) : WireMask :=
  ws.foldl (fun m w => m.set w) (WireMask.empty n)

/-- `a ⊆ b`. -/
def WireMask.subset (a b : WireMask) : Bool := Id.run do
  for i in [0:a.size] do
    if a[i]! &&& ~~~(b[i]!) != 0 then return false
  return true

@[inline] def popcount64 (x : UInt64) : Nat :=
  let m1 : UInt64 := 0x5555555555555555
  let m2 : UInt64 := 0x3333333333333333
  let m4 : UInt64 := 0x0F0F0F0F0F0F0F0F
  let h  : UInt64 := 0x0101010101010101
  let x := x - ((x >>> (1 : UInt64)) &&& m1)
  let x := (x &&& m2) + ((x >>> (2 : UInt64)) &&& m2)
  let x := (x + (x >>> (4 : UInt64))) &&& m4
  ((x * h) >>> (56 : UInt64)).toNat

/-- `|a ∩ b|`. -/
def WireMask.interCount (a b : WireMask) : Nat := Id.run do
  let mut c := 0
  for i in [0:a.size] do
    c := c + popcount64 (a[i]! &&& b[i]!)
  return c

def WireMask.toArray (m : WireMask) (n : Nat) : Array Nat :=
  (Array.range n).filter m.test

/-- The child cells of `cell` when split along the wire mask `m`: every
    distribution of each part's count over its in-mask and out-of-mask wires,
    except the all-in-mask one.  Order: the recursion order of the split search
    (in-mask counts descending). -/
partial def childCells (cell : Cell) (m : WireMask) : Array Cell :=
  let rec go (idx : Nat) (acc : Cell) (allIn : Bool) : Array Cell :=
    if idx >= cell.size then (if allIn then #[] else #[acc])
    else
      let (cnt, ws) := cell[idx]!
      let inJ  := ws.filter m.test
      let outJ := ws.filter (fun w => !m.test w)
      (List.range (cnt + 1)).reverse.foldl (fun out i =>
        let part : Cell :=
          (if i == 0 then #[] else #[(i, inJ)]) ++ (if cnt - i == 0 then #[] else #[(cnt - i, outJ)])
        out ++ go (idx + 1) (acc ++ part) (allIn && i == cnt)) #[]
  go 0 #[] true

-- ============================================================
-- The store of safe sets
-- ============================================================

/-- Certified safe sets, indexed for subset lookups through relabellings.
    For each wire `v`, `bits[v]` is a bitset over pairs `(k, t)` (bit
    `k * nG + t`), set when `v` lies in stored set `k` relabelled by `t`.  A
    probe set `O` lies inside `t(S_k)` iff bit `(k, t)` is set for every wire of
    `O`, so a lookup is an AND of `|O|` bitsets. -/
structure SafeStore where
  n       : Nat
  nG      : Nat
  sets    : Array (Array Nat) := #[]
  bits    : Array (Array UInt64)
  /-- `masks[k * nG + t]` is the wire mask of `t(S_k)`. -/
  masks   : Array WireMask := #[]
  maxSize : Nat := 0

def SafeStore.empty (n nG : Nat) : SafeStore :=
  { n, nG, bits := Array.replicate n #[] }

/-- Add a safe set.  The store is taken apart first, so that `sets` and `bits`
    are unshared when they are updated: an update of a field projected out of a
    still-live structure copies the whole array (here: every stored set, on
    every add). -/
def SafeStore.add (st : SafeStore) (look : Relabellings) (S : Array Nat) : SafeStore := Id.run do
  let { n, nG, sets, bits, masks, maxSize } := st
  let k := sets.size
  let words := ((k + 1) * nG + 63) / 64
  let mut bits := bits
  let mut masks := masks
  for t in [0:nG] do
    let b := k * nG + t
    let wd := b / 64
    let bit : UInt64 := (1 : UInt64) <<< (UInt64.ofNat (b % 64))
    let f := look[t]!
    let mut m := WireMask.empty n
    for w in S do
      let v := f[w]!
      if v < n then
        m := m.set v
        let mut a := bits[v]!
        bits := bits.set! v #[]          -- keep `a` unshared, so the pushes below are in place
        while a.size < words do a := a.push 0
        a := a.set! wd (a[wd]! ||| bit)
        bits := bits.set! v a
    masks := masks.push m
  return { n, nG, sets := sets.push S, bits, masks, maxSize := max maxSize S.size }

@[inline] def lowestBit (x : UInt64) : Nat := Id.run do
  for i in [0:64] do
    if (x >>> (UInt64.ofNat i)) &&& 1 != 0 then return i
  return 64

/-- Up to `limit` pairs `(k, t)` with `O ⊆ t(S_k)`. -/
def SafeStore.find (st : SafeStore) (O : Array Nat) (limit : Nat) : Array (Nat × Nat) := Id.run do
  if O.isEmpty || st.sets.isEmpty then return #[]
  let words := (st.sets.size * st.nG + 63) / 64
  let mut out : Array (Nat × Nat) := #[]
  for j in [0:words] do
    let mut x : UInt64 := 0xFFFFFFFFFFFFFFFF
    for o in O do
      let a := st.bits[o]!
      x := x &&& (if j < a.size then a[j]! else 0)
      if x == 0 then break
    while x != 0 do
      let b := lowestBit x
      let p := j * 64 + b
      out := out.push (p / st.nG, p % st.nG)
      if out.size >= limit then return out
      x := x &&& (x - 1)
  return out

/-- The wire mask of `t(S_k)`. -/
@[inline] def SafeStore.mask (st : SafeStore) (k t : Nat) : WireMask :=
  st.masks[k * st.nG + t]!

-- ============================================================
-- The search
-- ============================================================

structure CellCounters where
  cells    : Nat := 0   -- cells visited
  skips    : Nat := 0   -- cells inside one stored set, dropped
  covers   : Nat := 0   -- seeds covered by a stored set (no engine call)
  deep     : Nat := 0   -- of which only through an automorphism
  engine   : Nat := 0   -- engine calls on seeds
  deriving Repr, Inhabited

structure CellEnv where
  fw          : HashMap String NodeId
  ws          : Array String
  pos         : HashMap String Nat
  cands       : Array (String × NodeId)
  /-- Relabellings the store indexes every set under (the identity). -/
  look        : Relabellings
  /-- Automorphisms other than the identity, as (forward, inverse) wire tables
      (`n` = not valid).  Consulted only when an engine call is the alternative. -/
  sym         : Array (Array Nat × Array Nat) := #[]
  allowFactor : Bool := true

structure CellState where
  g      : GlobalDAG
  stats  : Stats := {}
  store  : SafeStore
  cnt    : CellCounters := {}

/-- Among the hits, the relabelled stored set covering most of the cell's wires
    (`allM`, the cell's wire mask); the first such in hit order. -/
def bestCover (st : SafeStore) (hits : Array (Nat × Nat)) (allM : WireMask) : WireMask :=
  (hits.foldl (fun (best : Nat × WireMask) (k, t) =>
    let m := st.mask k t
    let sz := allM.interCount m
    if sz > best.1 then (sz, m) else best) (0, WireMask.empty st.n)).2

/-- Dominance through the automorphisms: the first `h` (in order) with
    `h⁻¹(seed) ⊆ S_k` for some stored `S_k`, i.e. `seed ⊆ h(S_k)`; among that
    `h`'s hits the `h(S_k)` covering most of the cell.  Returns the mask of the
    chosen `h(S_k)`. -/
def findThroughSymmetry (env : CellEnv) (store : SafeStore) (seed : Array Nat) (allM : WireMask)
    : Option WireMask := Id.run do
  let n := env.ws.size
  for (fwd, inv) in env.sym do
    let img := seed.map (inv[·]!)
    if img.any (· >= n) then continue
    let hits := store.find img 8
    if hits.isEmpty then continue
    let mut best := WireMask.empty n
    let mut bestSz := 0
    for (k, _) in hits do
      let m := WireMask.ofArray n ((store.sets[k]!).filterMap (fun w =>
        let v := fwd[w]!
        if v < n then some v else none))
      let sz := allM.interCount m
      if sz > bestSz then
        best := m
        bestSz := sz
    return some best
  return none

/-- One visit to a cell: the new state, a counterexample if the engine failed
    on the cell's seed, and the child cells.

    The state is taken apart first (`match s with …`) so that the DAG, the
    `Stats` and the store are each held exactly once while the engine and the
    store update them: a field projected out of a live structure is shared, and
    every array push or hash-map insert on a shared value copies it whole. -/
def visitCell (env : CellEnv) (s : CellState) (cell : Cell)
    : CellState × Option (Array String) × Array Cell :=
  match s with
  | { g, stats, store, cnt } =>
  let n := env.ws.size
  if cell.any (fun (c, ws) => c > 0 && ws.size < c) then ({ g, stats, store, cnt }, none, #[]) else
  let cell := cell.filter (fun (c, _) => c > 0)
  if cell.isEmpty then ({ g, stats, store, cnt }, none, #[]) else
  let cnt := { cnt with cells := cnt.cells + 1 }
  let all := cell.foldl (fun acc (_, ws) => acc ++ ws) #[]
  -- the whole cell inside one stored set: nothing to do
  if all.size ≤ store.maxSize && !(store.find all 1).isEmpty then
    ({ g, stats, store, cnt := { cnt with skips := cnt.skips + 1 } }, none, #[])
  else
  let allM := WireMask.ofArray n all
  let seed := cell.foldl (fun acc (c, ws) => acc ++ ws.extract 0 c) #[]
  let hits := store.find seed 8
  if !hits.isEmpty then
    let kids := childCells cell (bestCover store hits allM)
    ({ g, stats, store, cnt := { cnt with covers := cnt.covers + 1 } }, none, kids)
  else
  -- through the automorphisms, only now that an engine call is the alternative.
  -- The image found is safe; it is stored as an ordinary set for later lookups.
  match findThroughSymmetry env store seed allM with
  | some m =>
    let cnt := { cnt with covers := cnt.covers + 1, deep := cnt.deep + 1 }
    let store := store.add env.look (m.toArray n)
    let kids := childCells cell m
    ({ g, stats, store, cnt }, none, kids)
  | none =>
    let names := seed.map (env.ws[·]!)
    let (g, sec, coupling, stats) := checkChosenCoupling g env.fw stats names env.allowFactor
    let cnt := { cnt with engine := cnt.engine + 1 }
    if !sec then ({ g, stats, store, cnt }, some names, #[])
    else
      let (g, safe, anf) := couplingExtend g coupling names env.cands
      let S := safe.filterMap (env.pos[·]?)
      -- (no `recordExtension`: its collision report keys every safe set by a
      -- sorted string, which costs more than the lookup itself here)
      let stats := { stats with anfFallbacks := stats.anfFallbacks + anf }
      let stats := stats.addSuccess (safe.size - names.size)
      let kids := childCells cell (WireMask.ofArray n S)
      ({ g, stats, store := store.add env.look S, cnt }, none, kids)

/-- Depth-first over the cells, starting from `roots`. -/
def runCells (env : CellEnv) (g : GlobalDAG) (roots : Array Cell) : CellState × CheckResult := Id.run do
  let mut s : CellState := { g, store := SafeStore.empty env.ws.size env.look.size }
  let mut stack : Array Cell := roots.reverse
  while !stack.isEmpty do
    let cell := stack.back!
    stack := stack.pop
    let (s2, bad, kids) := visitCell env s cell
    s := s2
    match bad with
    | some w => return (s, .Insecure w)
    | none => stack := stack ++ kids.reverse
  return (s, .Secure)

def CellEnv.of (g : GlobalDAG) (look : Relabellings) (allowFactor : Bool := true) : CellEnv :=
  let ws := g.circuit.wireOrder
  { fw := g.wires, ws, pos := (ws.zipIdx).foldl (fun acc (w, i) => acc.insert w i) {},
    cands := candidatesOf g.wires ws, look, allowFactor }

/-- Verify `probingOrder`-probing security with the cell search, no symmetry.
    Same verdicts as `checkDProbing` (both are sound; they may name different
    counterexamples). -/
def checkDProbingCells (g : GlobalDAG) (probingOrder : Nat) (allowFactor : Bool := true)
    : GlobalDAG × CellState × CheckResult :=
  let env := CellEnv.of g (identityLook g.circuit.wireOrder.size) allowFactor
  let root : Cell := #[(probingOrder, Array.range env.ws.size)]
  let (s, r) := runCells env g #[root]
  (s.g, s, r)

/-- Every probe set of a cell, in order. -/
partial def cellProbes (cell : Cell) : Array (Array Nat) :=
  let rec combs (ws : Array Nat) (k start : Nat) (acc : Array Nat) (out : Array (Array Nat)) : Array (Array Nat) :=
    if acc.size == k then out.push acc
    else (List.range (ws.size - start)).foldl (fun o i => combs ws k (start + i + 1) (acc.push ws[start + i]!) o) out
  cell.foldl (fun sets (k, ws) =>
    let cs := combs ws k 0 #[] #[]
    sets.foldl (fun out p => cs.foldl (fun o c => o.push (p ++ c)) out) #[]) #[#[]]

/-- Brute-force audit of the root cells of a finished secure run: every probe set
    of every root cell lies inside `t(S)` for a stored `S` and a relabelling `t`
    of either store.  `(probe sets checked, uncovered)`, or `none` beyond `budget`. -/
def coverageAuditCells (stores : Array SafeStore) (roots : Array Cell) (budget : Nat := 2000000)
    : Option (Nat × Nat) :=
  if roots.foldl (fun a c => a + probeCount c) 0 > budget then none else
  some (roots.foldl (fun (res : Nat × Nat) c =>
    (cellProbes c).foldl (fun (r : Nat × Nat) P =>
      (r.1 + 1, if stores.any (fun st => !(st.find P 1).isEmpty) then r.2 else r.2 + 1)) res) (0, 0))

/-- Brute-force audit of a finished secure run: every probe set of size `d`
    lies inside `t(S)` for some stored `S` and relabelling `t`.  Returns
    `(probe sets checked, uncovered)`, or `none` when there are more than
    `budget` of them. -/
partial def coverageAudit (st : SafeStore) (n d : Nat) (budget : Nat := 2000000) : Option (Nat × Nat) :=
  if binomial n d > budget then none else
  let rec go (start : Nat) (acc : Array Nat) (res : Nat × Nat) : Nat × Nat :=
    if acc.size == d then
      (res.1 + 1, if (st.find acc 1).isEmpty then res.2 + 1 else res.2)
    else (List.range (n - start)).foldl (fun r i => go (start + i + 1) (acc.push (start + i)) r) res
  some (go 0 #[] (0, 0))

end verif
