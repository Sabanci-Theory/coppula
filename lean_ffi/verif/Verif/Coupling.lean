import Verif.Engine

namespace verif

open Std (HashMap)

/-!
# Coupling Replay, PIT, ANF, and Probe-Set Extension

Consumes the coupling `T` certified by the engine (`checkProbeCompleteT`):

* bit-sliced evaluation (`evalNode`, `mkEnv`, `evalCoupledEnv`) — 64 parallel
  𝔽₂ lanes over a *coupled* random environment, so `eval(w, env) = eval(w∘T)`;
* the PIT fast-reject built on it (phase 1 of the extension) — reject-only,
  never decides acceptance;
* exact ANF conversion with a monomial budget (phase 3 fallback);
* `couplingExtend` — grows a certified probe set into the certified-safe set:
  every candidate wire `w` with `w∘T` exactly secret-free.
-/

partial def evalNode (dag : DAG) (env : Array UInt64) (n : NodeId) (cache : Array (Option UInt64))
    : Array (Option UInt64) × UInt64 :=
  match cache[n]! with
  | some v => (cache, v)
  | none =>
    let (cache, v) := match dag.kind? n with
      | some (NodeKind.constVal b) => (cache, if b then 0xFFFFFFFFFFFFFFFF else 0)
      -- All leaves (Secret, Random, AND Public) read their lanes from `env`.
      -- Publics must stay symbolic here: evaluating them as a constant would
      -- blind the PIT to secret-dependence that only shows jointly with a
      -- public (e.g. `s·p` at `p = 0`), wasting exact-phase calls.
      | some (NodeKind.leaf _) => (cache, env[n]!)
      | some (NodeKind.xorNode ch) =>
        ch.foldl (fun (c, acc) chId =>
          let (c, vCh) := evalNode dag env chId c
          (c, acc ^^^ vCh)) (cache, 0)
      | some (NodeKind.andNode ch) =>
        ch.foldl (fun (c, acc) chId =>
          let (c, vCh) := evalNode dag env chId c
          (c, acc &&& vCh)) (cache, 0xFFFFFFFFFFFFFFFF)
      | _ => (cache, 0)
    (cache.set! n v, v)

/-- Coupled random environment: bind each random `r` to the value of its *net*
    image `σ(r)` under the whole coupling, so that `eval(w, env) = eval(w∘T)`.
    Since `σ(r_k) = σ_{>k}(e_k) + r_k`, the later substitutions must already be in
    `env` when we process `r_k` — hence **reverse** (right-to-left) folding.  Each
    step sets `env[r] := eval(e+r)` (`rt.2 = e+r`); no extra XOR (that was the
    `r ← e` collapse bug). -/
def evalCoupledEnv (dag : DAG) (coupling : Array (NodeId × NodeId)) (initialEnv : Array UInt64)
    : Array UInt64 :=
  coupling.foldr (fun rt env =>
    let cache : Array (Option UInt64) := Array.replicate dag.nextId none
    let (_, ve) := evalNode dag env rt.2 cache
    env.set! rt.1 ve)
    initialEnv

def mkEnv (dag : DAG) (secretsZero : Bool) : Array UInt64 := Id.run do
  let mut env := Array.replicate dag.nextId 0
  let mut seed : UInt64 := 0xDEADBEEFCAFEBAB0
  for i in [0:dag.nextId] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let v := mix64 seed
    if dag.isSecretNode i then
      env := env.set! i (if secretsZero then 0 else v)
    else
      env := env.set! i v
  env

-- ============================================================
-- ANF (algebraic normal form) — exact secret-freeness fallback
--
-- A monomial is a sorted, distinct array of leaf NodeIds (a multilinear
-- product); an ANF is a set of monomials (an F2 polynomial), keyed by the
-- monomial itself (`Array NodeId` is `Hashable`); two equal monomials cancel.
-- Used when the syntactic `tupleHasSecret` cannot see a product-cancellation
-- that the coupling induced (the case where our XOR-only replay under-detects
-- vs the true, expanded polynomial).
--
-- ANF is worst-case exponential, so conversion carries a monomial budget:
-- blowing it aborts the conversion and the caller must REJECT the candidate.
-- Rejection only costs extension yield, never soundness — acceptance always
-- rests on a completed, exact ANF.
-- ============================================================

abbrev ANF     := HashMap (Array NodeId) Unit
abbrev ANFMemo := HashMap NodeId ANF

/-- Monomial budget per ANF set.  Generous: the pipeline examples never exceed
    a handful of monomials; this only guards against a pathological candidate
    hanging the whole run. -/
def anfBudget : Nat := 65536

/-- Sorted union of two monomials (`x·x = x`, so repeated variables collapse). -/
def monoUnion (a b : Array NodeId) : Array NodeId :=
  let sorted := (a ++ b).qsort (· < ·)
  sorted.foldl (fun acc x =>
    if acc.isEmpty || acc[acc.size - 1]! != x then acc.push x else acc) #[]

/-- Toggle a monomial into an ANF set (F2: two copies cancel). -/
@[inline] def anfToggle (s : ANF) (m : Array NodeId) : ANF :=
  if s.contains m then s.erase m else s.insert m ()

/-- XOR (symmetric difference) of two ANF sets; `none` = budget blown. -/
def anfXor (a b : ANF) : Option ANF :=
  let s := b.fold (fun acc m _ => anfToggle acc m) a
  if s.size > anfBudget then none else some s

/-- Product of two ANF sets: distribute, unioning each monomial pair;
    `none` = budget blown (checked per distributed row, so intermediates stay
    within a `b.size` overshoot of the budget). -/
def anfAnd (a b : ANF) : Option ANF :=
  a.fold (fun acc mp _ =>
    match acc with
    | none   => none
    | some s =>
      let s := b.fold (fun s mq _ => anfToggle s (monoUnion mp mq)) s
      if s.size > anfBudget then none else some s)
    (some ({} : ANF))

/-- Full ANF of `n` over its leaves, memoised by NodeId (an ANF is context-free,
    so the memo is valid across roots and across candidates).  `none` = the
    budget was blown somewhere below `n`; failures are not memoised. -/
partial def toANF (dag : DAG) (memo : ANFMemo) (n : NodeId) : ANFMemo × Option ANF :=
  match memo[n]? with
  | some a => (memo, some a)
  | none   =>
    let (memo, a?) := match dag.kind? n with
      | some (NodeKind.constVal false) => (memo, some ({} : ANF))
      | some (NodeKind.constVal true)  => (memo, some (({} : ANF).insert #[] ()))
      | some (NodeKind.leaf _)         => (memo, some (({} : ANF).insert #[n] ()))
      | some (NodeKind.xorNode ch) =>
        ch.foldl (fun (m, acc?) c =>
          match acc? with
          | none     => (m, none)
          | some acc =>
            match toANF dag m c with
            | (m, none)    => (m, none)
            | (m, some ac) => (m, anfXor acc ac))
          (memo, some ({} : ANF))
      | some (NodeKind.andNode ch) =>
        ch.foldl (fun (m, acc?) c =>
          match acc? with
          | none     => (m, none)
          | some acc =>
            match toANF dag m c with
            | (m, none)    => (m, none)
            | (m, some ac) => (m, anfAnd acc ac))
          (memo, some (({} : ANF).insert #[] ()))
      | _ => (memo, some ({} : ANF))
    match a? with
    | some a => (memo.insert n a, some a)
    | none   => (memo, none)

/-- Exact secret-freeness via ANF, threading the NodeId→ANF memo (candidates in
    one extension share most of their sub-DAG, so share the memo too).
    `w` is secret-free iff no surviving monomial of its ANF contains a `Secret`
    leaf — sound *and* complete up to the budget (ANF is the canonical F2 form);
    a blown budget REJECTS (sound: only extension yield is lost). -/
def anfSecretFreeM (dag : DAG) (memo : ANFMemo) (w : NodeId) : ANFMemo × Bool :=
  match toANF dag memo w with
  | (memo, none)     => (memo, false)
  | (memo, some anf) =>
    (memo, anf.fold (fun free m _ => free && !m.any dag.isSecretNode) true)

/-- Memo-less convenience wrapper (demos/tests). -/
def anfSecretFree (dag : DAG) (w : NodeId) : Bool :=
  (anfSecretFreeM dag ({} : ANFMemo) w).2

/-- PIT values of `n` (both lane sets: secrets random / secrets zero) when the
    random leaves in `leafVal` take the given values and every other leaf its
    base value.  `mask` is the support bitset of the leaves in `leafVal`: a node
    whose random support misses `mask` keeps its stored base value, so only the
    cone of the relabelled randoms is re-evaluated.  `memo` is valid for one
    fixed `leafVal`. -/
partial def coneEval (dag : DAG) (mask : Nat) (leafVal : HashMap NodeId (UInt64 × UInt64))
    (memo : HashMap NodeId (UInt64 × UInt64)) (n : NodeId)
    : HashMap NodeId (UInt64 × UInt64) × (UInt64 × UInt64) :=
  if dag.support n &&& mask == 0 then (memo, (dag.valR[n]!, dag.valZ[n]!))
  else match memo[n]? with
  | some v => (memo, v)
  | none =>
    let (memo, v) := match dag.kind? n with
      | some (NodeKind.xorNode ch) =>
        ch.foldl (fun (acc : HashMap NodeId (UInt64 × UInt64) × (UInt64 × UInt64)) c =>
          let (m, (r, z)) := coneEval dag mask leafVal acc.1 c
          (m, (acc.2.1 ^^^ r, acc.2.2 ^^^ z))) (memo, (0, 0))
      | some (NodeKind.andNode ch) =>
        ch.foldl (fun (acc : HashMap NodeId (UInt64 × UInt64) × (UInt64 × UInt64)) c =>
          let (m, (r, z)) := coneEval dag mask leafVal acc.1 c
          (m, (acc.2.1 &&& r, acc.2.2 &&& z))) (memo, (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF))
      | _ => (memo, (leafVal[n]?.getD (dag.valR[n]!, dag.valZ[n]!)))
    (memo.insert n v, v)

/-- **Coupling-driven probe-set extension.**  Given the coupling `T` and the
    candidate observations `(name, node)`, return the names whose `w∘T` is
    secret-free — the certified-safe set `ŷ`.  `T` is a composition of
    measure-preserving relabels `r ← e+r`, so any wire it blinds joins the safe
    set (every subset stays `d`-probing secure).

    `chosen` is force-included (its joint secret-freeness is the engine's verdict;
    this is also what keeps `unsafeWires = wires \ safe` shrinking → termination).

    A candidate is **touched** if some step `r ← t` of `T` meets it: scanning `T`
    in order with the candidate's random support `S`, a step whose `r ∈ S`
    touches it and widens `S` by `t`'s support.  An untouched candidate satisfies
    `w∘T = w` exactly (substitution leaves an expression without `r` unchanged,
    node for node), so it needs no substitution and its PIT values are its stored
    base values.  Each candidate is then decided **exactly**, in three phases:
      1. PIT fast-reject — a bit-sliced 𝔽₂ identity test (secrets random vs zero)
         under the coupled leaf values; a lane disagreement means genuine
         secret-dependence (sound to reject).  For touched candidates only the
         cone of the relabelled randoms is re-evaluated (`coneEval`).
      2. syntactic secret-freeness of `w∘T` (the `secretDep` bit; for touched
         survivors after substituting `T`);
      3. ANF fallback (`anfSecretFreeM`) — exact, catches the product-cancellations
         phase 2 misses; a blown monomial budget rejects (sound).  Acceptance
         never rests on the probabilistic PIT.
    Same output as `couplingExtendRef`, without its per-call whole-DAG arrays. -/
def couplingExtend (g : GlobalDAG) (coupling : Array (NodeId × NodeId))
    (chosen : Array String) (candidates : Array (String × NodeId))
    : GlobalDAG × Array String × Nat := Id.run do
  let dag := g.dag
  let chosenSet : HashMap String Unit := chosen.foldl (fun m w => m.insert w ()) {}
  -- Coupled leaf values: σ(r_k) = eval(t_k) with the later steps already applied,
  -- hence right-to-left, as in `evalCoupledEnv`.
  let mask := coupling.foldl (fun m rt => m ||| dag.support rt.1) 0
  let mut leafVal : HashMap NodeId (UInt64 × UInt64) := {}
  for k in [0:coupling.size] do
    let (r, t) := coupling[coupling.size - 1 - k]!
    let (_, v) := coneEval dag mask leafVal {} t
    leafVal := leafVal.insert r v
  -- Phase 1, per candidate.  `memo` is shared: `leafVal` is fixed from here on.
  let mut memo : HashMap NodeId (UInt64 × UInt64) := {}
  let mut keep : Array String := #[]
  -- survivors in candidate order: (name, node, touched?)
  let mut survivors : Array (String × NodeId × Bool) := #[]
  for c in candidates do
    if chosenSet.contains c.1 then
      keep := keep.push c.1
    else
      let touched := (coupling.foldl (fun (S, hit) rt =>
        if S &&& dag.support rt.1 != 0 then (S ||| dag.support rt.2, true) else (S, hit))
        (dag.support c.2, false)).2
      if touched then
        let (m, (vR, vZ)) := coneEval dag mask leafVal memo c.2
        memo := m
        if vR == vZ then survivors := survivors.push (c.1, c.2, true)
      else if dag.valR[c.2]! == dag.valZ[c.2]! then
        survivors := survivors.push (c.1, c.2, false)
  -- Phases 2–3.  `T` is applied to the touched survivors only (one shared
  -- `substNode` memo per step); an untouched survivor is its own image.
  let mut g := g
  let touchedIdx := (Array.range survivors.size).filter (fun i => survivors[i]!.2.2)
  let mut images : Array NodeId := touchedIdx.map (fun i => survivors[i]!.2.1)
  if !images.isEmpty then
    for rt in coupling do
      let (g', imgs') := substTuple g images rt.1 rt.2
      g := g'
      images := imgs'
  let mut image : Array NodeId := survivors.map (·.2.1)
  for k in [0:touchedIdx.size] do
    image := image.set! touchedIdx[k]! images[k]!
  let mut anfMemo : ANFMemo := {}
  let mut anfCount : Nat := 0
  for i in [0:survivors.size] do
    let w' := image[i]!
    if !g.dag.dependsOnSecret w' then
      keep := keep.push survivors[i]!.1
    else
      let (m, free) := anfSecretFreeM g.dag anfMemo w'
      anfMemo := m
      if free then
        keep := keep.push survivors[i]!.1
        anfCount := anfCount + 1
  return (g, keep, anfCount)

/-- Reference implementation of `couplingExtend` (the pre-2026-10-28 version):
    whole-DAG environments and caches per call, every PIT survivor substituted.
    Same output as `couplingExtend`; kept for differential testing.

    **Coupling-driven probe-set extension.**  Given the coupling `T` and the
    candidate observations `(name, node)`, return the names whose `w∘T` is
    secret-free — the certified-safe set `ŷ`.  `T` is a composition of
    measure-preserving relabels `r ← e+r`, so any wire it blinds joins the safe
    set (every subset stays `d`-probing secure).

    `chosen` is force-included (its joint secret-freeness is the engine's verdict;
    this is also what keeps `unsafeWires = wires \ safe` shrinking → termination).
    Each other candidate is decided **exactly**, in three phases:
      1. PIT fast-reject — a bit-sliced F2 identity test on the coupled env; a lane
         disagreement means genuine secret-dependence (sound to reject).
      2. syntactic `substNode`+`tupleHasSecret` (XOR-canonicalisation only);
      3. ANF fallback (`anfSecretFreeM`) — exact, catches the product-cancellations
         phase 2 misses; a blown monomial budget rejects (sound).  Acceptance
         never rests on the probabilistic PIT. -/
def couplingExtendRef (g : GlobalDAG) (coupling : Array (NodeId × NodeId))
    (chosen : Array String) (candidates : Array (String × NodeId))
    : GlobalDAG × Array String × Nat := Id.run do
  let chosenSet : HashMap String Unit := chosen.foldl (fun m w => m.insert w ()) {}
  let envRand := evalCoupledEnv g.dag coupling (mkEnv g.dag false)
  let envZero := evalCoupledEnv g.dag coupling (mkEnv g.dag true)
  -- Phase 1: PIT fast-reject.  A lane disagreement between secrets-random and
  -- secrets-zero witnesses genuine secret-dependence, so rejecting is sound
  -- (it can only cost yield if the env is imperfect, never admit a bad wire).
  -- The two envs are fixed across candidates, so each env's eval cache is built
  -- once and shared: work done for one candidate's sub-DAG serves all others.
  let mut cacheR : Array (Option UInt64) := Array.replicate g.dag.nextId none
  let mut cacheZ : Array (Option UInt64) := Array.replicate g.dag.nextId none
  let mut keep : Array String := #[]
  let mut survivors : Array (String × NodeId) := #[]
  for c in candidates do
    if chosenSet.contains c.1 then
      keep := keep.push c.1
    else
      let (cR, vR) := evalNode g.dag envRand c.2 cacheR
      let (cZ, vZ) := evalNode g.dag envZero c.2 cacheZ
      cacheR := cR
      cacheZ := cZ
      if vR == vZ then
        survivors := survivors.push c
  -- Acceptance is EXACT.  Apply T to *all* survivors at once — one shared
  -- `substNode` memo per coupling step (`substTuple`), instead of replaying the
  -- whole coupling per candidate with fresh memos — then per image:
  --   Phase 2: syntactic `tupleHasSecret` (fast, XOR-canonicalisation only);
  --   Phase 3: ANF fallback (exact, catches product-cancellations Phase 2
  --   misses); its NodeId→ANF memo is shared across survivors.
  let mut g := g
  let mut roots : Array NodeId := survivors.map (·.2)
  for rt in coupling do
    let (g', roots') := substTuple g roots rt.1 rt.2
    g := g'
    roots := roots'
  let mut anfMemo : ANFMemo := {}
  let mut anfCount : Nat := 0
  for i in [0:survivors.size] do
    let w' := roots[i]!
    if !tupleHasSecret g.dag #[w'] then
      keep := keep.push survivors[i]!.1
    else
      let (m, free) := anfSecretFreeM g.dag anfMemo w'
      anfMemo := m
      if free then
        keep := keep.push survivors[i]!.1
        anfCount := anfCount + 1
  return (g, keep, anfCount)

end verif
