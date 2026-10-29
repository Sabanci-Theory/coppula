import Verif.CellSearch
import Verif.Automorphism

namespace verif

open Std (HashMap)

/-!
# Circuit symmetries for the cell search

Turns the automorphism analyser (`Automorphism.lean`) into what the cell search
(`CellSearch.lean`) consumes:

* **Groups.**  `symmetriesOf` returns up to two candidate groups — leaf
  relabellings of the (chain-contracted) netlist, and, when the sharing checks
  (S1)/(S2) hold, share permutations with shares as atoms — each listed in full
  by closing its verified generators (`closeGroup`, capped; a capped group is
  replaced by the largest closed subgroup found, `closeIncremental`).
* **Wire tables.**  A leaf relabelling acts on a wire by relabelling its
  expression; it maps wire `w` to `w'` exactly when the relabelled expression is
  the very node of `w'` (`nameMap`).  Elsewhere it is *not valid* on `w`
  (entry `n` in the table).  A relabelling preserves the joint distribution of
  any set of wires it is valid on, for every value of the secrets, so it maps
  safe sets to safe sets — the soundness of every use below.
* **Lookups.**  Every non-identity element, as a forward and an inverse wire
  table; the cell search maps a seed backwards through each to ask whether a
  stored safe set covers it (dominance detection).
* **Orbital root.**  `orbitalRoot` cuts the root cell into cells that contain at
  least one member of every orbit of probe sets: it pins the first wire of each
  orbit, recurses with the stabiliser of the pinned wire, and handles the wires
  the group cannot move with a smaller group or plainly (`obranch`,
  `pinClass`, `looseClass`, `bestSubgroup`) — and only where cutting a cell
  removes at least a quarter of its probe sets.  `rootCheck` verifies this by brute
  force: every probe set must map into a root cell under some element valid on it.

Ported from the 2026-10 theory-session prototype (see `.ai/MASKVERIF_COMPARISON.md`).
-/

def normLM (m : HashMap VarType VarType) : HashMap VarType VarType :=
  m.fold (fun acc k v => if k == v then acc else acc.insert k v) {}

def composeLM (a b : HashMap VarType VarType) : HashMap VarType VarType :=
  let keys := b.fold (fun s k _ => s.insert k ()) (a.fold (fun s k _ => s.insert k ()) ({} : HashMap VarType Unit))
  keys.fold (fun m v _ =>
    let bv := (b[v]?).getD v
    let abv := (a[bv]?).getD bv
    if abv == v then m else m.insert v abv) {}

def vkey : VarType → String
  | .Secret x => "s" ++ x
  | .Random r => "r" ++ r
  | .Public p => "p" ++ p

def keyLM (m : HashMap VarType VarType) : String :=
  String.intercalate ";" ((m.toArray.map (fun (k, v) => vkey k ++ ">" ++ vkey v)).qsort (· < ·)).toList

def closeGroup (gens : Array (HashMap VarType VarType)) (cap : Nat) : Array (HashMap VarType VarType) × Bool := Id.run do
  let gens := gens.map normLM
  -- number the leaves that any generator moves
  let mut leaves : Array VarType := #[]
  let mut num : HashMap VarType Nat := {}
  for g in gens do
    for (k, v) in g.toArray do
      for x in [k, v] do
        if !num.contains x then
          num := num.insert x leaves.size
          leaves := leaves.push x
  let L := leaves.size
  let perm (g : HashMap VarType VarType) : Array Nat :=
    leaves.map (fun x => match g[x]? with | some y => (num[y]?).getD 0 | none => (num[x]?).getD 0)
  let gp := gens.map perm
  let toLM (p : Array Nat) : HashMap VarType VarType := Id.run do
    let mut m : HashMap VarType VarType := {}
    for i in [0:L] do
      if p[i]! != i then m := m.insert leaves[i]! leaves[p[i]!]!
    return m
  let idp := Array.range L
  let mut elems : Array (Array Nat) := #[idp]
  let mut seen : HashMap (Array Nat) Unit := ({} : HashMap (Array Nat) Unit).insert idp ()
  let mut i := 0
  while i < elems.size do
    let e := elems[i]!
    for g in gp do
      let h := e.map (fun x => g[x]!)          -- h = g ∘ e
      if !seen.contains h then
        if elems.size >= cap then return (elems.map toLM, true)
        seen := seen.insert h ()
        elems := elems.push h
    i := i + 1
  return (elems.map toLM, false)

/-- When the whole group is too large to list: the largest closed subgroup found by adding
    generators one at a time and keeping each one only if the closure still fits under `cap`. -/
def closeIncremental (gens : Array (HashMap VarType VarType)) (cap : Nat) : Array (HashMap VarType VarType) := Id.run do
  let mut acc : Array (HashMap VarType VarType) := #[]
  let mut best : Array (HashMap VarType VarType) := #[{}]
  for g in gens do
    let (els, capped) := closeGroup (acc.push g) cap
    if !capped then
      acc := acc.push g
      best := els
  return best

/-- `w ↦ w'` exactly when relabelling `w`'s expression gives the node of wire `w'`. -/
def nameMap (g : GlobalDAG) (lm : HashMap VarType VarType) : HashMap String String := Id.run do
  let fw := g.wires
  let ws := g.circuit.wireOrder
  let mut rev : HashMap NodeId String := {}
  for w in ws do
    match fw[w]? with
    | some n => if !(rev.contains n) then rev := rev.insert n w
    | none   => pure ()
  let mut gg := g
  let mut memo : HashMap NodeId NodeId := {}
  let mut m : HashMap String String := {}
  for w in ws do
    match fw[w]? with
    | some n =>
      let (g2, memo2, n') := permuteNode gg lm memo n
      gg := g2; memo := memo2
      match rev[n']? with
      | some w' => m := m.insert w w'
      | none    => pure ()
    | none => pure ()
  return m

structure SymGroup where
  tier   : String := "-"
  order  : Nat := 1
  capped : Bool := false          -- always false now: `group` is a closed (sub)group
  sub    : Bool := false          -- true when `group` is only a subgroup of the full symmetry group
  group  : Array (HashMap VarType VarType) := #[{}]
  dag    : GlobalDAG := {}
  deriving Inhabited

/-- The group generated by `gens`, listed in full when it has at most `cap`
    elements.  Otherwise (`true` in the second component): the largest closed
    subgroup found by `closeIncremental` when `fallback`, else just the partial
    listing (enough to tell that the group is large). -/
def closedGroup (gens : Array (HashMap VarType VarType)) (cap : Nat) (fallback : Bool := true)
    : Array (HashMap VarType VarType) × Bool :=
  let (els, capped) := closeGroup gens cap
  if capped then (if fallback then closeIncremental gens cap else els, true) else (els, false)

/-- Both candidate groups: leaf relabellings, and (when (S1)/(S2) hold) shares as atoms.
    `fallback := false` skips the subgroup search for groups larger than `cap`
    (their `sub` flag is set and their listing is partial). -/
def symmetriesOf (gd : GlobalDAG) (cap : Nat) (fallback : Bool := true) : Array SymGroup := Id.run do
  let c0 := gd.circuit
  let (rc, _) := contractAssoc c0
  let (gl, rl) := automorphisms rc
  let (leafG, leafSub) := closedGroup (rl.gens.map (leafMapOf gl)) cap fallback
  let mut out : Array SymGroup := #[{ tier := "leaf", order := leafG.size, sub := leafSub, group := leafG, dag := gd }]
  let chk := shareChecks c0
  if chk.ok then
    let c := rc
    let chk2 := shareChecks c
    let bundles := if chk2.ok then chk2.bundles else chk.bundles
    let g := buildShareGraph c bundles
    let (_, _, gens) := groupOf g 200000 g.kind
    let (shG, shSub) := closedGroup (gens.map (atomicLeafMap g)) cap fallback
    out := out.push { tier := "share", order := shG.size, sub := shSub, group := shG, dag := buildAtomicDAG c0 }
  return out


structure WireTables where
  ws     : Array String := #[]
  n      : Nat := 0
  fwd    : Array (Array Nat) := #[]      -- fwd[g][i] < n, or n when g is not valid on wire i; fwd[0] = identity
  closed : Bool := true
  deriving Inhabited

def WireTables.of (s : SymGroup) (ws : Array String) : WireTables :=
  let n := ws.size
  let pos : HashMap String Nat := (ws.zipIdx).foldl (fun acc (w, i) => acc.insert w i) {}
  -- wires that share an expression with another wire: a relabelling is not a permutation there
  let cnt : HashMap NodeId Nat := ws.foldl (fun m w =>
    match s.dag.wires[w]? with | some nd => m.insert nd ((m[nd]?).getD 0 + 1) | none => m) {}
  let dup (w : String) : Bool :=
    match s.dag.wires[w]? with | some nd => (cnt[nd]?).getD 0 > 1 | none => true
  let idx (m : HashMap String String) : Array Nat :=
    ws.map (fun w => if dup w then n else
      match m[w]? with | some v => if dup v then n else (pos[v]?).getD n | none => n)
  let maps := s.group.map (fun e =>
    let e := normLM e
    if e.isEmpty then Array.range n else idx (nameMap s.dag e))
  { ws, n, fwd := maps, closed := !s.capped }


def maskOf (n : Nat) (xs : Array Nat) : Array Bool :=
  xs.foldl (fun m i => m.set! i true) (Array.replicate n false)

/-- Wires of `F` on which every element of `K` is valid and stays inside `F`. -/
def stableIn (E : WireTables) (K : Array Nat) (F : Array Nat) : Array Nat :=
  let inF := maskOf E.n F
  F.filter (fun w => K.all (fun g => let v := E.fwd[g]![w]!; v < E.n && inF[v]!))

def orbitsOn (E : WireTables) (K : Array Nat) (N : Array Nat) : Array (Array Nat) := Id.run do
  let inN := maskOf E.n N
  let mut seen := Array.replicate E.n false
  let mut out : Array (Array Nat) := #[]
  for w in N do
    if seen[w]! then continue
    let mut orb := #[w]
    seen := seen.set! w true
    let mut i := 0
    while i < orb.size do
      let x := orb[i]!
      for g in K do
        let v := E.fwd[g]![x]!
        if v < E.n && inN[v]! && !seen[v]! then
          seen := seen.set! v true
          orb := orb.push v
      i := i + 1
    out := out.push (orb.qsort (· < ·))
  return out

/-- The ring of `w` under one element, if that element stays valid (and inside `F`) all the way round. -/
def ringOf (E : WireTables) (g : Nat) (w : Nat) (inF : Array Bool) : Option (Array Nat) := Id.run do
  let mut X := #[w]
  let mut cur := w
  let mut fuel := E.n
  while fuel > 0 do
    fuel := fuel - 1
    let v := E.fwd[g]![cur]!
    if v >= E.n || !inF[v]! then return none
    if v == w then return some X
    X := X.push v
    cur := v
  return none

/-- For a set `X` of wires, the elements of `K` that are valid on `X` and map `X` to itself.
    This is always a subgroup, and it acts on `X`. -/
def setStab (E : WireTables) (K : Array Nat) (X : Array Nat) : Array Nat :=
  let inX := maskOf E.n X
  K.filter (fun g => X.all (fun x => let v := E.fwd[g]![x]!; v < E.n && inX[v]!))

/-- Closure of `X` under a list of elements; `none` if one of them is not valid somewhere. -/
def closeUnder (E : WireTables) (T : Array Nat) (X : Array Nat) (inF : Array Bool) : Option (Array Nat) := Id.run do
  let mut inX := maskOf E.n X
  let mut Y := X
  let mut i := 0
  while i < Y.size do
    let x := Y[i]!
    for g in T do
      let v := E.fwd[g]![x]!
      if v >= E.n || !inF[v]! then return none
      if !inX[v]! then
        inX := inX.set! v true
        Y := Y.push v
    i := i + 1
  return some Y

/-- (wires that stop needing a cell of their own, wires newly covered) for subgroup `K2`. -/
def savedBy (E : WireTables) (K2 : Array Nat) (D2 D : Array Nat) : Nat × Nat :=
  let inD := maskOf E.n D
  let N2 := D2.filter (fun w => !inD[w]!)
  (N2.size - (orbitsOn E K2 N2).size, N2.size)

/-- A subgroup of `K` that acts on some loose wires, chosen to remove as many cells as possible.
    Start from the ring of a loose wire under one element, then absorb further elements while
    the wire set stays closed and the saving grows. -/
def bestSubgroup (E : WireTables) (K : Array Nat) (F D L : Array Nat) : Option (Array Nat × Array Nat) := Id.run do
  let inF := maskOf E.n F
  let mut best : Option (Array Nat × Array Nat) := none
  let mut bestSc : Nat × Nat := (0, 0)
  let mut seen : HashMap String Unit := {}
  for w in L do
    for g in K do
      match ringOf E g w inF with
      | none => pure ()
      | some X0 =>
        if X0.size < 2 then continue
        let key := toString (X0.qsort (· < ·)).toList
        if seen.contains key then continue
        seen := seen.insert key ()
        let mut X := X0
        let mut K2 := setStab E K X
        let mut D2 := stableIn E K2 F
        let mut sc := savedBy E K2 D2 D
        let mut improved := true
        while improved do
          improved := false
          let inK2 := maskOf E.fwd.size K2
          for h in K do
            if inK2[h]! then continue
            match closeUnder E (K2.push h) X inF with
            | none => pure ()
            | some X' =>
              let K3 := setStab E K X'
              let D3 := stableIn E K3 F
              let sc3 := savedBy E K3 D3 D
              if sc3.1 > sc.1 || (sc3.1 == sc.1 && sc3.2 > sc.2) then
                X := X'; K2 := K3; D2 := D3; sc := sc3
                improved := true
                break
        if sc.1 > bestSc.1 || (sc.1 == bestSc.1 && sc.2 > bestSc.2) then
          bestSc := sc
          best := some (K2, D2)
  return best


mutual
/-- probes = pre ∪ Q with Q ⊆ F, |Q| = c; `K` fixes every wire of `pre`.

    Orbital branching is applied only where it pays: if cutting the cell by
    orbits keeps more than three quarters of its probe sets, the cell is kept
    whole (fewer, larger cells serve the stored safe sets better, and the
    lookups through the group still remove symmetric repeats later). -/
partial def obranch (E : WireTables) (K : Array Nat) (pre : Cell) (F : Array Nat) (c : Nat) : Array Cell :=
  if c == 0 then #[pre]
  else if F.size < c then #[]
  else if K.size ≤ 1 then #[pre.push (c, F)]
  else
    let D := stableIn E K F
    let inD := maskOf E.n D
    let L := F.filter (fun w => !inD[w]!)
    let cut := (if D.isEmpty then #[] else pinClass E K pre D #[] c) ++
      (if L.isEmpty then #[] else looseClass E K pre L D F c)
    let whole := pre.push (c, F)
    if 4 * cut.foldl (fun a x => a + probeCount x) 0 > 3 * probeCount whole then #[whole] else cut

/-- probes = pre ∪ Q, Q ⊆ N ∪ B, |Q| = c, Q ∩ N ≠ ∅; `K` acts on `N` and on `B`. -/
partial def pinClass (E : WireTables) (K : Array Nat) (pre : Cell) (N B : Array Nat) (c : Nat) : Array Cell := Id.run do
  if c == 0 then return #[]
  let orbs := orbitsOn E K N
  let big := (orbs.filter (·.size > 1)).qsort (fun a b => a.size > b.size || (a.size == b.size && a[0]! < b[0]!))
  let fix := (orbs.filter (·.size == 1)).map (·[0]!)
  let mut out : Array Cell := #[]
  for i in [0:big.size] do
    let O := big[i]!
    let x := O[0]!
    let later := (big.extract (i+1) big.size).foldl (· ++ ·) #[]
    let F' := (O.extract 1 O.size) ++ later ++ fix ++ B
    let K' := K.filter (fun g => E.fwd[g]![x]! == x)
    out := out ++ obranch E K' (pre.push (1, #[x])) F' (c - 1)
  -- probes whose N-part lies entirely among the wires K leaves fixed
  if !fix.isEmpty then
    for j in [1:c+1] do
      if j ≤ fix.size then
        if c - j == 0 then out := out.push (pre.push (j, fix))
        else if !B.isEmpty then out := out ++ obranch E K (pre.push (j, fix)) B (c - j)
  return out

/-- probes = pre ∪ Q, Q ⊆ F, |Q| = c, Q touches L = F ∖ D. -/
partial def looseClass (E : WireTables) (K : Array Nat) (pre : Cell) (L D F : Array Nat) (c : Nat) : Array Cell := Id.run do
  let inD := maskOf E.n D
  match bestSubgroup E K F D L with
  | some (K2, D2) =>
    let inD2 := maskOf E.n D2
    let N2 := D2.filter (fun w => !inD[w]!)
    let L2 := F.filter (fun w => !inD2[w]!)
    return (pinClass E K2 pre N2 D c) ++ (if L2.isEmpty then #[] else looseClass E K2 pre L2 D2 F c)
  | none =>
    -- no subgroup moves the remaining loose wires among themselves.  A loose wire that some
    -- elements leave fixed gets its own pin with that stabiliser; the rest form one plain block.
    let mut out : Array Cell := #[]
    let mut removed : Array Nat := #[]
    let mut plain : Array Nat := #[]
    for w in L do
      let Kw := K.filter (fun g => E.fwd[g]![w]! == w)
      let moves := Kw.any (fun g => F.any (fun x => let v := E.fwd[g]![x]!; v < E.n && v != x))
      if Kw.size > 1 && moves then
        removed := removed.push w
        let inR := maskOf E.n removed
        out := out ++ obranch E Kw (pre.push (1, #[w])) (F.filter (fun x => !inR[x]!)) (c - 1)
      else plain := plain.push w
    for j in [1:c+1] do
      if j ≤ plain.size && c - j ≤ D.size then
        out := out.push ((pre.push (j, plain)).push (c - j, D))
    return out
end

/-- The orbital root of one candidate group. -/
def orbitalRoot (E : WireTables) (d : Nat) : Array Cell :=
  (obranch E (Array.range E.fwd.size) #[] (Array.range E.n) d).map (fun p => p.filter (fun (c, _) => c > 0))
    |>.filter (fun c => !(c.any (fun (k, ws) => k > 0 && ws.size < k)))

def rootProbeCount (r : Array Cell) : Nat := r.foldl (fun a c => a + probeCount c) 0

/-- Index of the candidate group whose orbital root holds the fewest probe sets, with that root. -/
def bestRootGroup (els : Array WireTables) (d : Nat) : Nat × Array Cell := Id.run do
  let mut bi := 0
  let mut best := orbitalRoot els[0]! d
  for i in [1:els.size] do
    let r := orbitalRoot els[i]! d
    if rootProbeCount r < rootProbeCount best then
      bi := i
      best := r
  return (bi, best)

/-- Is the probe set `P` (wire indices) a member of some root cell? -/
def inRoots (roots : Array Cell) (n : Nat) (P : Array Nat) : Bool :=
  let inP := maskOf n P
  roots.any (fun cell =>
    let tot := cell.foldl (fun a (c, _) => a + c) 0
    tot == P.size && cell.all (fun (c, ws) => (ws.foldl (fun a w => if inP[w]! then a + 1 else a) 0) == c))

/-- Brute force: every probe set of size `d` is mapped into a root cell by some
    table valid on it.  `(probe sets checked, misses)`, or `none` when there are
    more than `budget` probe sets (times tables). -/
partial def rootCheck (n d : Nat) (maps : Array (Array Nat)) (roots : Array Cell)
    (budget : Nat := 400000000) : Option (Nat × Nat) :=
  if binomial n d * maps.size * (roots.size + 1) > budget then none else
  let rec go (start : Nat) (acc : Array Nat) (res : Nat × Nat) : Nat × Nat :=
    if acc.size == d then
      let ok := maps.any (fun f =>
        let img := acc.map (f[·]!)
        !(img.any (· >= n)) && inRoots roots n img)
      (res.1 + 1, if ok then res.2 else res.2 + 1)
    else (List.range (n - start)).foldl (fun r i => go (start + i + 1) (acc.push (start + i)) r) res
  some (go 0 #[] (0, 0))

-- ============================================================
-- Symmetry plan and the symmetric cell search
-- ============================================================

/-- What the cell search needs from the symmetry. -/
structure SymmetryPlan where
  /-- The automorphisms other than the identity, as (forward, inverse) wire tables. -/
  sym       : Array (Array Nat × Array Nat)
  roots     : Array Cell
  /-- Probe sets in the root, and in total. -/
  rootSize  : Nat
  totalSize : Nat
  label     : String
  /-- All tables of the group whose orbits the root uses (for `rootCheck`). -/
  rootTables : Array (Array Nat)
  deriving Inhabited

/-- The inverse of a wire table (`n` where no wire maps to `v`).  Tables are
    injective on the wires where they are valid (duplicate wires are excluded
    in `WireTables.of`), so the inverse is well defined. -/
def invertTable (n : Nat) (f : Array Nat) : Array Nat := Id.run do
  let mut inv := Array.replicate n n
  for w in [0:n] do
    let v := f[w]!
    if v < n then inv := inv.set! v w
  return inv

/-- Default bound on the order of each group the search uses.  Any subgroup of
    the automorphism group is sound; a larger one prunes more but costs more to
    list, tabulate, branch on and look up through.  Measured on the suite
    (`bench cap`): DOM-AND 4 and 5 shares (groups of order 576 and more) are 6×
    and 2.4× faster at 64 than at 600, and DOM Keccak χ 4 shares (orders 10 and
    30) is unaffected; at 24 Keccak χ 4 loses 40 %. -/
def defaultGroupCap : Nat := 64

/-- The symmetry plan of `g` at order `d`: the automorphisms of every candidate
    group (each listed group capped at `groupCap` elements; a larger group is
    replaced by its largest closed subgroup that fits — any subgroup is sound),
    and the orbital root of the candidate group that shrinks the root most. -/
def planSymmetry (g : GlobalDAG) (d : Nat) (groupCap : Nat := defaultGroupCap) : SymmetryPlan := Id.run do
  let ws := g.circuit.wireOrder
  let n := ws.size
  let cands := symmetriesOf g groupCap
  let els := cands.map (fun s => WireTables.of s ws)
  let (ri, roots) := bestRootGroup els d
  -- every non-identity table, once
  let idT := Array.range n
  let mut seen : HashMap (Array Nat) Unit := ({} : HashMap (Array Nat) Unit).insert idT ()
  let mut sym : Array (Array Nat × Array Nat) := #[]
  for E in els do
    for f in E.fwd do
      if !seen.contains f && f.any (· < n) then
        seen := seen.insert f ()
        sym := sym.push (f, invertTable n f)
  let label := String.intercalate " + " (cands.toList.map (fun s => s!"{s.tier} {s.order}{if s.sub then "*" else ""}"))
  return { sym, roots, rootSize := rootProbeCount roots, totalSize := binomial n d, label,
           rootTables := (els[ri]!).fwd }

/-- Verify `d`-probing security with the symmetric cell search: the orbital
    root, and lookups through the automorphisms before every engine call.
    `useSymmetry := false` runs the same search without symmetry (ablation). -/
def checkDProbingSym (g : GlobalDAG) (d : Nat) (useSymmetry : Bool := true)
    (allowFactor : Bool := true) (orbitalRoot : Bool := true) (groupCap : Nat := defaultGroupCap)
    : GlobalDAG × CellState × CheckResult × Option SymmetryPlan :=
  if !useSymmetry then
    let (g, s, r) := checkDProbingCells g d allowFactor
    (g, s, r, none)
  else
    let p := planSymmetry g d groupCap
    let n := g.circuit.wireOrder.size
    let env := { CellEnv.of g (identityLook n) allowFactor with sym := p.sym }
    let (s, r) := runCells env g (if orbitalRoot then p.roots else #[#[(d, Array.range n)]])
    (s.g, s, r, some p)

end verif
