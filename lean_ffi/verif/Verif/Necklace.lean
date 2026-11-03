import Verif.Symmetry

namespace verif

open Std (HashMap)

/-!
# The necklace search: one permutation, no safe sets

The simplest symmetric verifier we can state.  It keeps the rewrite engine and the
group of `Symmetry.lean` and nothing else: no cells, no extension, no stored safe sets.

1. **Pick one permutation** `π` from the group (`choosePi`): the one that leaves the
   fewest probe sets to certify (`necklaceCount`).
2. **List the necklaces** (`runNecklaces`).  A *shift* of a probe set `P` is `π^k(P)`,
   for a power that is valid on every wire of `P`.  `P` is kept when no shift of it
   reads earlier (`isLeast`); a necklace is the family of probe sets joined by shifts.
3. **Run the engine** on every kept probe set, and stop at the first failure.

Soundness is a descent: a probe set that is not kept has a shift that reads strictly
earlier, and that shift has the same verdict (`Symmetry.lean`, transport).  Repeating,
it reaches a kept probe set.  Nothing here needs the shifts to form a group.

See `docs/simple-versions/01-necklaces.md`.
-/

/-- A chosen permutation, read on the wires. -/
structure NecklacePi where
  /-- Index of `π` in the wire tables. -/
  elem   : Nat := 0
  /-- Table indices of `π, π², …, π^(period-1)`: the identity is left out. -/
  powers : Array Nat := #[]
  period : Nat := 1
  /-- The rings: the wires on which every power is valid, in cycles of `π`. -/
  rings  : Array (Array Nat) := #[]
  /-- The wires on which some power is not valid. -/
  loose  : Array Nat := #[]
  /-- How many probe sets must be certified with this `π` (`necklaceCount`). -/
  score  : Nat := 0
  deriving Inhabited

/-- For every element of the listed group, the indices of its powers `e, e², …` up to
    (not including) the identity.  The group is closed, so all of them are listed. -/
def powerIndices (s : SymGroup) : Array (Array Nat) := Id.run do
  let idx : HashMap String Nat := (s.group.zipIdx).foldl (fun m (e, i) => m.insert (keyLM (normLM e)) i) {}
  let mut out : Array (Array Nat) := #[]
  for e in s.group do
    let mut ps : Array Nat := #[]
    let mut p := normLM e
    while !p.isEmpty do
      match idx[keyLM p]? with
      | some i => ps := ps.push i
      | none   => break
      p := normLM (composeLM p e)
    out := out.push ps
  return out

/-- The cycles of table `f` on the wires `D`, which `f` maps onto themselves. -/
def cyclesOn (n : Nat) (f : Array Nat) (D : Array Nat) : Array (Array Nat) := Id.run do
  let mut seen := Array.replicate n false
  let mut out : Array (Array Nat) := #[]
  for w in D do
    if seen[w]! then continue
    let mut ring := #[w]
    seen := seen.set! w true
    let mut v := f[w]!
    while v != w do
      ring := ring.push v
      seen := seen.set! v true
      v := f[v]!
    out := out.push ring
  return out

/-- The cycles of table `f`: wires that return to themselves through valid steps only. -/
def closedCycles (n : Nat) (f : Array Nat) : Array (Array Nat) := Id.run do
  let mut seen := Array.replicate n false
  let mut out : Array (Array Nat) := #[]
  for w in [0:n] do
    if seen[w]! then continue
    let mut ring := #[w]
    let mut v := f[w]!
    while v < n && v != w do
      ring := ring.push v
      v := f[v]!
    if v == w then
      out := out.push ring
      for x in ring do seen := seen.set! x true
  return out

def popCount (x : Nat) : Nat := Id.run do
  let mut x := x
  let mut c := 0
  while x > 0 do
    c := c + x % 2
    x := x / 2
  return c

/-- The exact number of necklaces of `d` wires, for `tables[k] = π^k` (`tables[0]` the
    identity), without listing them.  A necklace of `c` members is `c` probe sets that
    count `1/c` each, and `c = |V(P)| / |unmoved(P)|` for a member `P`, where `V(P)` holds
    the powers valid on `P` and `unmoved(P)` those of them with `π^k(P) = P`.  So

      necklaces = ∑ₖ ∑_{P unmoved by π^k} 1 / |V(P)|.

    `P` is unmoved by `π^k` exactly when it is a union of closed cycles of `π^k`, so for
    each `k` this is a knapsack over those cycles, remembering the size so far and the
    powers still valid (a bit mask, bit `k` for `π^k`).  With every power valid on every
    wire, `|V(P)|` is the period and this is the orbit-counting lemma. -/
def necklaceCount (tables : Array (Array Nat)) (n d : Nat) : Nat := Id.run do
  let m := tables.size
  let full := 2 ^ m - 1
  let masks := (Array.range n).map (fun w =>
    (List.range m).foldl (fun a k => if tables[k]![w]! < n then a + 2 ^ k else a) 0)
  let unit := (List.range m).foldl (fun a k => Nat.lcm a (k + 1)) 1
  let mut total := 0
  for f in tables do
    let mut states : HashMap (Nat × Nat) Nat := ({} : HashMap (Nat × Nat) Nat).insert (full, 0) 1
    for ring in closedCycles n f do
      if ring.size > d then continue
      let rm := ring.foldl (fun a w => a &&& masks[w]!) full
      for ((u, c), ways) in states.toArray do
        if c + ring.size ≤ d then
          let key := (u &&& rm, c + ring.size)
          states := states.insert key ((states[key]?).getD 0 + ways)
    for ((u, c), ways) in states.toArray do
      if c == d then total := total + ways * (unit / popCount u)
  return total / unit

/-- The element `i` of the group, read on the wires. -/
def NecklacePi.of (E : WireTables) (pows : Array Nat) (i d : Nat) : NecklacePi :=
  let all := Array.range E.n
  let D := stableIn E (pows.push i) all
  let inD := maskOf E.n D
  let rings := cyclesOn E.n E.fwd[i]! D
  let period := pows.size + 1
  { elem := i, powers := pows, period, rings, loose := all.filter (fun w => !inD[w]!),
    score := necklaceCount (#[Array.range E.n] ++ pows.map (E.fwd[·]!)) E.n d }

/-- The best permutation: fewest necklaces, then the longest period.  Two elements with
    the same powers count the same, so each set of powers is scored once. -/
def choosePi (E : WireTables) (pows : Array (Array Nat)) (d : Nat) : NecklacePi := Id.run do
  let mut seen : Std.HashSet (Array Nat) := {}
  let mut best := NecklacePi.of E pows[0]! 0 d
  for (ps, i) in pows.zipIdx do
    let key := ps.qsort (· < ·)
    if seen.contains key then continue
    seen := seen.insert key
    let p := NecklacePi.of E ps i d
    if p.score < best.score || (p.score == best.score && p.period > best.period) then best := p
  return best

/-- Does `a` read strictly earlier than `b` (sorted, same size)? -/
@[inline] def readsEarlier (a b : Array Nat) : Bool := Id.run do
  for i in [0:a.size] do
    if a[i]! != b[i]! then return a[i]! < b[i]!
  return false

/-- No shift of `P` reads earlier.  A table is one shift; it applies only when it is
    valid on every wire of `P`. -/
def isLeast (tables : Array (Array Nat)) (n : Nat) (P : Array Nat) : Bool := Id.run do
  for f in tables do
    let img := P.map (f[·]!)
    if img.any (· ≥ n) then continue
    if readsEarlier (img.insertionSort (· < ·)) P then return false
  return true

/-- The next `d`-subset of `0..n-1` in reading order. -/
def nextSet (n : Nat) (c : Array Nat) : Option (Array Nat) := Id.run do
  let d := c.size
  for i' in [0:d] do
    let i := d - 1 - i'
    if c[i]! + (d - i) < n then
      let mut c := c.set! i (c[i]! + 1)
      for j in [i + 1:d] do
        c := c.set! j (c[j - 1]! + 1)
      return some c
  return none

/-- How many probe sets of size `d` are kept. -/
def countLeast (tables : Array (Array Nat)) (n d : Nat) : Nat := Id.run do
  if d == 0 || n < d then return 0
  let mut c := Array.range d
  let mut kept := 0
  repeat
    if isLeast tables n c then kept := kept + 1
    match nextSet n c with
    | some c' => c := c'
    | none    => break
  return kept

structure NecklaceRun where
  engine : Nat := 0
  result : CheckResult := .Secure

/-- Run the engine on every kept probe set, in reading order, and stop at the first
    failure.  With no tables this is plain enumeration of all probe sets. -/
def runNecklaces (g : GlobalDAG) (tables : Array (Array Nat)) (d : Nat)
    (allowFactor : Bool := true) : NecklaceRun := Id.run do
  let ws := g.circuit.wireOrder
  let n := ws.size
  if d == 0 || n < d then return {}
  let ids := ws.map (fun w => g.wires[w]!)
  let mut g := g
  let mut c := Array.range d
  let mut engine := 0
  repeat
    if isLeast tables n c then
      let (g', sec) := checkProbeRoots g (c.map (ids[·]!)) allowFactor
      g := g'
      engine := engine + 1
      if !sec then return { engine, result := .Insecure (c.map (ws[·]!)) }
    match nextSet n c with
    | some c' => c := c'
    | none    => break
  return { engine }

/-- Audit: the engine's verdict on every probe set against its verdict on every shift.
    `(pairs compared, pairs that disagree)`, or `none` beyond `budget` probe sets. -/
def necklaceAudit (g : GlobalDAG) (tables : Array (Array Nat)) (d : Nat) (allowFactor : Bool := true)
    (budget : Nat := 50000) : Option (Nat × Nat) := Id.run do
  let ws := g.circuit.wireOrder
  let n := ws.size
  if binomial n d > budget || d == 0 || n < d then return none
  let ids := ws.map (fun w => g.wires[w]!)
  let mut g := g
  let mut c := Array.range d
  let mut verdict : HashMap (Array Nat) Bool := {}
  let mut sets : Array (Array Nat) := #[]
  repeat
    let (g', sec) := checkProbeRoots g (c.map (ids[·]!)) allowFactor
    g := g'
    verdict := verdict.insert c sec
    sets := sets.push c
    match nextSet n c with
    | some c' => c := c'
    | none    => break
  let mut pairs := 0
  let mut bad := 0
  for P in sets do
    for f in tables do
      let img := P.map (f[·]!)
      if img.any (· ≥ n) then continue
      pairs := pairs + 1
      if verdict[img.insertionSort (· < ·)]! != verdict[P]! then bad := bad + 1
  return some (pairs, bad)

end verif
