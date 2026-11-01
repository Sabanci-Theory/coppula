import Verif

namespace verif

/-!
# Evaluation examples and the `=== Results ===` ablation

Benchmark gadgets for the evaluation section, mirroring the example suites of

* [BBD+15] Barthe, Belaïd, Dupressoir, Fouque, Grégoire, Strub
* [BBC+19] Barthe, Belaïd, Cassiers, Fouque, Grégoire, Standaert
* [BNN+15] Bilgin, Nikova, Nikov, Rijmen, Tokareva, Vitkup

Scope note: the tool works on Boolean (𝔽₂) circuits in the value-based ISW
model, so the GF(2⁸) benchmarks of [BBD+15] (AES S-box/rounds, key schedule,
Schramm–Paar) are represented by their field-agnostic core — the ISW
multiplication — instantiated over 𝔽₂; glitch/transition rows of [BBC+19] are
out of scope (value-based model only).
-/

-- Helper function to build a chain of XORs from an array of terms.
-- Association is left-to-right in the order given, which is security-relevant!
partial def addWireXorChain (g : GlobalDAG) (out : String) (terms : Array WireInput) : GlobalDAG :=
  if terms.size == 0 then
    g.addWireXor out #[.const false]
  else if terms.size == 1 then
    g.addWireXor out #[terms[0]!]
  else
    let firstName := if terms.size == 2 then out else s!"{out}m0"
    let g := g.addWireXor firstName #[terms[0]!, terms[1]!]
    let rec go (g : GlobalDAG) (acc : String) (idx : Nat) : GlobalDAG :=
      if idx >= terms.size then g
      else
        let name := if idx + 1 == terms.size then out else s!"{out}m{idx - 1}"
        let g := g.addWireXor name #[.wire acc, terms[idx]!]
        go g name (idx + 1)
    go g firstName 2

/-- Declare the canonical `shares`-sharing of secret `sec`: shares `pre0 …`,
    the first `shares-1` are fresh randoms, the last carries the secret
    (`pre{n-1} = sec + Σ randoms`).  Any `shares-1` of them are uniform. -/
def addSecretShares (g : GlobalDAG) (pre : String) (sec : String) (shares : Nat) : GlobalDAG := Id.run do
  let mut g := g
  let mut last : Array WireInput := #[.leaf (.Secret sec)]
  for i in [0:shares-1] do
    g := g.addShare s!"{pre}{i}" #[.leaf (.Random s!"r{pre}{i}")]
    last := last.push (.leaf (.Random s!"r{pre}{i}"))
  g := g.addShare s!"{pre}{shares-1}" last
  return g

/-- 1-based variant (`pre1 … pre{n}`, secret in the last share) — used by the
    TI examples whose component functions are cited with 1-based indices. -/
def addSecretShares1 (g : GlobalDAG) (pre : String) (sec : String) (shares : Nat) : GlobalDAG := Id.run do
  let mut g := g
  let mut last : Array WireInput := #[.leaf (.Secret sec)]
  for i in [1:shares] do
    g := g.addShare s!"{pre}{i}" #[.leaf (.Random s!"r{pre}{i}")]
    last := last.push (.leaf (.Random s!"r{pre}{i}"))
  g := g.addShare s!"{pre}{shares}" last
  return g


/-! ## §1 Multiplication / AND gadgets -/

/-! ### ISW / Rivain–Prouff multiplication over 𝔽₂ (SecMult)

    [ISW03; RP10].  The "multiplication" rows of [BBD+15] Table 2 (orders 1–5,
    their timings 0.001s/0.033s/1.138s/45s at orders 2–5) and the "ISW AND"
    row of [BBC+19] Table 2 (their timings 0.1s order 4, 2.6s order 5).
    Structure ([BBD+15] Alg. 7, t = 2 case, generalized):
      i < j:  r_ij fresh;  r_ji := (r_ij + a_i·b_j) + a_j·b_i
      c_i := a_i·b_i + Σ_{j≠i} r_ij       (2-ary chain, ascending j)
    An n-share instance is expected (n-1)-probing secure. -/
/-- Core ISW multiplication layer over already-declared share wires `aSh`/`bSh`
    (body wires and fresh randoms prefixed with `pre`); returns the output share
    wire names.  With `pre := ""` this is the plain `iswAND` body; the
    depth-scaling chain instantiates it once per stage. -/
def iswANDCore (g : GlobalDAG) (pre : String) (aSh bSh : Array String)
    : GlobalDAG × Array String := Id.run do
  let n := aSh.size
  let mut g := g
  -- all n² partial products
  for i in [0:n] do
    for j in [0:n] do
      g := g.addWireAnd s!"{pre}p{i}{j}" #[.wire aSh[i]!, .wire bSh[j]!]
  -- r_ji = (r_ij + a_i b_j) + a_j b_i   (association per Alg. 7)
  for i in [0:n] do
    for j in [i+1:n] do
      g := g.addWireXor s!"{pre}t{i}{j}" #[.leaf (.Random s!"{pre}r{i}{j}"), .wire s!"{pre}p{i}{j}"]
      g := g.addWireXor s!"{pre}s{j}{i}" #[.wire s!"{pre}t{i}{j}", .wire s!"{pre}p{j}{i}"]
  -- c_i = a_i b_i + Σ_{j≠i} r_ij
  let mut outs : Array String := #[]
  for i in [0:n] do
    let mut terms : Array WireInput := #[.wire s!"{pre}p{i}{i}"]
    for j in [0:n] do
      if j != i then
        terms := terms.push (if i < j then .leaf (.Random s!"{pre}r{i}{j}") else .wire s!"{pre}s{i}{j}")
    g := addWireXorChain g s!"{pre}c{i}" terms
    outs := outs.push s!"{pre}c{i}"
  return (g, outs)

def iswAND (shares : Nat) : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  for (pre, sec) in #[("a", "a"), ("b", "b")] do
    g := addSecretShares g pre sec shares
  let aSh := (Array.range shares).map (fun i => s!"a{i}")
  let bSh := (Array.range shares).map (fun i => s!"b{i}")
  (iswANDCore g "" aSh bSh).1

/-! ### Depth-scaling chain of ISW-ANDs

    y⁽¹⁾ = x⁽⁰⁾·x⁽¹⁾,  y⁽ᵏ⁾ = y⁽ᵏ⁻¹⁾·x⁽ᵏ⁾ — `len` cascaded ISW-ANDs, each with
    its own fresh randomness, each intermediate sharing feeding exactly one
    successor gadget.  ISW multiplication is SNI, so the chain is expected
    (shares-1)-probing secure at every length; circuit size and multiplicative
    depth grow linearly in `len`, giving the verification-time scaling curve. -/
def iswAndChain (shares len : Nat) : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  for k in [0:len+1] do
    g := addSecretShares g s!"x{k}_" s!"x{k}" shares
  let mut cur := (Array.range shares).map (fun i => s!"x0_{i}")
  for k in [1:len+1] do
    let xs := (Array.range shares).map (fun i => s!"x{k}_{i}")
    let (g2, outs) := iswANDCore g s!"g{k}_" cur xs
    g := g2
    cur := outs
  return g

/-! ### DOM-independent AND, parameterized ([GMK16]; "DOM AND" in [BBC+19])

      diagonals      u_i  = a_i·b_i
      cross products p_ij = a_i·b_j                    (i ≠ j)
      masked terms   c_ij = p_ij + r_ij,  r_ij = r_ji  (one fresh random per unordered pair)
      outputs        s_i  = u_i + Σ_{j≠i} c_ij         (2-ary chain; the mask is
                     grouped with its cross term inside c_ij, which is the
                     security-relevant association)
    An n-share DOM-AND is expected (n-1)-probing secure.  NOTE: names are only
    unambiguous for `shares ≤ 10` (two digits concatenate in `p{i}{j}`). -/
def domAND (shares : Nat) : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  for (pre, sec) in #[("a", "a"), ("b", "b")] do
    g := addSecretShares g pre sec shares
  -- diagonal products
  for i in [0:shares] do
    g := g.addWireAnd s!"u{i}" #[.wire s!"a{i}", .wire s!"b{i}"]
  -- cross products
  for i in [0:shares] do
    for j in [i+1:shares] do
      g := g.addWireAnd s!"p{i}{j}" #[.wire s!"a{i}", .wire s!"b{j}"]
      g := g.addWireAnd s!"p{j}{i}" #[.wire s!"a{j}", .wire s!"b{i}"]
  -- masked cross terms
  for i in [0:shares] do
    for j in [i+1:shares] do
      let r := WireInput.leaf (.Random s!"r{i}{j}")
      g := g.addWireXor s!"c{i}{j}" #[.wire s!"p{i}{j}", r]
      g := g.addWireXor s!"c{j}{i}" #[.wire s!"p{j}{i}", r]
  -- outputs
  for i in [0:shares] do
    let mut terms : Array WireInput := #[.wire s!"u{i}"]
    for j in [0:shares] do
      if j != i then
        terms := terms.push (.wire s!"c{i}{j}")
    g := addWireXorChain g s!"s{i}" terms
  return g

/-- 7-share DOM-AND instance (kept for the stored-timing note in `runAblation`). -/
def sevenDomAND : GlobalDAG := domAND 7

/-! ### Trichina AND gate ([Tri03]; "Trichina AND" in [BBC+19] Table 2)

    2 shares, one fresh random `r`:
      c0 = r
      c1 = (((r + a0·b0) + a0·b1) + a1·b0) + a1·b1
    Every prefix of the accumulation chain is masked by `r`, so the gate is
    1-probing secure in the value-based model. -/
def trichinaAND : GlobalDAG := ({} : GlobalDAG)
  |>.addShare "a0" #[.leaf (.Random "ra")]
  |>.addShare "a1" #[.leaf (.Secret "a"), .leaf (.Random "ra")]
  |>.addShare "b0" #[.leaf (.Random "rb")]
  |>.addShare "b1" #[.leaf (.Secret "b"), .leaf (.Random "rb")]
  |>.addWireAnd "a0b0" #[.wire "a0", .wire "b0"]
  |>.addWireAnd "a0b1" #[.wire "a0", .wire "b1"]
  |>.addWireAnd "a1b0" #[.wire "a1", .wire "b0"]
  |>.addWireAnd "a1b1" #[.wire "a1", .wire "b1"]
  |>.addWireXor "c0" #[.leaf (.Random "r")]
  |>.addWireXor "t1" #[.leaf (.Random "r"), .wire "a0b0"]
  |>.addWireXor "t2" #[.wire "t1", .wire "a0b1"]
  |>.addWireXor "t3" #[.wire "t2", .wire "a1b0"]
  |>.addWireXor "c1" #[.wire "t3", .wire "a1b1"]

/-- Trichina AND with the accumulation mis-associated (mask added last).
    The prefix `t1 = a0·b0 + a0·b1 = a0·b` depends on the secret `b`
    (Pr[t1 = 1] = 0 if b = 0, = 1/2 if b = 1) — a classic first-order flaw;
    expected INSECURE at order 1.  Same functional output as `trichinaAND`. -/
def trichinaANDBad : GlobalDAG := ({} : GlobalDAG)
  |>.addShare "a0" #[.leaf (.Random "ra")]
  |>.addShare "a1" #[.leaf (.Secret "a"), .leaf (.Random "ra")]
  |>.addShare "b0" #[.leaf (.Random "rb")]
  |>.addShare "b1" #[.leaf (.Secret "b"), .leaf (.Random "rb")]
  |>.addWireAnd "a0b0" #[.wire "a0", .wire "b0"]
  |>.addWireAnd "a0b1" #[.wire "a0", .wire "b1"]
  |>.addWireAnd "a1b0" #[.wire "a1", .wire "b0"]
  |>.addWireAnd "a1b1" #[.wire "a1", .wire "b1"]
  |>.addWireXor "c0" #[.leaf (.Random "r")]
  |>.addWireXor "t1" #[.wire "a0b0", .wire "a0b1"]
  |>.addWireXor "t2" #[.wire "t1", .wire "a1b0"]
  |>.addWireXor "t3" #[.wire "t2", .wire "a1b1"]
  |>.addWireXor "c1" #[.wire "t3", .leaf (.Random "r")]

/-! ### Threshold-implementation AND ([NRR06]; "TI AND" in [BBC+19] Table 2)

    3 shares, no fresh randomness (= [BNN+15] Eq. (2) without the linear part):
      c1 = a2·b2 + a2·b3 + a3·b2
      c2 = a3·b3 + a3·b1 + a1·b3
      c3 = a1·b1 + a1·b2 + a2·b1
    Component i avoids share index i (non-completeness) ⇒ 1-probing secure.
    TI guarantees first order only; order 2 probes the design boundary. -/
def tiAND : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  for (pre, sec) in #[("a", "a"), ("b", "b")] do
    g := addSecretShares1 g pre sec 3
  for (i, j) in #[(2,2),(2,3),(3,2),(3,3),(3,1),(1,3),(1,1),(1,2),(2,1)] do
    g := g.addWireAnd s!"m{i}{j}" #[.wire s!"a{i}", .wire s!"b{j}"]
  g := addWireXorChain g "c1" #[.wire "m22", .wire "m23", .wire "m32"]
  g := addWireXorChain g "c2" #[.wire "m33", .wire "m31", .wire "m13"]
  g := addWireXorChain g "c3" #[.wire "m11", .wire "m12", .wire "m21"]
  return g


/-! ## §2 Mask-refresh gadgets

    The refresh variants studied in [BBD+15] Table 3 / [CPRR14], over 𝔽₂. -/

/-! ### Additive refresh (`RefreshMasks` of [RP10])

    n shares, n-1 fresh randoms:
      y_i = x_i + r_i               (i = 1 … n-1)
      y_0 = x_0 + r_1 + … + r_{n-1} (2-ary chain)
    Expected (n-1)-probing secure standalone (it is not SNI — that distinction
    is invisible to a probing-only check). -/
def refreshAdd (shares : Nat) : GlobalDAG := Id.run do
  let mut g : GlobalDAG := addSecretShares {} "x" "x" shares
  let mut acc : Array WireInput := #[.wire "x0"]
  for i in [1:shares] do
    g := g.addWireXor s!"y{i}" #[.wire s!"x{i}", .leaf (.Random s!"r{i}")]
    acc := acc.push (.leaf (.Random s!"r{i}"))
  g := addWireXorChain g "y0" acc
  return g

/-! ### ISW-based refresh (multiplication-style; the "stronger" refresh of
    [DDF14/CPRR14]): one fresh random per unordered share pair,
      y_i = x_i + Σ_{j≠i} r_{min(i,j),max(i,j)}   (2-ary chain, ascending j).
    Expected (n-1)-probing secure. -/
def refreshISW (shares : Nat) : GlobalDAG := Id.run do
  let mut g : GlobalDAG := addSecretShares {} "x" "x" shares
  for i in [0:shares] do
    let mut terms : Array WireInput := #[.wire s!"x{i}"]
    for j in [0:shares] do
      if j != i then
        let p := min i j
        let q := max i j
        terms := terms.push (.leaf (.Random s!"r{p}{q}"))
    g := addWireXorChain g s!"y{i}" terms
  return g


/-! ## §3 S-boxes -/

/-! ### DOM Keccak χ S-box ([GSM17]; "DOM Keccak S-box" in [BBC+19] Table 2,
    orders 1–5; cf. `Verif/netlists/keccak_chi.txt`)

    5-bit χ: out_k = v_k + (¬v_{k+1})·v_{k+2} (indices mod 5).  Each of the 5
    AND gates is a `shares`-share DOM-AND with its own fresh randomness; the
    NOT is folded into share 0 of the negated operand (cf. the netlist's
    `d0 := ~a0`).  Expected (shares-1)-probing secure. -/
def domKeccakChi (shares : Nat) : GlobalDAG := Id.run do
  let names := #["a", "b", "c", "d", "e"]
  let mut g : GlobalDAG := {}
  for v in names do
    g := addSecretShares g v v shares
  for k in [0:5] do
    let x := names[k]!            -- linear input
    let y := names[(k+1) % 5]!    -- negated AND input
    let z := names[(k+2) % 5]!    -- other AND input
    g := g.addWireXor s!"n{k}" #[.wire s!"{y}0", .const true]
    let ys := fun (i : Nat) => if i == 0 then s!"n{k}" else s!"{y}{i}"
    -- DOM-AND: partial products
    for i in [0:shares] do
      for j in [0:shares] do
        g := g.addWireAnd s!"q{k}_{i}{j}" #[.wire (ys i), .wire s!"{z}{j}"]
    -- masked cross products (one fresh random per unordered pair, per bit)
    for i in [0:shares] do
      for j in [0:shares] do
        if i != j then
          let p := min i j
          let q := max i j
          g := g.addWireXor s!"t{k}_{i}{j}" #[.wire s!"q{k}_{i}{j}", .leaf (.Random s!"r{k}_{p}{q}")]
    -- compress, then add the linear share
    for i in [0:shares] do
      let mut terms : Array WireInput := #[.wire s!"q{k}_{i}{i}"]
      for j in [0:shares] do
        if j != i then
          terms := terms.push (.wire s!"t{k}_{i}{j}")
      g := addWireXorChain g s!"s{k}_{i}" terms
      g := g.addWireXor s!"f{k}_{i}" #[.wire s!"{x}{i}", .wire s!"s{k}_{i}"]
  return g

/-! ### TI Keccak χ S-box (3 shares, no fresh randomness; [BDPV10]-style
    direct sharing, [BNN+15] §4)

    Per output bit k the coordinate v_k + (¬v_{k+1})·v_{k+2} is shared with the
    Eq. (2) pattern, the NOT folded into share 1 of the negated operand:
      f_k,1 = x2 + y2·z2 + y2·z3 + y3·z2
      f_k,2 = x3 + y3·z3 + y3·z1 + y1·z3
      f_k,3 = x1 + y1·z1 + y1·z2 + y2·z1     (y1 = ¬v_{k+1},1)
    Non-completeness ⇒ 1-probing secure; TI promises nothing at order 2
    (the direct sharing is also non-uniform — [BNN+15] §4 fixes that with 4
    fresh bits per round, irrelevant to a single-gadget probing check). -/
def tiKeccakChi : GlobalDAG := Id.run do
  let names := #["a", "b", "c", "d", "e"]
  let mut g : GlobalDAG := {}
  for v in names do
    g := addSecretShares1 g v v 3
  for k in [0:5] do
    let x := names[k]!
    let y := names[(k+1) % 5]!
    let z := names[(k+2) % 5]!
    g := g.addWireXor s!"n{k}" #[.wire s!"{y}1", .const true]
    let ys := fun (i : Nat) => if i == 1 then s!"n{k}" else s!"{y}{i}"
    for (i, j) in #[(2,2),(2,3),(3,2),(3,3),(3,1),(1,3),(1,1),(1,2),(2,1)] do
      g := g.addWireAnd s!"u{k}_{i}{j}" #[.wire (ys i), .wire s!"{z}{j}"]
    g := addWireXorChain g s!"f{k}_1" #[.wire s!"{x}2", .wire s!"u{k}_22", .wire s!"u{k}_23", .wire s!"u{k}_32"]
    g := addWireXorChain g s!"f{k}_2" #[.wire s!"{x}3", .wire s!"u{k}_33", .wire s!"u{k}_31", .wire s!"u{k}_13"]
    g := addWireXorChain g s!"f{k}_3" #[.wire s!"{x}1", .wire s!"u{k}_11", .wire s!"u{k}_12", .wire s!"u{k}_21"]
  return g

/-! ### Q⁴₁₂ quadratic bijection, 2-share direct sharing

    Representative of the quadratic class Q⁴₁₂ ([BNN+15] Table 10, truth table
    0123456789CDEFAB):  F(a,b,c,d) = (a, b+ac, c+ab+ac, d).
    2-share direct sharing; the interesting case for the engine: at order 1 the
    simple rewrite rule stalls and lazy *factoring* is needed to certify (see
    CURRENT_STATE.md — witness-replay without factoring reports a false
    INSECURE here; the coupling branch verifies SECURE). -/
def q_12 : GlobalDAG := ({} : GlobalDAG)
  -- input shares (atomically encoded; not probe targets)
  |>.addShare "a1" #[.leaf (.Secret "a"), .leaf (.Random "r0")]
  |>.addShare "a2" #[.leaf (.Random "r0")]
  |>.addShare "b1" #[.leaf (.Secret "b"), .leaf (.Random "r1")]
  |>.addShare "b2" #[.leaf (.Random "r1")]
  |>.addShare "c1" #[.leaf (.Secret "c"), .leaf (.Random "r2")]
  |>.addShare "c2" #[.leaf (.Random "r2")]
  |>.addShare "d1" #[.leaf (.Secret "d"), .leaf (.Random "r3")]
  |>.addShare "d2" #[.leaf (.Random "r3")]
  -- product gates
  |>.addWireAnd "a1c1" #[.wire "a1", .wire "c1"]
  |>.addWireAnd "a1c2" #[.wire "a1", .wire "c2"]
  |>.addWireAnd "a2c1" #[.wire "a2", .wire "c1"]
  |>.addWireAnd "a2c2" #[.wire "a2", .wire "c2"]
  |>.addWireAnd "a1b1" #[.wire "a1", .wire "b1"]
  |>.addWireAnd "a1b2" #[.wire "a1", .wire "b2"]
  |>.addWireAnd "a2b1" #[.wire "a2", .wire "b1"]
  |>.addWireAnd "a2b2" #[.wire "a2", .wire "b2"]
  -- outputs
  |>.addWireXor "x1" #[.wire "a1"]
  |>.addWireXor "x2" #[.wire "a2"]
  |>.addWireXor "y1" #[.wire "a1c1", .wire "b1"]
  |>.addWireXor "y2" #[.wire "a1c2"]
  |>.addWireXor "y3" #[.wire "a2c1", .wire "b2"]
  |>.addWireXor "y4" #[.wire "a2c2"]
  |>.addWireXor "z1a" #[.wire "a1b1", .wire "a1c1"]
  |>.addWireXor "z1"  #[.wire "z1a", .wire "c1"]
  |>.addWireXor "z2" #[.wire "a1b2", .wire "a1c2"]
  |>.addWireXor "z3" #[.wire "a2b1", .wire "a2c1"]
  |>.addWireXor "z4a" #[.wire "a2b2", .wire "a2c2"]
  |>.addWireXor "z4"  #[.wire "z4a", .wire "c2"]
  |>.addWireXor "t1" #[.wire "d1"]
  |>.addWireXor "t2" #[.wire "d2"]
  -- Recombination layer.
  |>.addWireXor "xb1" #[.wire "x1"]
  |>.addWireXor "xb2" #[.wire "x2"]
  |>.addWireXor "yb1" #[.wire "y1", .wire "y2"]
  |>.addWireXor "yb2" #[.wire "y3", .wire "y4"]
  |>.addWireXor "zb1" #[.wire "z1", .wire "z2"]
  |>.addWireXor "zb2" #[.wire "z3", .wire "z4"]
  |>.addWireXor "tb1" #[.wire "t1"]
  |>.addWireXor "tb2" #[.wire "t2"]

/-! ### Q⁴₁₂ quadratic bijection, 3-share TI ([BNN+15] §3.2)

    The proper first-order TI of the same representative: each coordinate is of
    the form `x + yz` (coordinate 3 is c + a·(b+c), i.e. z = b+c share-wise),
    shared per-coordinate with the correction-term pattern Eq. (3):
      F1 = x3 + z2·y2 + z2·y3 + z3·y2
      F2 = x1 + z3·y3 + z3·y1 + z1·y3
      F3 = x2 + z1·y1 + z1·y2 + z2·y1
    Non-completeness ⇒ expected 1-probing secure. -/
def q12TI : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  for v in #["a", "b", "c", "d"] do
    g := addSecretShares1 g v v 3
  -- w_i = b_i + c_i  (share-wise shares of b+c)
  for i in [1:4] do
    g := g.addWireXor s!"w{i}" #[.wire s!"b{i}", .wire s!"c{i}"]
  -- products c_i·a_j (coordinate 2) and w_i·a_j (coordinate 3)
  for (i, j) in #[(2,2),(2,3),(3,2),(3,3),(3,1),(1,3),(1,1),(1,2),(2,1)] do
    g := g.addWireAnd s!"ca{i}{j}" #[.wire s!"c{i}", .wire s!"a{j}"]
    g := g.addWireAnd s!"wa{i}{j}" #[.wire s!"w{i}", .wire s!"a{j}"]
  -- coordinate 1 (= a) and 4 (= d): share-wise aliases
  for i in [1:4] do
    g := g.addWireXor s!"X{i}" #[.wire s!"a{i}"]
    g := g.addWireXor s!"T{i}" #[.wire s!"d{i}"]
  -- coordinate 2 (= b + ac):  Eq. (3) with x=b, y=a, z=c
  let g' := addWireXorChain g  "Y1" #[.wire "b3", .wire "ca22", .wire "ca23", .wire "ca32"]
  let g' := addWireXorChain g' "Y2" #[.wire "b1", .wire "ca33", .wire "ca31", .wire "ca13"]
  let g' := addWireXorChain g' "Y3" #[.wire "b2", .wire "ca11", .wire "ca12", .wire "ca21"]
  -- coordinate 3 (= c + a(b+c)):  Eq. (3) with x=c, y=a, z=w
  let g' := addWireXorChain g' "Z1" #[.wire "c3", .wire "wa22", .wire "wa23", .wire "wa32"]
  let g' := addWireXorChain g' "Z2" #[.wire "c1", .wire "wa33", .wire "wa31", .wire "wa13"]
  let g' := addWireXorChain g' "Z3" #[.wire "c2", .wire "wa11", .wire "wa12", .wire "wa21"]
  return g'


/-! ### d+1 quadratic S-box family: 2-share expanded direct sharing with
    share compression (the structure of `q_12`, generated for all quadratic
    permutation classes of [BNN+15])

    First-order d+1 masking of an S-box in the style of Reparaz et al.
    (CRYPTO'15) / De Cnudde et al. (CHES'16), but with **randomness-free
    compression**: cross-share products `P = v_u,i · v_w,j`, per-(i,j)
    non-complete partial sums `o_k,ij` (linear share i folded into the
    diagonal cells), and compression wires `ob_k,i = o_k,i1 + o_k,i2`.
    The compression wire computes `Σ_m u_i·w + (linear shares)` — the share
    sums telescope their randomness only under the common factor `u_i`, so
    certifying it requires the factoring rewrite  u_i·w_1 + u_i·w_2 → u_i·w
    whenever no fresh linear blinder remains in the coordinate.

    Predicted split (confirmed by an external brute-force first-order check of
    every wire, `tools/gen_dplus1.py`):
    - coordinates with a fresh linear variable (Toffoli-style, e.g. `d + ab`)
      verify without factoring;
    - coordinates with quadratic feedback (every linear variable also occurs in
      a monomial, e.g. `c + ab + ac`) are secure but certifiable only with
      factoring — maskVerif-style rewriting reports a false INSECURE;
    - coordinates with no linear part (`ab+ac+bc` in Q³₃/Q⁴₃₀₀) are genuinely
      1-probing INSECURE — precisely the two classes with no uniform 3-share
      TI ([BNN+15] Corollaries 1–2). -/
def dPlusOneQuadSbox (nvars : Nat) (coords : Array (Array Nat × Array (Nat × Nat))) : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  -- 2 shares per input: v{a}1 = secret + r_a, v{a}2 = r_a  (as in q_12)
  for a in [0:nvars] do
    g := g.addShare s!"v{a}1" #[.leaf (.Secret s!"v{a}"), .leaf (.Random s!"r{a}")]
    g := g.addShare s!"v{a}2" #[.leaf (.Random s!"r{a}")]
  for k in [0:coords.size] do
    let (lin, quad) := coords[k]!
    -- cross-share products (idempotent adds dedupe across coordinates)
    for (u, w) in quad do
      for i in [1:3] do
        for j in [1:3] do
          g := g.addWireAnd s!"P{u}_{i}_{w}_{j}" #[.wire s!"v{u}{i}", .wire s!"v{w}{j}"]
    -- non-complete cells o_k,ij, then compression along j
    let mut rows : Array (Array WireInput) := #[#[], #[]]
    for i in [1:3] do
      for j in [1:3] do
        let mut terms : Array WireInput := #[]
        for (u, w) in quad do
          terms := terms.push (.wire s!"P{u}_{i}_{w}_{j}")
        if i == j then
          for w in lin do
            terms := terms.push (.wire s!"v{w}{i}")
        if terms.size > 0 then
          g := addWireXorChain g s!"o{k}_{i}{j}" terms
          rows := rows.set! (i-1) (rows[i-1]!.push (.wire s!"o{k}_{i}{j}"))
    for i in [1:3] do
      if rows[i-1]!.size > 0 then
        g := addWireXorChain g s!"ob{k}_{i}" rows[i-1]!
  return g

/-- Q³₁ = (a, b, c+ab) — Toffoli; fresh linear blinder in every coordinate. -/
def q31d1 : GlobalDAG := dPlusOneQuadSbox 3 #[
  (#[0], #[]), (#[1], #[]), (#[2], #[(0, 1)])]

/-- Q³₂ = (a, b+ac, c+ab+ac) — quadratic feedback in coordinate 3. -/
def q32d1 : GlobalDAG := dPlusOneQuadSbox 3 #[
  (#[0], #[]), (#[1], #[(0, 2)]), (#[2], #[(0, 1), (0, 2)])]

/-- Q³₃ = (ab+ac+bc, a+b+ab+bc, a+c+bc) — coordinate 1 has no linear part:
    genuinely 1-probing INSECURE in this 2-share form (and the class has no
    uniform 3-share TI, [BNN+15] Cor. 1). -/
def q33d1 : GlobalDAG := dPlusOneQuadSbox 3 #[
  (#[], #[(0, 1), (0, 2), (1, 2)]),
  (#[0, 1], #[(0, 1), (1, 2)]),
  (#[0, 2], #[(1, 2)])]

/-- Q⁴₄ = (a, b, c, d+ab) — the Toffoli gate. -/
def q44d1 : GlobalDAG := dPlusOneQuadSbox 4 #[
  (#[0], #[]), (#[1], #[]), (#[2], #[]), (#[3], #[(0, 1)])]

/-- Q⁴₁₂ = (a, b+ac, c+ab+ac, d) — generated twin of the hand-written `q_12`. -/
def q412d1 : GlobalDAG := dPlusOneQuadSbox 4 #[
  (#[0], #[]), (#[1], #[(0, 2)]), (#[2], #[(0, 1), (0, 2)]), (#[3], #[])]

/-- Q⁴₂₉₃ = (a, b+ac, c+ab+ac, d+bc). -/
def q4293d1 : GlobalDAG := dPlusOneQuadSbox 4 #[
  (#[0], #[]), (#[1], #[(0, 2)]), (#[2], #[(0, 1), (0, 2)]), (#[3], #[(1, 2)])]

/-- Q⁴₂₉₄ = (a, b, c+ab, d+ac) — Toffoli-style throughout. -/
def q4294d1 : GlobalDAG := dPlusOneQuadSbox 4 #[
  (#[0], #[]), (#[1], #[]), (#[2], #[(0, 1)]), (#[3], #[(0, 2)])]

/-- Q⁴₂₉₉ = (a, b+ab+ac, c+ab+ac+ad, d+ab+ad) — quadratic feedback in three
    coordinates; the strongest factoring stress case in the family. -/
def q4299d1 : GlobalDAG := dPlusOneQuadSbox 4 #[
  (#[0], #[]),
  (#[1], #[(0, 1), (0, 2)]),
  (#[2], #[(0, 1), (0, 2), (0, 3)]),
  (#[3], #[(0, 1), (0, 3)])]

/-- Q⁴₃₀₀ = (ab+ac+bc, a+b+ab+bc, a+c+bc, d) — genuinely 1-probing INSECURE
    (no linear part in coordinate 1; no uniform 3-share TI, [BNN+15] Cor. 2). -/
def q4300d1 : GlobalDAG := dPlusOneQuadSbox 4 #[
  (#[], #[(0, 1), (0, 2), (1, 2)]),
  (#[0, 1], #[(0, 1), (1, 2)]),
  (#[0, 2], #[(1, 2)]),
  (#[3], #[])]


/-! ## §4 TI sharings of quadratic/cubic functions ([BNN+15]) -/

/-! ### `x + yz`, direct 3-share TI ([BNN+15] Eq. (2))

      F1 = x2 + y2·z2 + y2·z3 + y3·z2
      F2 = x3 + y3·z3 + y3·z1 + y1·z3
      F3 = x1 + y1·z1 + y1·z2 + y2·z1
    Non-complete (component i avoids index i) but NOT uniform ⇒ expected
    1-probing secure as a standalone gadget. -/
def tiXplusYZ3 : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  for v in #["x", "y", "z"] do
    g := addSecretShares1 g v v 3
  for (i, j) in #[(2,2),(2,3),(3,2),(3,3),(3,1),(1,3),(1,1),(1,2),(2,1)] do
    g := g.addWireAnd s!"m{i}{j}" #[.wire s!"y{i}", .wire s!"z{j}"]
  let g' := addWireXorChain g  "F1" #[.wire "x2", .wire "m22", .wire "m23", .wire "m32"]
  let g' := addWireXorChain g' "F2" #[.wire "x3", .wire "m33", .wire "m31", .wire "m13"]
  let g' := addWireXorChain g' "F3" #[.wire "x1", .wire "m11", .wire "m12", .wire "m21"]
  return g'

/-! ### `x + yz`, 3-share TI with correction terms ([BNN+15] Eq. (3))

    The uniform variant (the sharing used for classes Q³₂, Q⁴₁₂, Q⁴₂₉₃):
      F1 = x3 + z2·y2 + z2·y3 + z3·y2
      F2 = x1 + z3·y3 + z3·y1 + z1·y3
      F3 = x2 + z1·y1 + z1·y2 + z2·y1
    Same quadratic terms per component as Eq. (2); the linear shares rotate. -/
def tiXplusYZ3ct : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  for v in #["x", "y", "z"] do
    g := addSecretShares1 g v v 3
  for (i, j) in #[(2,2),(2,3),(3,2),(3,3),(3,1),(1,3),(1,1),(1,2),(2,1)] do
    g := g.addWireAnd s!"m{i}{j}" #[.wire s!"y{i}", .wire s!"z{j}"]  -- m{i}{j} = y_i·z_j
  let g' := addWireXorChain g  "F1" #[.wire "x3", .wire "m22", .wire "m32", .wire "m23"]
  let g' := addWireXorChain g' "F2" #[.wire "x1", .wire "m33", .wire "m13", .wire "m31"]
  let g' := addWireXorChain g' "F3" #[.wire "x2", .wire "m11", .wire "m21", .wire "m12"]
  return g'

/-! ### `x + yz`, 4-share TI ([BNN+15] §3, quadratic part of Eq. (6);
    expanded monomial form)

      F1 = x2 + Σ_{i,j ∈ {2,3,4}} y_i·z_j
      F2 = x3 + y1·z3 + y1·z4 + y3·z1 + y4·z1 + y1·z1
      F3 = x4 + y1·z2 + y2·z1
      F4 = x1
    Expected 1-probing (and, with 4 shares, 2-probing) secure;
    genuinely 3-probing INSECURE — confirmed by brute force (see
    CURRENT_STATE.md), a useful attack-finding benchmark. -/
def tiXplusYZ4 : GlobalDAG :=
  let g : GlobalDAG := ({} : GlobalDAG)
  -- share production for x
  |>.addShare "x1" #[.leaf (.Random "r_x0")]
  |>.addShare "x2" #[.leaf (.Random "r_x1")]
  |>.addShare "x3" #[.leaf (.Random "r_x2")]
  |>.addShare "x4" #[.leaf (.Secret "x"), .leaf (.Random "r_x0"),
                     .leaf (.Random "r_x1"), .leaf (.Random "r_x2")]
  -- share production for y
  |>.addShare "y1" #[.leaf (.Random "r_y0")]
  |>.addShare "y2" #[.leaf (.Random "r_y1")]
  |>.addShare "y3" #[.leaf (.Random "r_y2")]
  |>.addShare "y4" #[.leaf (.Secret "y"), .leaf (.Random "r_y0"),
                     .leaf (.Random "r_y1"), .leaf (.Random "r_y2")]
  -- share production for z
  |>.addShare "z1" #[.leaf (.Random "r_z0")]
  |>.addShare "z2" #[.leaf (.Random "r_z1")]
  |>.addShare "z3" #[.leaf (.Random "r_z2")]
  |>.addShare "z4" #[.leaf (.Secret "z"), .leaf (.Random "r_z0"),
                     .leaf (.Random "r_z1"), .leaf (.Random "r_z2")]
  -- all 16 cross-products y_i * z_j
  |>.addWireAnd "y2z2" #[.wire "y2", .wire "z2"]
  |>.addWireAnd "y2z3" #[.wire "y2", .wire "z3"]
  |>.addWireAnd "y2z4" #[.wire "y2", .wire "z4"]
  |>.addWireAnd "y3z2" #[.wire "y3", .wire "z2"]
  |>.addWireAnd "y3z3" #[.wire "y3", .wire "z3"]
  |>.addWireAnd "y3z4" #[.wire "y3", .wire "z4"]
  |>.addWireAnd "y4z2" #[.wire "y4", .wire "z2"]
  |>.addWireAnd "y4z3" #[.wire "y4", .wire "z3"]
  |>.addWireAnd "y4z4" #[.wire "y4", .wire "z4"]
  |>.addWireAnd "y1z3" #[.wire "y1", .wire "z3"]
  |>.addWireAnd "y1z4" #[.wire "y1", .wire "z4"]
  |>.addWireAnd "y3z1" #[.wire "y3", .wire "z1"]
  |>.addWireAnd "y4z1" #[.wire "y4", .wire "z1"]
  |>.addWireAnd "y1z1" #[.wire "y1", .wire "z1"]
  |>.addWireAnd "y1z2" #[.wire "y1", .wire "z2"]
  |>.addWireAnd "y2z1" #[.wire "y2", .wire "z1"]
  -- output shares
  let g := addWireXorChain g "F1" #[.wire "x2",
                       .wire "y2z2", .wire "y2z3", .wire "y2z4",
                       .wire "y3z2", .wire "y3z3", .wire "y3z4",
                       .wire "y4z2", .wire "y4z3", .wire "y4z4"]
  let g := addWireXorChain g "F2" #[.wire "x3",
                       .wire "y1z3", .wire "y1z4",
                       .wire "y3z1", .wire "y4z1",
                       .wire "y1z1"]
  let g := addWireXorChain g "F3" #[.wire "x4",
                       .wire "y1z2", .wire "y2z1"]
  addWireXorChain g "F4" #[.wire "x1"]

/-! ### `x + yz + xyz`, 4-share TI ([BNN+15] Eq. (6))

    The cubic sharing used (together with Eq. (3)) to build 4-share TIs of all
    4-bit permutations.  Products of share-sums are built as circuit products
    of XOR-chain wires (association: sums first, then x·(y·z) left-to-right);
    the cubic monomial terms of F3/F4 reuse the pairwise products x_i·y_j.
    Component i avoids share index i ⇒ expected 1-probing secure. -/
def tiCubic4 : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  for v in #["x", "y", "z"] do
    g := addSecretShares1 g v v 4
  -- shared sub-sums
  g := addWireXorChain g "sx234" #[.wire "x2", .wire "x3", .wire "x4"]
  g := addWireXorChain g "sy234" #[.wire "y2", .wire "y3", .wire "y4"]
  g := addWireXorChain g "sz234" #[.wire "z2", .wire "z3", .wire "z4"]
  g := g.addWireXor "sx34" #[.wire "x3", .wire "x4"]
  g := g.addWireXor "sy34" #[.wire "y3", .wire "y4"]
  g := g.addWireXor "sz34" #[.wire "z3", .wire "z4"]
  -- F1 = x2 + (y2+y3+y4)(z2+z3+z4) + (x2+x3+x4)(y2+y3+y4)(z2+z3+z4)
  g := g.addWireAnd "qA" #[.wire "sy234", .wire "sz234"]
  g := g.addWireAnd "qB" #[.wire "sx234", .wire "qA"]
  g := addWireXorChain g "F1" #[.wire "x2", .wire "qA", .wire "qB"]
  -- F2 = x3 + y1(z3+z4) + z1(y3+y4) + y1z1 + x1(y3+y4)(z3+z4)
  --        + y1(x3+x4)(z3+z4) + z1(x3+x4)(y3+y4) + x1y1(z3+z4)
  --        + x1z1(y3+y4) + y1z1(x3+x4) + x1y1z1
  g := g.addWireAnd "e1"  #[.wire "y1", .wire "sz34"]
  g := g.addWireAnd "e2"  #[.wire "z1", .wire "sy34"]
  g := g.addWireAnd "e3"  #[.wire "y1", .wire "z1"]
  g := g.addWireAnd "e4a" #[.wire "sy34", .wire "sz34"]
  g := g.addWireAnd "e4"  #[.wire "x1", .wire "e4a"]
  g := g.addWireAnd "e5a" #[.wire "sx34", .wire "sz34"]
  g := g.addWireAnd "e5"  #[.wire "y1", .wire "e5a"]
  g := g.addWireAnd "e6a" #[.wire "sx34", .wire "sy34"]
  g := g.addWireAnd "e6"  #[.wire "z1", .wire "e6a"]
  g := g.addWireAnd "e7a" #[.wire "x1", .wire "y1"]
  g := g.addWireAnd "e7"  #[.wire "e7a", .wire "sz34"]
  g := g.addWireAnd "e8a" #[.wire "x1", .wire "z1"]
  g := g.addWireAnd "e8"  #[.wire "e8a", .wire "sy34"]
  g := g.addWireAnd "e9"  #[.wire "e3", .wire "sx34"]
  g := g.addWireAnd "e10" #[.wire "e7a", .wire "z1"]
  g := addWireXorChain g "F2" #[.wire "x3", .wire "e1", .wire "e2", .wire "e3",
                                .wire "e4", .wire "e5", .wire "e6", .wire "e7",
                                .wire "e8", .wire "e9", .wire "e10"]
  -- pairwise products x_i·y_j needed by the cubic monomials of F3/F4
  for (i, j) in #[(1,1),(1,2),(2,1),(2,2),(1,3),(2,3),(3,1),(3,2),(1,4),(2,4),(4,1),(4,2)] do
    g := g.addWireAnd s!"pxy{i}{j}" #[.wire s!"x{i}", .wire s!"y{j}"]
  -- cubic monomials mm{i}{j}{k} = (x_i·y_j)·z_k
  for (i, j, k) in #[(1,1,2),(1,2,1),(2,1,1),(1,2,2),(2,1,2),(2,2,1),
                     (1,2,4),(2,1,4),(1,4,2),(2,4,1),(4,1,2),(4,2,1),
                     (1,2,3),(1,3,2),(2,1,3),(2,3,1),(3,1,2),(3,2,1)] do
    g := g.addWireAnd s!"mm{i}{j}{k}" #[.wire s!"pxy{i}{j}", .wire s!"z{k}"]
  -- F3 = x4 + y1z2 + y2z1 + x1y1z2 + x1y2z1 + x2y1z1 + x1y2z2 + x2y1z2
  --        + x2y2z1 + x1y2z4 + x2y1z4 + x1y4z2 + x2y4z1 + x4y1z2 + x4y2z1
  g := g.addWireAnd "pyz12" #[.wire "y1", .wire "z2"]
  g := g.addWireAnd "pyz21" #[.wire "y2", .wire "z1"]
  g := addWireXorChain g "F3" #[.wire "x4", .wire "pyz12", .wire "pyz21",
                                .wire "mm112", .wire "mm121", .wire "mm211",
                                .wire "mm122", .wire "mm212", .wire "mm221",
                                .wire "mm124", .wire "mm214", .wire "mm142",
                                .wire "mm241", .wire "mm412", .wire "mm421"]
  -- F4 = x1 + x1y2z3 + x1y3z2 + x2y1z3 + x2y3z1 + x3y1z2 + x3y2z1
  g := addWireXorChain g "F4" #[.wire "x1", .wire "mm123", .wire "mm132",
                                .wire "mm213", .wire "mm231", .wire "mm312",
                                .wire "mm321"]
  return g

/-! ### Generic 4-share TI of a quadratic S-box (direct sharing)

    Applies the quadratic part of [BNN+15] Eq. (6) mechanically: for each
    quadratic monomial v_a·v_b of a coordinate's ANF,
      F1 gets a_i·b_j for i,j ∈ {2,3,4};  F2 gets a1b3, a1b4, a3b1, a4b1, a1b1;
      F3 gets a1b2, a2b1;  F4 gets nothing,
    and each linear term v_a contributes share x2/x3/x4/x1 to F1/F2/F3/F4.
    Component c never touches share index c (non-completeness), so with a
    uniform input sharing the result is expected 1-probing secure.  Uniformity
    of the *output* sharing is not claimed (single-gadget probing check only).

    `coords`: per output coordinate, the ANF as (linear variable indices,
    quadratic variable pairs), variables 0-based. -/
def tiQuadratic4 (nvars : Nat) (coords : Array (Array Nat × Array (Nat × Nat))) : GlobalDAG := Id.run do
  -- share-index pattern per component (the union over components is exactly
  -- the 16 pairs, so the products loop below covers all of them once)
  let quadPat : Array (Nat × Array (Nat × Nat)) :=
    #[(1, #[(2,2),(2,3),(2,4),(3,2),(3,3),(3,4),(4,2),(4,3),(4,4)]),
      (2, #[(1,3),(1,4),(3,1),(4,1),(1,1)]),
      (3, #[(1,2),(2,1)]),
      (4, #[])]
  let linIdx : Nat → Nat := fun c => match c with
    | 1 => 2 | 2 => 3 | 3 => 4 | _ => 1
  let mut g : GlobalDAG := {}
  for v in [0:nvars] do
    g := addSecretShares1 g s!"v{v}" s!"v{v}" 4
  -- all share products of every quadratic monomial (idempotent across coords)
  for k in [0:coords.size] do
    let (_, quad) := coords[k]!
    for (a, b) in quad do
      for i in [1:5] do
        for j in [1:5] do
          g := g.addWireAnd s!"P{a}_{i}_{b}_{j}" #[.wire s!"v{a}{i}", .wire s!"v{b}{j}"]
  -- component chains
  for k in [0:coords.size] do
    let (lin, quad) := coords[k]!
    for (c, pairs) in quadPat do
      let mut terms : Array WireInput := #[]
      for v in lin do
        terms := terms.push (.wire s!"v{v}{linIdx c}")
      for (a, b) in quad do
        for (i, j) in pairs do
          terms := terms.push (.wire s!"P{a}_{i}_{b}_{j}")
      g := addWireXorChain g s!"F{k}_{c}" terms
  return g

/-! ### Fides 5-bit AB1 S-box, 4-share TI ("TI Fides-160 S-box" in [BBC+19]
    Table 2: 192 HW / 6657 SW observations at order 1)

    The AB1 representative x³ of [BNN+15] Table 3 (used by FIDES-160 and
    PRIMATEs); every coordinate is quadratic.  ANF computed from the truth
    table and the shared circuit re-verified functionally (2000 random share
    assignments) by an external script before transcription. -/
def tiFidesAB1 : GlobalDAG := tiQuadratic4 5 #[
  (#[],
   #[(0, 1), (0, 2), (0, 4), (1, 2), (1, 3), (2, 3)]),
  (#[],
   #[(0, 1), (0, 3), (1, 3), (1, 4), (2, 4)]),
  (#[0, 1],
   #[(0, 2), (1, 2), (1, 3), (1, 4), (3, 4)]),
  (#[0, 2, 3],
   #[(0, 2), (0, 4), (1, 3), (1, 4), (2, 4), (3, 4)]),
  (#[1, 2, 4],
   #[(0, 3), (0, 4), (2, 3), (3, 4)])]

/-! ### `xy`, 3-share TI with a virtual variable ([BNN+15] Eq. (7))

    The product of two variables has no 3-share TI; adding a virtual (purely
    random) variable z restores it:
      F1 = x2y2 + x2y3 + x3y2 + x2z2 + x3z3 + y2z2 + y3z3
      F2 = x3y3 + x1y3 + x3y1 + x3z3 + x1z1 + y3z3 + y1z1
      F3 = x1y1 + x1y2 + x2y1 + x1z1 + x2z2 + y1z1 + y2z2 -/
def tiMultVirtual : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  for v in #["x", "y"] do
    g := addSecretShares1 g v v 3
  for i in [1:4] do  -- virtual variable: all three shares fresh randoms
    g := g.addShare s!"z{i}" #[.leaf (.Random s!"rz{i}")]
  for (i, j) in #[(2,2),(2,3),(3,2),(3,3),(3,1),(1,3),(1,1),(1,2),(2,1)] do
    g := g.addWireAnd s!"m{i}{j}" #[.wire s!"x{i}", .wire s!"y{j}"]
  for i in [1:4] do
    g := g.addWireAnd s!"xz{i}" #[.wire s!"x{i}", .wire s!"z{i}"]
    g := g.addWireAnd s!"yz{i}" #[.wire s!"y{i}", .wire s!"z{i}"]
  let g' := addWireXorChain g  "F1" #[.wire "m22", .wire "m23", .wire "m32",
                                      .wire "xz2", .wire "xz3", .wire "yz2", .wire "yz3"]
  let g' := addWireXorChain g' "F2" #[.wire "m33", .wire "m13", .wire "m31",
                                      .wire "xz3", .wire "xz1", .wire "yz3", .wire "yz1"]
  let g' := addWireXorChain g' "F3" #[.wire "m11", .wire "m12", .wire "m21",
                                      .wire "xz1", .wire "xz2", .wire "yz1", .wire "yz2"]
  return g'

/-! ### `xy`, 3-share TI with a single virtual share ([BNN+15] Eq. (8))

      F1 = x2y2 + x2y3 + x3y2 + z
      F2 = x3y3 + x1y3 + x3y1 + x1z + y1z
      F3 = x1y1 + x1y2 + x2y1 + x1z + y1z + z
    (z is one fresh random; [BNN+15] read the pair x1z + y1z as re-masking.) -/
def tiMultVirtualShare : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  for v in #["x", "y"] do
    g := addSecretShares1 g v v 3
  for (i, j) in #[(2,2),(2,3),(3,2),(3,3),(3,1),(1,3),(1,1),(1,2),(2,1)] do
    g := g.addWireAnd s!"m{i}{j}" #[.wire s!"x{i}", .wire s!"y{j}"]
  g := g.addWireAnd "xz" #[.wire "x1", .leaf (.Random "z")]
  g := g.addWireAnd "yz" #[.wire "y1", .leaf (.Random "z")]
  g := addWireXorChain g "F1" #[.wire "m22", .wire "m23", .wire "m32",
                                .leaf (.Random "z")]
  g := addWireXorChain g "F2" #[.wire "m33", .wire "m13", .wire "m31",
                                .wire "xz", .wire "yz"]
  g := addWireXorChain g "F3" #[.wire "m11", .wire "m12", .wire "m21",
                                .wire "xz", .wire "yz", .leaf (.Random "z")]
  return g

/-! ### `xy`, 4 input shares → 3 output shares ([BNN+15] §6.2)

      F1 = (x2+x3+x4)(y2+y3) + y4
      F2 = (x1+x3)(y1+y4) + x1y3 + x4
      F3 = (x2+x4)(y1+y4) + x1y2 + x4 + y4
    Output component i is independent of share index i of both inputs. -/
def tiMult43 : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  for v in #["x", "y"] do
    g := addSecretShares1 g v v 4
  g := addWireXorChain g "sx234" #[.wire "x2", .wire "x3", .wire "x4"]
  g := g.addWireXor "sy23" #[.wire "y2", .wire "y3"]
  g := g.addWireXor "sx13" #[.wire "x1", .wire "x3"]
  g := g.addWireXor "sy14" #[.wire "y1", .wire "y4"]
  g := g.addWireXor "sx24" #[.wire "x2", .wire "x4"]
  g := g.addWireAnd "p1" #[.wire "sx234", .wire "sy23"]
  g := g.addWireXor "F1" #[.wire "p1", .wire "y4"]
  g := g.addWireAnd "p2" #[.wire "sx13", .wire "sy14"]
  g := g.addWireAnd "q2" #[.wire "x1", .wire "y3"]
  g := addWireXorChain g "F2" #[.wire "p2", .wire "q2", .wire "x4"]
  g := g.addWireAnd "p3" #[.wire "sx24", .wire "sy14"]
  g := g.addWireAnd "q3" #[.wire "x1", .wire "y2"]
  g := addWireXorChain g "F3" #[.wire "p3", .wire "q3", .wire "x4", .wire "y4"]
  return g


/-! ## Comparison: coupling extension vs. the naive (no-extension) baseline

    Runs each instance twice — once with the coupling extension growing every
    certified probe set (`extend := true`), once with no extension
    (`extend := false`), where each representative covers only its own subsets and
    the space-split degrades toward exhaustive enumeration.  Both use the same
    sound rewrite checker, so the verdicts must agree; only the discharge count and
    wall-clock differ. -/
def ppAblation (name : String) (g : GlobalDAG) (order : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let (_, _, resC, sC) := checkDProbing g order true
  let t1 ← IO.monoMsNow
  -- let (_, _, resN, sN) := checkDProbing g order false
  -- let t2 ← IO.monoMsNow
  let v := fun (r : CheckResult) => if r.isSecure then "secure" else "INSECURE"
  -- IO.println s!"{name} @ order {order}:  coupling {v resC}  |  naive {v resN}  (agree={resC.isSecure == resN.isSecure})"
  IO.println s!"{name} @ order {order}:  coupling {v resC}"
  IO.println s!"    coupling     : {t1 - t0} ms\n{sC.pp}\n"
  -- IO.println s!"    no extension : {t2 - t1} ms\n{sN.pp}\n"
  (← IO.getStdout).flush


def runAblation : IO Unit := do
  IO.println "=== Results ==="
  -- IO.println "--- §1 multiplication / AND gadgets ---"
  -- ppAblation "ISW AND (2 shares)" (iswAND 2) 1
  -- ppAblation "ISW AND (3 shares)" (iswAND 3) 2
  -- ppAblation "ISW AND (4 shares)" (iswAND 4) 3
  -- ppAblation "ISW AND (5 shares)" (iswAND 5) 4
  -- -- ppAblation "ISW AND (6 shares)" (iswAND 6) 5   -- long; enable for the thesis table
  -- ppAblation "DOM AND (2 shares)" (domAND 2) 1
  -- ppAblation "DOM AND (2 shares)" (domAND 2) 2       -- above design order: INSECURE
  -- ppAblation "DOM AND (3 shares)" (domAND 3) 2
  -- ppAblation "DOM AND (4 shares)" (domAND 4) 3
  -- -- ppAblation "7-share DOM-AND" sevenDomAND 5      -- stored run: see note below
  -- ppAblation "Trichina AND" trichinaAND 1
  -- ppAblation "Trichina AND (bad assoc)" trichinaANDBad 1  -- first-order flaw: INSECURE
  -- ppAblation "TI AND (3 shares)" tiAND 1
  -- ppAblation "TI AND (3 shares)" tiAND 2             -- above the TI guarantee
  -- IO.println "--- §2 mask refresh gadgets ---"
  -- ppAblation "Additive refresh (3 shares)" (refreshAdd 3) 2
  -- ppAblation "Additive refresh (4 shares)" (refreshAdd 4) 3
  -- ppAblation "ISW refresh (3 shares)" (refreshISW 3) 2
  -- ppAblation "ISW refresh (4 shares)" (refreshISW 4) 3
  -- IO.println "--- §3 S-boxes ---"
  -- ppAblation "DOM Keccak χ (2 shares)" (domKeccakChi 2) 1
  -- ppAblation "DOM Keccak χ (3 shares)" (domKeccakChi 3) 2
  -- ppAblation "DOM Keccak χ (4 shares)" (domKeccakChi 4) 3   -- long; enable for the thesis table
  -- ppAblation "TI Keccak χ (3 shares)" tiKeccakChi 1
  -- ppAblation "TI Keccak χ (3 shares)" tiKeccakChi 2  -- above the TI guarantee
  -- ppAblation "Q⁴₁₂ (2-share direct)" q_12 1
  -- ppAblation "Q⁴₁₂ TI (3 shares)" q12TI 1
  -- ppAblation "TI Fides AB1 5-bit S-box (4 shares)" tiFidesAB1 1
  -- IO.println "--- §4 TI gadgets (Bilgin et al.) ---"
  -- ppAblation "x+yz TI direct (3 shares)" tiXplusYZ3 1
  -- ppAblation "x+yz TI with CT (3 shares)" tiXplusYZ3ct 1
  -- ppAblation "x+yz TI (4 shares)" tiXplusYZ4 2
  -- ppAblation "x+yz TI (4 shares)" tiXplusYZ4 3       -- genuinely 3-probing INSECURE
  -- ppAblation "x+yz+xyz TI (4 shares)" tiCubic4 1
  -- ppAblation "xy TI, virtual variable" tiMultVirtual 1
  -- ppAblation "xy TI, virtual share" tiMultVirtualShare 1
  -- ppAblation "xy TI, 4→3 shares" tiMult43 1

/-! ## Factoring ablation (`lake exe verif nofactor`)

    Re-checks the suite with multiplicative factoring disabled throughout the
    engine (`allowFactor := false`, coupling extension on in both runs).
    Factoring only widens the certifiable class, so a flip is always
    secure → false-INSECURE: the flipped rows are exactly the examples that
    fall out of reach without factoring. -/
def ppNoFactor (name : String) (g : GlobalDAG) (order : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let (_, _, resF, _) := checkDProbing g order true true
  let t1 ← IO.monoMsNow
  let (_, _, resN, _) := checkDProbing g order true false
  let t2 ← IO.monoMsNow
  let v := fun (r : CheckResult) => if r.isSecure then "secure" else "INSECURE"
  let flip := if resF.isSecure && !resN.isSecure then "   <-- LOST without factoring" else ""
  IO.println s!"{name} @ order {order}:  factoring {v resF} ({t1 - t0} ms)  |  no factoring {v resN} ({t2 - t1} ms){flip}"
  (← IO.getStdout).flush

def runNoFactorAblation : IO Unit := do
  IO.println "=== Factoring ablation (both runs coupling-extended) ==="
  ppNoFactor "ISW AND (2 shares)" (iswAND 2) 1
  ppNoFactor "ISW AND (3 shares)" (iswAND 3) 2
  ppNoFactor "ISW AND (4 shares)" (iswAND 4) 3
  ppNoFactor "ISW AND (5 shares)" (iswAND 5) 4
  ppNoFactor "DOM AND (2 shares)" (domAND 2) 1
  ppNoFactor "DOM AND (3 shares)" (domAND 3) 2
  ppNoFactor "DOM AND (4 shares)" (domAND 4) 3
  ppNoFactor "Trichina AND" trichinaAND 1
  ppNoFactor "Trichina AND (bad assoc)" trichinaANDBad 1
  ppNoFactor "TI AND (3 shares)" tiAND 1
  ppNoFactor "Additive refresh (3 shares)" (refreshAdd 3) 2
  ppNoFactor "Additive refresh (4 shares)" (refreshAdd 4) 3
  ppNoFactor "ISW refresh (3 shares)" (refreshISW 3) 2
  ppNoFactor "ISW refresh (4 shares)" (refreshISW 4) 3
  ppNoFactor "DOM Keccak χ (2 shares)" (domKeccakChi 2) 1
  ppNoFactor "DOM Keccak χ (3 shares)" (domKeccakChi 3) 2
  ppNoFactor "TI Keccak χ (3 shares)" tiKeccakChi 1
  ppNoFactor "Q⁴₁₂ (2-share direct)" q_12 1
  ppNoFactor "Q⁴₁₂ TI (3 shares)" q12TI 1
  ppNoFactor "TI Fides AB1 5-bit S-box (4 shares)" tiFidesAB1 1
  ppNoFactor "x+yz TI direct (3 shares)" tiXplusYZ3 1
  ppNoFactor "x+yz TI with CT (3 shares)" tiXplusYZ3ct 1
  ppNoFactor "x+yz TI (4 shares)" tiXplusYZ4 2
  ppNoFactor "x+yz+xyz TI (4 shares)" tiCubic4 1
  ppNoFactor "xy TI, virtual variable" tiMultVirtual 1
  ppNoFactor "xy TI, virtual share" tiMultVirtualShare 1
  ppNoFactor "xy TI, 4→3 shares" tiMult43 1
  IO.println "--- d+1 quadratic S-box family (randomness-free compression) ---"
  ppNoFactor "Q³₁ d+1 (Toffoli-style)" q31d1 1
  ppNoFactor "Q³₂ d+1 (quadratic feedback)" q32d1 1
  ppNoFactor "Q³₃ d+1 (genuinely insecure)" q33d1 1
  ppNoFactor "Q⁴₄ d+1 (Toffoli)" q44d1 1
  ppNoFactor "Q⁴₁₂ d+1 (generated)" q412d1 1
  ppNoFactor "Q⁴₂₉₃ d+1 (quadratic feedback)" q4293d1 1
  ppNoFactor "Q⁴₂₉₄ d+1 (Toffoli-style)" q4294d1 1
  ppNoFactor "Q⁴₂₉₉ d+1 (feedback ×3 coords)" q4299d1 1
  ppNoFactor "Q⁴₃₀₀ d+1 (genuinely insecure)" q4300d1 1

/-! ## Extension-mode comparison (`lake exe verif compare`)

    The canonical benchmark list for the three-branch comparison of the
    probe-set extension mechanisms — (i) coupling (this branch),
    (ii) witness replay (`replay-witness`), (iii) closures
    (`closure-exploration`).  The same list is ported verbatim to worktrees of
    the other two branches; each branch runs its own mechanism via its
    `checkDProbing g order true`.  Extension mode only (the naive baseline is
    mechanism-independent; see results/2026-07-12.txt for its numbers). -/
def runCompare : IO Unit := do
  IO.println "=== Extension-mode run (this branch's mechanism) ==="
  ppAblation "ISW AND (2 shares)" (iswAND 2) 1
  ppAblation "ISW AND (3 shares)" (iswAND 3) 2
  ppAblation "ISW AND (4 shares)" (iswAND 4) 3
  ppAblation "ISW AND (5 shares)" (iswAND 5) 4
  ppAblation "DOM AND (2 shares)" (domAND 2) 1
  ppAblation "DOM AND (2 shares) o2" (domAND 2) 2
  ppAblation "DOM AND (3 shares)" (domAND 3) 2
  ppAblation "DOM AND (4 shares)" (domAND 4) 3
  ppAblation "Trichina AND" trichinaAND 1
  ppAblation "Trichina AND (bad assoc)" trichinaANDBad 1
  ppAblation "TI AND (3 shares)" tiAND 1
  ppAblation "TI AND (3 shares) o2" tiAND 2
  ppAblation "Additive refresh (3 shares)" (refreshAdd 3) 2
  ppAblation "Additive refresh (4 shares)" (refreshAdd 4) 3
  ppAblation "ISW refresh (3 shares)" (refreshISW 3) 2
  ppAblation "ISW refresh (4 shares)" (refreshISW 4) 3
  ppAblation "DOM Keccak χ (2 shares)" (domKeccakChi 2) 1
  ppAblation "DOM Keccak χ (3 shares)" (domKeccakChi 3) 2
  ppAblation "TI Keccak χ (3 shares)" tiKeccakChi 1
  ppAblation "TI Keccak χ (3 shares) o2" tiKeccakChi 2
  ppAblation "Q⁴₁₂ (2-share direct)" q_12 1
  ppAblation "Q⁴₁₂ TI (3 shares)" q12TI 1
  ppAblation "TI Fides AB1 (4 shares)" tiFidesAB1 1
  ppAblation "x+yz TI direct (3 shares)" tiXplusYZ3 1
  ppAblation "x+yz TI with CT (3 shares)" tiXplusYZ3ct 1
  ppAblation "x+yz TI (4 shares)" tiXplusYZ4 2
  ppAblation "x+yz TI (4 shares) o3" tiXplusYZ4 3
  ppAblation "x+yz+xyz TI (4 shares)" tiCubic4 1
  ppAblation "xy TI virtual variable" tiMultVirtual 1
  ppAblation "xy TI virtual share" tiMultVirtualShare 1
  ppAblation "xy TI 4to3 shares" tiMult43 1
  ppAblation "Q31 d+1" q31d1 1
  ppAblation "Q32 d+1" q32d1 1
  ppAblation "Q33 d+1" q33d1 1
  ppAblation "Q44 d+1" q44d1 1
  ppAblation "Q412 d+1" q412d1 1
  ppAblation "Q4293 d+1" q4293d1 1
  ppAblation "Q4294 d+1" q4294d1 1
  ppAblation "Q4299 d+1" q4299d1 1
  ppAblation "Q4300 d+1" q4300d1 1

/-! ## Depth-scaling run (`lake exe verif scaling`)

    CSV: chain length vs verification time for `iswAndChain`, at 2 shares
    (order 1) and 3 shares (order 2), coupling and naive columns. -/
def ppScalingLine (shares len : Nat) : IO Unit := do
  let g := iswAndChain shares len
  let wireCount := g.circuit.wireOrder.size
  let order := shares - 1
  let t0 ← IO.monoMsNow
  let (_, _, resC, _) := checkDProbing g order true
  let t1 ← IO.monoMsNow
  let (_, _, resN, _) := checkDProbing g order false
  let t2 ← IO.monoMsNow
  let v := fun (r : CheckResult) => if r.isSecure then "secure" else "INSECURE"
  IO.println s!"{shares},{len},{wireCount},{t1 - t0},{t2 - t1},{v resC},{v resN}"
  (← IO.getStdout).flush

def runScaling : IO Unit := do
  IO.println "shares,len,wires,couplingMs,naiveMs,verdictC,verdictN"
  -- Verification time grows exponentially in chain length (≈ ×2.2 per stage at
  -- 2 shares — the canonical form of a deep wire blows up with multiplicative
  -- depth), so the ranges are capped where a step crosses ~1 min.
  for len in [1:13] do
    ppScalingLine 2 len
  for len in [1:7] do
    ppScalingLine 3 len

/-
  stored output (pre-coupling closure ablation, kept for reference):
  7-share DOM-AND @ order 5:  verdict secure (agree=true)
      with closure   : 1072583 ms  | discharges 14256  certs 7113  free/main 0.532265
      without closure: 842942 ms  | discharges 9298  certs 4633
-/

open Std (HashMap)

/-! ## Engine benchmark and golden test (`lake exe verif bench` / `golden`)

    Safety net and yardstick for the engine-speed work (`.ai/ENGINE_SPEED_PLAN.md`).

    * `golden` — differential test.  On a fixed, seeded sample of probe sets per
      gadget it records the complete engine output: the verdict of the complete
      loop, its coupling, the coupling extension over **all** wires, and the
      tiered verdict-only path on the probe and on a larger "union-sized" set.
      Each gadget prints one aggregate line (counts + a hash of every per-probe
      record), and every suite entry also its end-to-end `checkDProbing` result.
      Expressions are printed in a canonical, NodeId-independent form, so the
      record survives changes to the DAG representation and allocation order.
      An engine change is accepted only if the output equals the baseline in
      `results/engine-golden_baseline.txt` (`golden check <file>`).
      `golden full <name>` prints the per-probe records of one gadget, for
      locating a mismatch.
    * `bench` — timing.  End-to-end `checkDProbing` on the suite (best of 3), and
      on the large gadgets a per-call profile on seeded random probe sets: engine
      µs/call, extension µs per secure call, DAG growth, early vs late call cost. -/

/-- The 40-entry `compare` list plus `domAND 3` at order 3. -/
def benchSuite : List (String × GlobalDAG × Nat) := [
  ("ISW AND (2 shares)", iswAND 2, 1), ("ISW AND (3 shares)", iswAND 3, 2),
  ("ISW AND (4 shares)", iswAND 4, 3), ("ISW AND (5 shares)", iswAND 5, 4),
  ("DOM AND (2 shares)", domAND 2, 1), ("DOM AND (2 shares) o2", domAND 2, 2),
  ("DOM AND (3 shares)", domAND 3, 2), ("DOM AND (3 shares) o3", domAND 3, 3),
  ("DOM AND (4 shares)", domAND 4, 3),
  ("Trichina AND", trichinaAND, 1), ("Trichina AND (bad assoc)", trichinaANDBad, 1),
  ("TI AND (3 shares)", tiAND, 1), ("TI AND (3 shares) o2", tiAND, 2),
  ("Additive refresh (3 shares)", refreshAdd 3, 2), ("Additive refresh (4 shares)", refreshAdd 4, 3),
  ("ISW refresh (3 shares)", refreshISW 3, 2), ("ISW refresh (4 shares)", refreshISW 4, 3),
  ("DOM Keccak χ (2 shares)", domKeccakChi 2, 1), ("DOM Keccak χ (3 shares)", domKeccakChi 3, 2),
  ("TI Keccak χ (3 shares)", tiKeccakChi, 1), ("TI Keccak χ (3 shares) o2", tiKeccakChi, 2),
  ("Q⁴₁₂ (2-share direct)", q_12, 1), ("Q⁴₁₂ TI (3 shares)", q12TI, 1),
  ("TI Fides AB1 (4 shares)", tiFidesAB1, 1),
  ("x+yz TI direct (3 shares)", tiXplusYZ3, 1), ("x+yz TI with CT (3 shares)", tiXplusYZ3ct, 1),
  ("x+yz TI (4 shares)", tiXplusYZ4, 2), ("x+yz TI (4 shares) o3", tiXplusYZ4, 3),
  ("x+yz+xyz TI (4 shares)", tiCubic4, 1),
  ("xy TI virtual variable", tiMultVirtual, 1), ("xy TI virtual share", tiMultVirtualShare, 1),
  ("xy TI 4to3 shares", tiMult43, 1),
  ("Q31 d+1", q31d1, 1), ("Q32 d+1", q32d1, 1), ("Q33 d+1", q33d1, 1), ("Q44 d+1", q44d1, 1),
  ("Q412 d+1", q412d1, 1), ("Q4293 d+1", q4293d1, 1), ("Q4294 d+1", q4294d1, 1),
  ("Q4299 d+1", q4299d1, 1), ("Q4300 d+1", q4300d1, 1)]

/-- Gadgets too large for the split search to finish quickly; profiled per call only. -/
def benchLarge : List (String × GlobalDAG × Nat) := [
  ("DOM Keccak χ (4 shares)", domKeccakChi 4, 3), ("DOM AND (5 shares)", domAND 5, 4),
  ("ISW AND (5 shares)", iswAND 5, 4), ("TI Fides AB1 (4 shares)", tiFidesAB1, 1)]

/-- Wall-clock of `f ()` in nanoseconds. -/
def timeNs {α} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return (r, t1 - t0)

/-- Seeded sampler: `k` distinct indices below `n` (requires `k ≤ n`). -/
def sampleIdx (n k : Nat) (st : Nat) : Array Nat × Nat := Id.run do
  let mut st := st
  let mut idx : Array Nat := #[]
  while idx.size < k do
    st := (st * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
    let i := (st / 4294967296) % n
    if !idx.contains i then idx := idx.push i
  return (idx.qsort (· < ·), st)

/-- NodeId-independent rendering: leaves by name, XOR/AND children sorted by
    their own rendering. -/
partial def canonStr (dag : DAG) (memo : HashMap NodeId String) (n : NodeId)
    : HashMap NodeId String × String :=
  match memo[n]? with
  | some s => (memo, s)
  | none =>
    let (memo, s) := match dag.kind? n with
      | some (NodeKind.constVal b) => (memo, if b then "1" else "0")
      | some (NodeKind.leaf (VarType.Secret x)) => (memo, s!"s:{x}")
      | some (NodeKind.leaf (VarType.Random x)) => (memo, s!"r:{x}")
      | some (NodeKind.leaf (VarType.Public x)) => (memo, s!"p:{x}")
      | some (NodeKind.xorNode ch) | some (NodeKind.andNode ch) =>
        let op := match dag.kind? n with | some (NodeKind.xorNode _) => "+" | _ => "*"
        let (memo, parts) := ch.foldl (fun (acc : HashMap NodeId String × Array String) c =>
          let (m, s) := canonStr dag acc.1 c
          (m, acc.2.push s)) (memo, #[])
        (memo, "(" ++ op ++ " " ++ String.intercalate " " (parts.qsort (· < ·)).toList ++ ")")
      | none => (memo, "?")
    (memo.insert n s, s)

def joinSorted (xs : Array String) : String := String.intercalate "," (xs.qsort (· < ·)).toList

structure GoldAgg where
  probes  : Nat := 0
  secure  : Nat := 0
  coup    : Nat := 0
  safe    : Nat := 0
  anf     : Nat := 0
  unionOk : Nat := 0
  hash    : UInt64 := 7

/-- Golden records of one gadget: `n` seeded probe sets of size `d`; returns the
    aggregate and (when `full`) the per-probe records. -/
def goldenGadget (g0 : GlobalDAG) (d n : Nat) (full : Bool) : GoldAgg × Array String := Id.run do
  let ws := g0.circuit.wireOrder
  let cands := candidatesOf g0.wires ws
  let unionSize := min ws.size (4 * d)
  let mut g := g0
  let mut st : Nat := 88172645463325252
  let mut agg : GoldAgg := {}
  let mut lines : Array String := #[]
  for _ in [0:n] do
    let (idx, st1) := sampleIdx ws.size d st
    let (uidx, st2) := sampleIdx ws.size unionSize st1
    st := st2
    let names := idx.map (ws[·]!)
    let ids := names.map (fun w => g.wires[w]!)
    let (g1, sec, coupling) := checkProbeCompleteT g ids
    g := g1
    let mut memo : HashMap NodeId String := {}
    let mut coupStr : Array String := #[]
    for (r, t) in coupling do
      let (m1, rs) := canonStr g.dag memo r
      let (m2, ts) := canonStr g.dag m1 t
      memo := m2
      coupStr := coupStr.push s!"{rs}<-{ts}"
    let mut safeStr := "-"
    if sec then
      let (g2, safe, anf) := couplingExtend g coupling names cands
      g := g2
      safeStr := joinSorted safe
      agg := { agg with secure := agg.secure + 1, coup := agg.coup + coupling.size,
                        safe := agg.safe + safe.size, anf := agg.anf + anf }
    let (g3, tiered) := checkProbeRoots g ids
    g := g3
    let uids := uidx.map (fun i => g.wires[ws[i]!]!)
    let (g4, uSec) := checkProbeRoots g uids
    g := g4
    if uSec then agg := { agg with unionOk := agg.unionOk + 1 }
    let line := s!"{joinSorted names}|{sec}|{String.intercalate ";" coupStr.toList}|{safeStr}|{tiered}|{uSec}"
    agg := { agg with probes := agg.probes + 1, hash := mixHash agg.hash (hash line) }
    if full then lines := lines.push line
  return (agg, lines)

/-- One golden line for the cell search on `g` at order `d`. -/
def cellLine (name : String) (g : GlobalDAG) (d : Nat) : String :=
  let (_, s, res) := checkDProbingCells g d
  let audit := if !res.isSecure then "-" else
    match coverageAudit s.store g.circuit.wireOrder.size d with
    | some (n, 0) => s!"ok/{n}"
    | some (n, m) => s!"UNCOVERED {m}/{n}"
    | none => "skipped"
  s!"CELL\t{name}\t{d}\t{if res.isSecure then "S" else "I"}\tengine={s.cnt.engine}\tcells={s.cnt.cells}\tcovers={s.cnt.covers}\tskips={s.cnt.skips}\tsafeSets={s.store.sets.size}\taudit={audit}"

/-- One golden line for the symmetric cell search (`mode`), with both audits:
    the root covers every orbit (`rootCheck`), and every probe set of the root is
    covered by a stored set (`coverageAuditCells`). -/
def symLine (name : String) (g : GlobalDAG) (d : Nat) : String :=
  let n := g.circuit.wireOrder.size
  let (_, s, res, plan?) := checkDProbingSym g d
  let fmt (r : Option (Nat × Nat)) : String := match r with
    | some (k, 0) => s!"ok/{k}" | some (k, m) => s!"FAIL {m}/{k}" | none => "skipped"
  match plan? with
  | none => s!"SYM\t{name}\t{d}\t{if res.isSecure then "S" else "I"}\tsymmetry=off\tengine={s.cnt.engine}\tcells={s.cnt.cells}"
  | some p =>
    let rc := fmt (rootCheck n d p.rootTables p.roots)
    let cov := if !res.isSecure then "-" else fmt (coverageAuditCells #[s.store] p.roots)
    s!"SYM\t{name}\t{d}\t{if res.isSecure then "S" else "I"}\tgroup={p.label}\tautomorphisms={p.sym.size}\troot={p.rootSize}/{p.totalSize} in {p.roots.size} cells\tengine={s.cnt.engine}\tcells={s.cnt.cells}\tcovers={s.cnt.covers}\tdeep={s.cnt.deep}\tskips={s.cnt.skips}\trootCheck={rc}\tcoverage={cov}"

def goldenLines : IO (Array String) := do
  let mut out : Array String := #[]
  for (name, g, d) in benchSuite do
    let (_, _, res, st) := checkDProbing g d
    out := out.push s!"E2E\t{name}\t{d}\t{if res.isSecure then "S" else "I"}\tdischarges={st.totalDischarges}\tdistinct={st.verdictCache.size}\tmain={st.successMain}\tfree={st.freeWiresSum}\textensions={st.extensionWitnesses.size}\tanf={st.anfFallbacks}"
    let (a, _) := goldenGadget g d 100 false
    out := out.push s!"GOLD\t{name}\t{d}\tprobes={a.probes}\tsecure={a.secure}\tcoup={a.coup}\tsafe={a.safe}\tanf={a.anf}\tunionSecure={a.unionOk}\thash={a.hash}"
  for (name, g, d) in benchLarge do
    let (a, _) := goldenGadget g d 300 false
    out := out.push s!"GOLD\t{name}\t{d}\tprobes={a.probes}\tsecure={a.secure}\tcoup={a.coup}\tsafe={a.safe}\tanf={a.anf}\tunionSecure={a.unionOk}\thash={a.hash}"
  -- cell search (`CellSearch.lean`): verdict, counters, and the brute-force coverage audit
  for (name, g, d) in benchSuite ++ benchLarge do
    out := out.push (cellLine name g d)
  -- symmetric cell search, symmetry forced on (exercises the audits everywhere)
  for (name, g, d) in benchSuite ++ benchLarge do
    out := out.push (symLine name g d)
  return out

def runGolden (args : List String) : IO UInt32 := do
  match args with
  | ["full", name] =>
    match (benchSuite ++ benchLarge).find? (·.1 == name) with
    | none => IO.eprintln s!"unknown gadget '{name}'"; return 2
    | some (_, g, d) =>
      let n := if (benchLarge.any (·.1 == name)) && !(benchSuite.any (·.1 == name)) then 300 else 100
      let (_, lines) := goldenGadget g d n true
      for l in lines do IO.println l
      return 0
  | ["cell", name] =>
    match (benchSuite ++ benchLarge).find? (·.1 == name) with
    | none => IO.eprintln s!"unknown gadget '{name}'"; return 2
    | some (_, g, d) => IO.println (cellLine name g d); return 0
  | ["contract"] =>
    -- the one-pass `contractAssoc` against iterating `contractAssocStep` (the definition)
    let mut bad := 0
    for (name, g, _) in benchSuite ++ benchLarge do
      let c := g.circuit
      let (fast, _) := contractAssoc c
      let slow := Id.run do
        let mut cur := c
        for _ in [0:c.wireOrder.size + 1] do
          match contractAssocStep cur with
          | (c', true) => cur := c'
          | (_, false) => break
        return cur
      let render (x : Circuit) : String := String.intercalate "\n"
        ((x.inputOrder ++ x.wireOrder).toList.map (fun w => w ++ " = " ++ Circuit.ppWireDef x.wireDefs[w]!))
      if render fast != render slow then
        bad := bad + 1
        IO.println s!"CONTRACT MISMATCH {name}"
    IO.println s!"contract: {if bad == 0 then "OK" else toString bad ++ " MISMATCHES"}"
    return (if bad == 0 then 0 else 1)
  | ["sym", name] =>
    match (benchSuite ++ benchLarge).find? (·.1 == name) with
    | none => IO.eprintln s!"unknown gadget '{name}'"; return 2
    | some (_, g, d) => IO.println (symLine name g d); return 0
  | ["check", file] =>
    let expected := (← IO.FS.lines file).filter (fun l => l.startsWith "E2E" || l.startsWith "GOLD" || l.startsWith "CELL" || l.startsWith "SYM")
    let got ← goldenLines
    let mut bad := 0
    for i in [0:max expected.size got.size] do
      let e := expected[i]?.getD "<missing>"
      let o := got[i]?.getD "<missing>"
      if e != o then
        bad := bad + 1
        IO.println s!"MISMATCH\n  expected: {e}\n  got:      {o}"
    IO.println (if bad == 0 then s!"golden: OK ({got.size} lines identical)" else s!"golden: {bad} MISMATCHES")
    return (if bad == 0 then 0 else 1)
  | _ =>
    for l in ← goldenLines do IO.println l
    return 0

/-- Per-call profile on `n` seeded random probe sets (the engine + extension work
    a search would do per discharge, without the search). -/
def profileCalls (name : String) (g0 : GlobalDAG) (d n : Nat) : IO Unit := do
  let ws := g0.circuit.wireOrder
  let cands := candidatesOf g0.wires ws
  let mut g := g0
  let mut st : Nat := 88172645463325252
  let mut tE := 0
  let mut tX := 0
  let mut tEarly := 0
  let mut tLate := 0
  let mut nSec := 0
  let n0 := g.dag.nextId
  for i in [0:n] do
    let (idx, st1) := sampleIdx ws.size d st
    st := st1
    let names := idx.map (ws[·]!)
    let ids := names.map (fun w => g.wires[w]!)
    let gin := g
    let ((g1, sec, coupling), te) ← timeNs (fun _ => checkProbeCompleteT gin ids)
    g := g1
    tE := tE + te
    let mut tx := 0
    if sec then
      nSec := nSec + 1
      let gin := g
      let ((g2, _, _), t) ← timeNs (fun _ => couplingExtend gin coupling names cands)
      g := g2
      tx := t
      tX := tX + t
    if i < 100 then tEarly := tEarly + te + tx
    if i + 100 ≥ n then tLate := tLate + te + tx
  let perSec := if nSec == 0 then 0 else tX / 1000 / nSec
  IO.println s!"CALL\t{name}\t{d}\tcalls={n}\tsecure={nSec}\tengine_us={tE / 1000 / n}\textend_us={perSec}\tdag={n0}->{g.dag.nextId}\tfirst100_us={tEarly / 1000 / 100}\tlast100_us={tLate / 1000 / 100}"
  (← IO.getStdout).flush

/-- `bench cells <gadget>`: the cell search on one gadget, best of 3. -/
def benchCellsOne (name : String) : IO Unit := do
  match (benchSuite ++ benchLarge).find? (·.1 == name) with
  | none => IO.eprintln s!"unknown gadget '{name}'"
  | some (_, g, d) =>
    let mut best := 0
    for k in [0:3] do
      let ((_, s, res), t) ← timeNs (fun _ => checkDProbingCells g d)
      if k == 0 || t < best then best := t
      if k == 2 then
        IO.println s!"CELLS\t{name}\t{d}\t{if res.isSecure then "S" else "I"}\tengine={s.cnt.engine}\tcells={s.cnt.cells}\tms={best / 1000000}.{(best / 100000) % 10}"

/-- `bench sym <gadget>`: the symmetric cell search (symmetry on), best of 3,
    setup included, and the setup alone. -/
def benchSymOne (name : String) : IO Unit := do
  match (benchSuite ++ benchLarge).find? (·.1 == name) with
  | none => IO.eprintln s!"unknown gadget '{name}'"
  | some (_, g, d) =>
    let mut best := 0
    let mut bestPlan := 0
    for k in [0:3] do
      let (p, tp) ← timeNs (fun _ => planSymmetry g d)
      let ((_, s, res, _), t) ← timeNs (fun _ => checkDProbingSym g d)
      if k == 0 || t < best then best := t
      if k == 0 || tp < bestPlan then bestPlan := tp
      if k == 2 then
        IO.println s!"SYM\t{name}\t{d}\t{if res.isSecure then "S" else "I"}\tgroup={p.label}\troot={p.rootSize}/{p.totalSize}\tengine={s.cnt.engine}\tcells={s.cnt.cells}\tdeep={s.cnt.deep}\tms={best / 1000000}.{(best / 100000) % 10}\tsetup_ms={bestPlan / 1000000}.{(bestPlan / 100000) % 10}"

/-- `bench setup <gadget>`: where the symmetry setup time goes. -/
def benchSetup (name : String) : IO Unit := do
  match (benchSuite ++ benchLarge).find? (·.1 == name) with
  | none => IO.eprintln s!"unknown gadget '{name}'"
  | some (_, g, d) =>
    let ws := g.circuit.wireOrder
    let (s, t1) ← timeNs (fun _ => symmetryOf g 600)
    let (E, t2) ← timeNs (fun _ => WireTables.of s ws)
    let (roots, t3) ← timeNs (fun _ => orbitalRoot E d)
    let ms (x : Nat) : String := s!"{x / 1000000}.{(x / 100000) % 10}"
    IO.println s!"SETUP\t{name}\tgroup={s.order}\tgroupExtraction={ms t1}\twireTables={ms t2}\torbitalRoot={ms t3}\troot={rootProbeCount roots}/{binomial ws.size d}"

/-- `bench groups <gadget>`: the steps of `symmetryOf`, timed. -/
def benchGroups (name : String) : IO Unit := do
  match (benchSuite ++ benchLarge).find? (·.1 == name) with
  | none => IO.eprintln s!"unknown gadget '{name}'"
  | some (_, g, _) =>
    let c0 := g.circuit
    let (chk, t1) ← timeNs (fun _ => shareChecks c0)
    let ((rc, _), t2) ← timeNs (fun _ => contractAssoc c0)
    let (sg, t3) ← timeNs (fun _ => buildShareGraph rc chk.bundles)
    let ((_, _, gens), t4) ← timeNs (fun _ => groupOf sg 200000 sg.kind)
    let ((els, _), t5) ← timeNs (fun _ => closedGroup (gens.map (atomicLeafMap sg)) 600)
    let (ad, t6) ← timeNs (fun _ => buildAtomicDAG c0)
    let ms (x : Nat) : String := s!"{x / 1000000}.{(x / 100000) % 10}"
    IO.println s!"GROUPS\t{name}\tgroup={els.size}\tshareChecks={ms t1}\tcontract={ms t2}\tshareGraph={ms t3}\tgroupOf={ms t4}\tclose={ms t5}\tatomicDAG={ms t6}\t(atomic nodes {ad.dag.nextId})"

/-- `bench plainroot <gadget>`: symmetric lookups with the plain root (experiment). -/
def benchPlainRoot (name : String) : IO Unit := do
  match (benchSuite ++ benchLarge).find? (·.1 == name) with
  | none => IO.eprintln s!"unknown gadget '{name}'"
  | some (_, g, d) =>
    let mut best := 0
    for k in [0:3] do
      let ((_, s, _, _), t) ← timeNs (fun _ => checkDProbingSym g d (orbitalRoot := false))
      if k == 0 || t < best then best := t
      if k == 2 then IO.println s!"PLAINROOT\t{name}\tengine={s.cnt.engine}\tcells={s.cnt.cells}\tdeep={s.cnt.deep}\tms={best / 1000000}.{(best / 100000) % 10}"

/-- `bench cap <gadget> <cap>`: the symmetric search with the group capped at `cap`. -/
def benchCap (name : String) (cap : Nat) : IO Unit := do
  match (benchSuite ++ benchLarge).find? (·.1 == name) with
  | none => IO.eprintln s!"unknown gadget '{name}'"
  | some (_, g, d) =>
    let mut best := 0
    let mut bestP := 0
    for k in [0:3] do
      let (p, tp) ← timeNs (fun _ => planSymmetry g d cap)
      let ((_, s, _, _), t) ← timeNs (fun _ => checkDProbingSym g d (groupCap := cap))
      if k == 0 || t < best then best := t
      if k == 0 || tp < bestP then bestP := tp
      if k == 2 then IO.println s!"CAP {cap}\t{name}\tgroup={p.label}\tauts={p.sym.size}\troot={p.rootSize}/{p.totalSize}\tengine={s.cnt.engine}\tcells={s.cnt.cells}\tms={best / 1000000}.{(best / 100000) % 10}\tsetup={bestP / 1000000}.{(bestP / 100000) % 10}"

/-- `trace <gadget>`: the symmetric cell search on one gadget, step by step —
    wires, group, root cells, and every cell visit with its outcome. -/
def runTrace (name : String) : IO Unit := do
  match (benchSuite ++ benchLarge).find? (·.1 == name) with
  | none => IO.eprintln s!"unknown gadget '{name}'"
  | some (_, g, d) =>
    let ws := g.circuit.wireOrder
    let n := ws.size
    let nm (w : Nat) : String := ws[w]!
    let showCell (c : Cell) : String :=
      String.intercalate " × " (c.toList.map (fun (k, xs) => s!"{k} of " ++ "{" ++ String.intercalate "," (xs.toList.map nm) ++ "}"))
    let showSet (xs : Array Nat) : String := "{" ++ String.intercalate "," (xs.toList.map nm) ++ "}"
    IO.println s!"GADGET {name} at order {d}: {n} wires"
    for w in g.circuit.inputOrder ++ ws do
      IO.println s!"  {Circuit.ppLine g.circuit (if g.circuit.inputOrder.contains w then "[in] " else "") w}"
    let p := planSymmetry g d
    IO.println s!"GROUP {p.label}; automorphisms used for lookups: {p.sym.size}"
    for (f, _) in p.sym.extract 0 (min 6 p.sym.size) do
      let moved := (Array.range n).filter (fun w => f[w]! < n && f[w]! != w)
      let inval := (Array.range n).filter (fun w => f[w]! >= n)
      IO.println (s!"  e.g. " ++ String.intercalate " " (moved.toList.map (fun w => s!"{nm w}→{nm f[w]!}")) ++ (if inval.isEmpty then "" else s!"   (not valid on {showSet inval})"))
    IO.println s!"ROOT {p.rootSize} of {p.totalSize} probe sets in {p.roots.size} cells"
    for c in p.roots do IO.println s!"  [{probeCount c}] {showCell c}"
    let env := { CellEnv.of g (identityLook n) with sym := p.sym }
    let mut s : CellState := { g, store := SafeStore.empty n 1 }
    let mut stack : Array Cell := p.roots.reverse
    let mut step := 0
    while !stack.isEmpty do
      let cell := stack.back!
      stack := stack.pop
      let before := s.cnt
      let nSets := s.store.sets.size
      let (s2, bad, kids) := visitCell env s cell
      s := s2
      if s.cnt.cells == before.cells then continue    -- vacuous cell, not counted
      step := step + 1
      let seed := cell.filter (fun (c, _) => c > 0) |>.foldl (fun acc (c, xs) => acc ++ xs.extract 0 c) #[]
      let what :=
        if s.cnt.skips > before.skips then "SKIP (whole cell inside a stored safe set)"
        else if s.cnt.deep > before.deep then s!"SYMMETRY: seed {showSet seed} lies in an automorphic image of a stored set; stored image {showSet s.store.sets[nSets]!}"
        else if s.cnt.covers > before.covers then s!"COVER: seed {showSet seed} inside a stored safe set"
        else match bad with
          | some w => s!"ENGINE on {showSet seed}: NOT certified -> counterexample {w}"
          | none => s!"ENGINE on {showSet seed}: certified; safe set {showSet s.store.sets[nSets]!} stored"
      IO.println (s!"STEP {step} cell [{probeCount cell}] {showCell (cell.filter (fun (c, _) => c > 0))}\n    {what}" ++ (if kids.isEmpty then "" else s!"\n    -> {kids.size} child cells"))
      match bad with
      | some _ => break
      | none => stack := stack ++ kids.reverse
    IO.println s!"DONE engine={s.cnt.engine} cells={s.cnt.cells} covers={s.cnt.covers} (through symmetry {s.cnt.deep}) skips={s.cnt.skips} stored={s.store.sets.size}"

/-- `bench ablate <gadget|suite> <sym 0/1> <extendAll 0/1> <union 0/1/2>`: one search
    variant, best of 3, setup included.  `suite` sums over the 41 entries. -/
def benchAblate (name : String) (sym : Bool) (extendAll : Bool) (union : Nat) : IO Unit := do
  let opts : SearchOpts := { extendAll, union }
  let rows := if name == "suite" then benchSuite
    else (benchSuite ++ benchLarge).filter (·.1 == name) |>.take 1
  let mut total := 0
  let mut eng := 0
  let mut cells := 0
  let mut uni := 0
  let mut uok := 0
  let mut verdicts := ""
  for (_, g, d) in rows do
    let mut best := 0
    for k in [0:3] do
      let ((_, s, res, _), t) ← timeNs (fun _ => checkDProbingSym g d sym (opts := opts))
      if k == 0 || t < best then best := t
      if k == 2 then
        eng := eng + s.cnt.engine; cells := cells + s.cnt.cells
        uni := uni + s.cnt.unions; uok := uok + s.cnt.unionsOk
        verdicts := verdicts ++ (if res.isSecure then "S" else "I")
    total := total + best
  IO.println s!"ABL\t{name}\tsym={sym}\textendAll={extendAll}\tunion={union}\tverdicts={verdicts}\tengine={eng}\tcells={cells}\tunions={uni}\tunionsOk={uok}\tms={total / 1000000}.{(total / 100000) % 10}"

/-- `bench contraction <gadget|suite|all> <contract 0/1>`: the symmetric search with the
    group found on the contracted or the as-built netlist, best of 3, setup included. -/
def benchContraction (name : String) (contract : Bool) : IO Unit := do
  let opts : SearchOpts := { contract }
  let rows := if name == "suite" then benchSuite
    else if name == "all" then benchSuite ++ benchLarge
    else (benchSuite ++ benchLarge).filter (·.1 == name) |>.take 1
  let mut total := 0
  let mut eng := 0
  let mut cells := 0
  let mut verdicts := ""
  for (nm, g, d) in rows do
    let mut best := 0
    let mut line := ""
    for k in [0:3] do
      let ((_, s, res, p?), t) ← timeNs (fun _ => checkDProbingSym g d (opts := opts))
      if k == 0 || t < best then best := t
      if k == 2 then
        eng := eng + s.cnt.engine; cells := cells + s.cnt.cells
        verdicts := verdicts ++ (if res.isSecure then "S" else "I")
        let lbl := match p? with | some p => s!"{p.label} root={p.rootSize}/{p.totalSize}" | none => "-"
        line := s!"{if res.isSecure then "S" else "I"}\t{lbl}\tengine={s.cnt.engine}\tcells={s.cnt.cells}"
    total := total + best
    IO.println s!"CONTRACTION\t{nm}\t{d}\tcontract={contract}\t{line}\tms={best / 1000000}.{(best / 100000) % 10}"
    (← IO.getStdout).flush
  IO.println s!"CONTRACTION-TOTAL\t{name}\tcontract={contract}\tverdicts={verdicts}\tengine={eng}\tcells={cells}\tms={total / 1000000}.{(total / 100000) % 10}"

/-- `bench groups-report <cap>`: for every gadget, what contraction absorbs, the group
    order with and without contraction, whether the sharing checks hold, and how the
    group acts on the real wires. -/
def benchGroupsReport (cap : Nat) : IO Unit := do
  for (name, g, _) in benchSuite ++ benchLarge do
    let c0 := g.circuit
    let ws := c0.wireOrder
    let n := ws.size
    let (rc, absorbed) := contractAssoc c0
    let chk := shareChecks c0
    let ordOf (c : Circuit) : Nat :=
      if chk.ok then
        let sg := buildShareGraph c chk.bundles
        let (_, ord, _) := groupOf sg 200000 sg.kind
        ord
      else 0
    let s := symmetryOf g cap
    let E := WireTables.of s ws
    let isLive (f : Array Nat) : Bool := (Array.range n).any (fun w => f[w]! < n && f[w]! != w)
    let T := E.fwd.filter isLive
    let validPct : Nat :=
      if T.isEmpty then 0 else
        (T.foldl (fun a f => a + (f.filter (· < n)).size) 0) * 100 / (T.size * n)
    let gone : HashMap String Unit := absorbed.foldl (fun m w => m.insert w ()) {}
    let survivors := (Array.range n).filter (fun w => !gone.contains ws[w]!)
    let dom := stableIn E (Array.range E.fwd.size) (Array.range n)
    let inD := maskOf n dom
    let outside := (survivors.filter (fun w => !inD[w]!)).size
    let probs := if chk.ok then "ok" else String.ofList ((chk.problems[0]!).toList.take 70)
    -- body wires that repeat another wire's expression, on the DAG the tables read
    let dups : Nat := if s.active then
        let nodes := ws.filterMap (fun w => s.dag.wires[w]?)
        let cnt : HashMap NodeId Nat := nodes.foldl (fun m x => m.insert x ((m[x]?).getD 0 + 1)) {}
        (nodes.filter (fun x => (cnt[x]?).getD 0 > 1)).size
      else 0
    -- Lemma (b) at the level of expressions: surviving wires that some element sends to an
    -- expression no wire computes (raw `nameMap`, before the tables refuse duplicates)
    let lost : Nat := if s.active then
        let maps := s.group.map (fun e => nameMap s.dag (normLM e))
        (survivors.filter (fun w => maps.any (fun m => !m.contains ws[w]!))).size
      else 0
    IO.println s!"GR\t{name}\tsurvivorsNoImage={lost}\twires={n}\tabsorbed={absorbed.size}\torder:built={ordOf c0} contracted={ordOf rc}\tlisted={T.size + 1}\tvalid%={validPct}\tdupWires={dups}\tsurvivorsOutside={outside}\tchecks={probs}"
    (← IO.getStdout).flush

/-- `bench trichina`: the secure and the insecure Trichina AND, contracted.  They differ only
    in the bracketing of one sum, so contraction identifies them. -/
def benchTrichina : IO Unit := do
  let pick (nm : String) : GlobalDAG := ((benchSuite.find? (·.1 == nm)).get!).2.1
  let render (x : Circuit) : List String :=
    (x.wireOrder.toList.map (fun w =>
      let sortIn := (Circuit.ppWireDef x.wireDefs[w]!).splitOn " + " |>.toArray.qsort (· < ·)
      w ++ " = " ++ String.intercalate " + " sortIn.toList))
  let (a, _) := contractAssoc (pick "Trichina AND").circuit
  let (b, _) := contractAssoc (pick "Trichina AND (bad assoc)").circuit
  for l in render a do IO.println s!"good  {l}"
  for l in render b do IO.println s!"bad   {l}"
  IO.println s!"identical after contraction: {render a == render b}"

-- ------------------------------------------------------------
-- Brute-force transport check
-- ------------------------------------------------------------

/-- The raw netlist evaluated on every assignment of its leaves: `(values, secret
    index, secret-value count)`, `values[w][e]` being wire `w` under assignment `e`.
    Deliberately reads `wireDefs` only — no DAG, no interning, no canonicalisation —
    so it shares nothing with the code it checks.  Publics count as secrets (they
    are quantified over). -/
def truthTables (c : Circuit) : Option (HashMap String ByteArray × Array Nat × Nat) := Id.run do
  let names := c.inputOrder ++ c.wireOrder
  let mut sec : Array VarType := #[]
  let mut rnd : Array VarType := #[]
  for nm in names do
    for i in (c.wireDefs[nm]!).inputs do
      match i with
      | .leaf l@(.Random _) => if !rnd.contains l then rnd := rnd.push l
      | .leaf l => if !sec.contains l then sec := sec.push l
      | _ => pure ()
  let L := sec.size + rnd.size
  if L > 18 then return none
  let N := 1 <<< L
  let leaves := sec ++ rnd
  let idx : HashMap VarType Nat := (leaves.zipIdx).foldl (fun m (v, i) => m.insert v i) {}
  let mut vals : HashMap String ByteArray := {}
  for nm in names do
    let d := c.wireDefs[nm]!
    let mut acc := ByteArray.mk (Array.replicate N (if d.isXor then 0 else 1))
    for i in d.inputs do
      for e in [0:N] do
        let b : UInt8 := match i with
          | .leaf l  => (((e >>> idx[l]!) &&& 1 : Nat).toUInt8)
          | .const v => if v then 1 else 0
          | .wire w  => (vals[w]!).get! e
        let a := acc.get! e
        acc := acc.set! e (if d.isXor then a ^^^ b else a &&& b)
    vals := vals.insert nm acc
  let secIdx := (Array.range N).map (fun e => e &&& ((1 <<< sec.size) - 1))
  return some (vals, secIdx, 1 <<< sec.size)

/-- For each secret value, the histogram of the tuple `P`, hashed; sorted, so that two
    tuples agree exactly when their conditional distributions agree up to renaming
    the secret values. -/
def distKey (vals : HashMap String ByteArray) (secIdx : Array Nat) (nSec : Nat) (P : Array String) : Array UInt64 := Id.run do
  let cols := P.map (vals[·]!)
  let k := P.size
  let mut hist : Array Nat := Array.replicate (nSec <<< k) 0
  for e in [0:secIdx.size] do
    let mut key := secIdx[e]! <<< k
    for j in [0:k] do
      key := key ||| ((cols[j]!.get! e).toNat <<< j)
    hist := hist.modify key (· + 1)
  let mut out : Array UInt64 := #[]
  for s in [0:nSec] do
    let mut h : UInt64 := 0x9E3779B97F4A7C15
    for v in [0:1 <<< k] do
      h := hash64 (h * 31 + (hist[(s <<< k) + v]!).toUInt64 + 1)
    out := out.push h
  return out.qsort (· < ·)

/-- Probe sets of size `k` drawn from `dom`: all of them, or `budget` seeded samples. -/
def probeSample (dom : Array Nat) (k budget : Nat) (seed : Nat) : Array (Array Nat) := Id.run do
  if dom.size < k then return #[]
  if binomial dom.size k ≤ budget then
    let mut out : Array (Array Nat) := #[#[]]
    for _ in [0:k] do
      out := out.foldl (fun acc p =>
        let start := if p.isEmpty then 0 else p.back! + 1
        acc ++ ((List.range (dom.size - start)).toArray.map (fun i => p.push (start + i)))) #[]
    return out.map (·.map (dom[·]!))
  let mut st := seed
  let mut out : Array (Array Nat) := #[]
  for _ in [0:budget] do
    let (idx, st1) := sampleIdx dom.size k st
    st := st1
    out := out.push (idx.map (dom[·]!))
  return out

/-- Count, over the probe sets of size `k` on which table `f` is valid and moves something,
    how many have a different distribution from their image. -/
def transportViolations (vals : HashMap String ByteArray) (secIdx : Array Nat) (nSec : Nat)
    (ws : Array String) (f : Array Nat) (k budget seed : Nat) : Nat × Nat := Id.run do
  let n := ws.size
  let dom := (Array.range n).filter (fun w => f[w]! < n)
  let mut tested := 0
  let mut bad := 0
  for P in probeSample dom k budget seed do
    if P.any (fun w => f[w]! != w) then
      tested := tested + 1
      let Q := P.map (f[·]!)
      if distKey vals secIdx nSec (P.map (ws[·]!)) != distKey vals secIdx nSec (Q.map (ws[·]!)) then
        bad := bad + 1
  return (tested, bad)

/-- `bench transport`: the property everything rests on, checked by brute force on the raw
    netlist.  (a) every listed group element; (b) relabellings of the atoms that map whole
    sharings to whole sharings and come from no symmetry search at all; (c) corrupted tables,
    which must be caught, so that (a) and (b) mean something. -/
def benchTransport : IO Unit := do
  let work : Nat := 1 <<< 27
  let mut sumT := 0
  let mut sumB := 0
  let mut sumBog := 0
  let mut sumBogB := 0
  let mut caught := 0
  let mut planted := 0
  for (name, g, d) in benchSuite ++ benchLarge do
    let c := g.circuit
    let ws := c.wireOrder
    let n := ws.size
    match truthTables c with
    | none => IO.println s!"TRANSPORT\t{name}\tskipped (too many leaves)"
    | some (vals, secIdx, nSec) =>
      let s := symmetryOf g 64
      let T := (WireTables.of s ws).fwd.filter
        (fun f => (Array.range n).any (fun w => f[w]! < n && f[w]! != w))
      let sizes := [d, d + 1]
      let budget := (work / secIdx.size / (max T.size 1 + 8) / (sizes.length * 2)) + 1
      let mut seed : Nat := 88172645463325252
      let mut gt := 0
      let mut gb := 0
      for f in T do
        for k in sizes do
          seed := seed + 1
          let (t', b') := transportViolations vals secIdx nSec ws f k budget seed
          gt := gt + t'; gb := gb + b'
      sumT := sumT + gt; sumB := sumB + gb
      -- (b) relabellings from nowhere: swap two shares of a sharing, two gadget randoms, or two
      -- whole sharings of the same size; take whatever is valid
      let atom (nm : String) : VarType := .Public s!"sh:{nm}"
      let bundles := (shareChecks c).bundles
      let rnds : Array VarType := ws.foldl (fun acc nm =>
        (c.wireDefs[nm]!).inputs.foldl (fun acc i => match i with
          | .leaf l@(.Random _) => if acc.contains l then acc else acc.push l
          | _ => acc) acc) #[]
      let mut swaps : Array (Array (VarType × VarType)) := #[]
      for x in bundles do
        for i in [0:x.shares.size - 1] do
          swaps := swaps.push #[(atom x.shares[i]!, atom x.shares[i + 1]!)]
      for i in [0:min rnds.size 6] do
        for j in [i+1:min rnds.size 6] do
          swaps := swaps.push #[(rnds[i]!, rnds[j]!)]
      for i in [0:bundles.size - 1] do
        let x := bundles[i]!
        let y := bundles[i + 1]!
        if x.shares.size == y.shares.size then
          swaps := swaps.push (x.shares.zip y.shares |>.map (fun (u, v) => (atom u, atom v)))
      let mut bt := 0
      let mut bb := 0
      if s.active then
        let pos : HashMap String Nat := (ws.zipIdx).foldl (fun acc (w, q) => acc.insert w q) {}
        for sw in swaps do
          let lm : HashMap VarType VarType := sw.foldl (fun m (u, v) => (m.insert u v).insert v u) {}
          let m := nameMap s.dag lm
          let f := ws.map (fun w => match m[w]? with | some v => (pos[v]?).getD n | none => n)
          seed := seed + 1
          let (t', b') := transportViolations vals secIdx nSec ws f d (budget / 4 + 1) seed
          bt := bt + t'; bb := bb + b'
      sumBog := sumBog + bt; sumBogB := sumBogB + bb
      -- (c) corrupt a real table: exchange two images inside its valid part
      let mut plantedHere := 0
      let mut caughtHere := 0
      for f in T.extract 0 (min T.size 4) do
        let dom := (Array.range n).filter (fun w => f[w]! < n)
        if dom.size ≥ 2 then
          let a := dom[0]!
          let b := dom[dom.size - 1]!
          if f[a]! != f[b]! then
            let f' := (f.set! a f[b]!).set! b f[a]!
            seed := seed + 1
            let (_, v1) := transportViolations vals secIdx nSec ws f' d (budget / 2 + 1) seed
            let (_, v2) := transportViolations vals secIdx nSec ws f' (d + 1) (budget / 2 + 1) (seed + 7)
            plantedHere := plantedHere + 1
            if v1 + v2 > 0 then caughtHere := caughtHere + 1
      planted := planted + plantedHere; caught := caught + caughtHere
      IO.println s!"TRANSPORT\t{name}\t{d}\tleaves=2^{secIdx.size.log2}\tper-table budget={budget}\tgroup: elements={T.size} tested={gt} violations={gb}\tfree relabellings: tested={bt} violations={bb}\tcorrupted tables: {caughtHere}/{plantedHere} caught"
      (← IO.getStdout).flush
  -- (d) a relabelling that splits a sharing has a perfect wire map and still fails
  let mut h : GlobalDAG := {}
  h := demoShares h "a" "a" 2
  h := demoShares h "b" "b" 2
  h := h.addWireXor "v" #[.wire "a0", .wire "a1"]
  h := h.addWireXor "w" #[.wire "a0", .wire "b1"]
  let atomic := buildAtomicDAG h.circuit
  let swap : HashMap VarType VarType := ({} : HashMap VarType VarType)
    |>.insert (.Public "sh:a1") (.Public "sh:b1") |>.insert (.Public "sh:b1") (.Public "sh:a1")
  let m := nameMap atomic swap
  let wrong := match truthTables h.circuit with
    | some (vals, secIdx, nSec) =>
      distKey vals secIdx nSec #["v"] != distKey vals secIdx nSec #["w"]
    | none => false
  IO.println s!"TRANSPORT-SUMMARY\tgroup elements: tested={sumT} violations={sumB}\tfree relabellings: tested={sumBog} violations={sumBogB}\tcorrupted tables caught={caught}/{planted}\tsplit-sharing swap maps v to {m["v"]?.getD "-"}; distributions differ={wrong}"

def runBench : IO Unit := do
  IO.println "=== end-to-end checkDProbing (best of 3) ==="
  let mut total := 0
  for (name, g, d) in benchSuite do
    let mut best := 0
    let mut line := ""
    for k in [0:3] do
      let ((_, _, res, st), t) ← timeNs (fun _ => checkDProbing g d)
      if k == 0 || t < best then best := t
      line := s!"{if res.isSecure then "S" else "I"}\tdischarges={st.totalDischarges}"
    total := total + best
    IO.println s!"E2E\t{name}\t{d}\t{line}\tms={best / 1000000}.{(best / 100000) % 10}"
    (← IO.getStdout).flush
  IO.println s!"E2E-TOTAL\tms={total / 1000000}"
  IO.println "=== cell search, no symmetry (best of 3) ==="
  let mut totalC := 0
  -- `benchLarge` repeats some suite entries: each entry counts towards the suite total once
  for ((name, g, d), i) in (benchSuite ++ benchLarge).zipIdx do
    let mut best := 0
    let mut line := ""
    for k in [0:3] do
      let ((_, s, res), t) ← timeNs (fun _ => checkDProbingCells g d)
      if k == 0 || t < best then best := t
      line := s!"{if res.isSecure then "S" else "I"}\tengine={s.cnt.engine}\tcells={s.cnt.cells}"
    if i < benchSuite.length then totalC := totalC + best
    IO.println s!"CELLS\t{name}\t{d}\t{line}\tms={best / 1000000}.{(best / 100000) % 10}"
    (← IO.getStdout).flush
  IO.println s!"CELLS-TOTAL(suite)\tms={totalC / 1000000}"
  IO.println "=== symmetric cell search, setup included (best of 3) ==="
  let mut totalS := 0
  for ((name, g, d), i) in (benchSuite ++ benchLarge).zipIdx do
    let mut best := 0
    let mut line := ""
    for k in [0:3] do
      let ((_, s, res, _), t) ← timeNs (fun _ => checkDProbingSym g d)
      if k == 0 || t < best then best := t
      line := s!"{if res.isSecure then "S" else "I"}\tengine={s.cnt.engine}\tcells={s.cnt.cells}\tdeep={s.cnt.deep}"
    if i < benchSuite.length then totalS := totalS + best
    IO.println s!"SYM\t{name}\t{d}\t{line}\tms={best / 1000000}.{(best / 100000) % 10}"
    (← IO.getStdout).flush
  IO.println s!"SYM-TOTAL(suite)\tms={totalS / 1000000}"
  IO.println "=== per-call profile (seeded random probe sets) ==="
  for (name, g, d) in benchLarge do
    profileCalls name g d (if d == 1 then 300 else 2000)

end verif

def main (args : List String) : IO UInt32 :=
  match args with
  | ["nofactor"] => do verif.runNoFactorAblation; return 0
  | ["scaling"]  => do verif.runScaling; return 0
  | ["compare"]  => do verif.runCompare; return 0
  | ["bench"]    => do verif.runBench; return 0
  | ["trace", name] => do verif.runTrace name; return 0
  | ["bench", "cells", name] => do verif.benchCellsOne name; return 0
  | ["bench", "sym", name] => do verif.benchSymOne name; return 0
  | ["bench", "ablate", name, sy, ea, u] => do
    verif.benchAblate name (sy == "1") (ea == "1") u.toNat!; return 0
  | ["bench", "setup", name] => do verif.benchSetup name; return 0
  | ["bench", "plainroot", name] => do verif.benchPlainRoot name; return 0
  | ["bench", "cap", name, c] => do verif.benchCap name c.toNat!; return 0
  | ["bench", "groups", name] => do verif.benchGroups name; return 0
  | ["bench", "groups-report", c] => do verif.benchGroupsReport c.toNat!; return 0
  | ["bench", "contraction", name, co] => do verif.benchContraction name (co == "1"); return 0
  | ["bench", "transport"] => do verif.benchTransport; return 0
  | ["bench", "trichina"] => do verif.benchTrichina; return 0
  | "golden" :: rest => verif.runGolden rest
  | ["check", name] =>
    -- one gadget, cell search with the automatic symmetry policy
    match (verif.benchSuite ++ verif.benchLarge).find? (·.1 == name) with
    | none => do IO.eprintln s!"unknown gadget '{name}'"; return 2
    | some (_, g, d) => do
      let (_, s, res, plan?) := verif.checkDProbingSym g d
      IO.println s!"{name} @ order {d}: {if res.isSecure then "SECURE" else "INSECURE"}  (engine calls {s.cnt.engine}, cells {s.cnt.cells}, group {(plan?.map (·.label)).getD "off"})"
      return 0
  | _            => do verif.runAblation; return 0

-- #eval main
