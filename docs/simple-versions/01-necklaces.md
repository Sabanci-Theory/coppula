# Version 1: one permutation, one engine call per necklace

The simplest symmetric verifier we can state:

1. pick one good permutation π of the circuit;
2. group the probe sets into families that π relates, called necklaces;
3. run the engine once per necklace.

There are no cells, no extension and no stored safe sets. The engine sees one probe set at a
time, and a verdict covers only that probe set and its necklace.

Code: [`Verif/Necklace.lean`](../../lean_ffi/verif/Verif/Necklace.lean). The rewrite engine and
the group are the same ones the full algorithm uses.

## The idea, on DOM-AND with 3 shares

DOM-AND with 3 shares at `d = 2` has 21 wires, so 210 pairs of wires to check. Take the
permutation that adds 1 to every share index: `a0→a1→a2→a0`, the same for `b`, and the randoms
follow (`r01→r12→r20→r01`). On the wires it reads

```
(u0 u1 u2)  (p01 p12 p20)  (p10 p21 p02)  (c01 c12 c20)  (c10 c21 c02)  (s0 s1 s2)
```

Each bracket is a **ring**: π moves every wire one place along it. Now take the pair `{u0, s1}`.
Applying π gives `{u1, s2}`, and applying it again gives `{u2, s0}`. All three are the same
computation with the shares renamed, and renaming the shares of a uniform sharing changes nothing
an attacker can learn. So the three pairs have the same verdict, and one engine call settles
them all. That family of three is a **necklace**: a shift moves every mark one step around its
ring, as if you rotated a necklace.

## Shifts, and wires where they fail

A **shift** of a probe set `P` is `π^k(P)`. It needs a condition. π renames input shares, not
wires, so it acts on a wire by renaming its expression, and the result must be the expression of
some wire. If it is not, we say π^k is **not valid** on that wire and the shift does not exist.

DOM-AND computes `s0` in two steps, and the middle step `s0m0 = u0 ⊕ c01` shows this. Applying π
gives `u1 ⊕ c12`, but the circuit computes `s1m0 = u1 ⊕ c10`, so no wire holds that value and π
is not valid on `s0m0`. These are the **loose** wires of π: some power is not valid on them. π²
happens to work here, since it sends `s0m0` to `u2 ⊕ c20 = s2m0`. A shift of `P` exists exactly
when that power is valid on every wire of `P`.

The verdict carries over along every shift that exists (§6.1 of the full notes), under the
assumptions (S1) and (S2). A circuit that fails them has no shifts, and this version becomes
plain enumeration.

## What makes a permutation good

There is no extension here, so nothing is ever settled except by an engine call on its necklace.
The cost is therefore simple:

> engine calls = number of necklaces (for a secure circuit)

**A good permutation is one that leaves the fewest necklaces.** That is the entire definition.
Three things pull on it:

- **Long period.** A necklace has at most as many members as π has powers, so the period is the
  best possible saving factor.
- **Valid on many wires.** A probe set that no shift applies to is a necklace of one.
- **Rings as long as the period.** Short rings give short necklaces, and a wire π leaves alone
  moves nothing.

These conflict, so no single one of them picks the winner. On DOM-AND with 3 shares:

| Period | Rings | Loose wires | Necklaces |
|---|---|---|---|
| 3 | six of length 3 | 3 | **90** |
| 6 | lengths 6, 3, 2, 1 | 9 | 107 |
| 2 | nine of length 2, two of length 1 | 1 | 120 |
| 3 | four of length 3 | 9 | 166 |
| 1 (no symmetry) | | 0 | 210 |

The longest period loses here, and so does the permutation with the fewest loose wires. On Keccak
χ with 4 shares it goes the other way. Period 5 is valid on every wire and leaves 374,640
necklaces, while period 15 has 25 loose wires and leaves 179,378.

So we do not guess from the shape of π. We count the necklaces exactly and take the smallest.

## Scoring: counting necklaces without listing them

**The trick.** Let a necklace of 3 probe sets count as 3 × ⅓. Then

```
necklaces = sum, over all probe sets P, of 1 / (size of P's necklace)
```

**When every shift exists.** On the 18 ring wires of DOM-AND there are 153 pairs. π has period 3
and no pair is left in place by a shift, so every necklace has 3 members and there are
153 / 3 = **51**.

Sometimes a shift leaves a set in place, and then its necklace is shorter. On a ring of 4 wires,
`{w0, w2}` shifted by 2 is itself, so it has a necklace of only 2. Each such set makes the plain
division too small. The orbit-counting lemma corrects for this by adding them back:

```
necklaces = (1 / period) × sum, over k, of (sets that π^k leaves in place)
```

A set is left in place by `π^k` exactly when it is made of whole cycles of `π^k`, and those are
easy to count: a ring of length `L` splits into `gcd(L, k)` cycles of length `L / gcd(L, k)`.

**With loose wires.** The size of a necklace now depends on the set, because different sets allow
different powers. Write `V(P)` for the powers valid on every wire of `P`. Each member of a
necklace reaches all the others, so the same counting gives

```
necklaces = sum, over k, of: sum, over P left in place by π^k, of 1 / |V(P)|
```

The ordinary formula is the case where `|V(P)|` is always the period. To evaluate this we go
through the cycles of `π^k` and count how many sets of size `d` can be built from them, grouped
by which powers stay valid (`necklaceCount`). No probe set is listed: on Keccak χ with 4 shares
the whole setup takes 35 ms, against 1.9 million probe sets.

**The DOM-AND number.** Pairs inside the rings give 51, as above. That leaves 57 pairs touching a
loose wire. On the 54 pairs of one loose and one ring wire, π² carries `{s0m0, x}` to
`{s2m0, π²(x)}`, which merges 18 of them into 18 pairs of the other kind, leaving 36 necklaces.
The 3 pairs of two loose wires stay separate: `{s0m0, s2m0}` under π² would need π² valid on
`s2m0`, and it is not. In total 51 + 36 + 3 = **90**.

**Finding π.** List every element of the group (the same list of at most 64 elements the full
algorithm uses) and score it. Elements with the same powers get the same score, so each set of
powers is scored once. Ties go to the longer period.

## Producing the necklaces

We need exactly one probe set from each necklace. Every necklace has one member that reads first
in wire order, so we take that one:

```
for every probe set P, in reading order:
    if some shift of P reads earlier than P:  skip P
    otherwise:                                run the engine on P, stop if it fails
```

Example: `{u0, u1}` has shifts `{u1, u2}` and `{u0, u2}`, and neither reads earlier, so it is
kept. When the walk reaches `{u0, u2}`, its shift by π is `{u0, u1}`, which does read earlier, so
it is skipped. `{u1, u2}` is skipped the same way.

The walk does not recognise necklaces. It looks at one probe set and its shifts, stores nothing,
and every test takes at most `period - 1` table lookups per wire.

This is deliberately naive: it visits every probe set, even the ones it skips, because this
version has no way to skip a block. The cost turns out to be small next to the engine calls (see
the results).

## Why it is correct

Take any probe set `P`. If it was skipped, it has a shift that reads earlier, and that shift has
the same verdict. If that one was skipped too, repeat. Reading order cannot go down forever, so
this ends at a probe set that was kept, and the engine certified it. Going back along the chain,
`P` is secure. Sets smaller than `d` are subsets of these.

This argument needs only one fact, that a shift keeps the verdict, so it does not depend on the
scoring. A wrong score could only make the run slower.

If the engine fails on a kept probe set the run reports INSECURE at that probe set. As in the full
algorithm, that means the engine could not certify it.

## How it was checked

- **The score is exact.** `lake exe verif bench necklace-score <gadget>` walks every distinct
  choice of π and compares the walk's count with `necklaceCount`. They are equal on all 249
  choices across the 43 gadgets, so the chosen π really is the best one in the list.
- **Shifts keep the verdict.** `lake exe verif bench necklace-audit <gadget>` runs the engine on
  every probe set and compares it with every shift by every group element, not just the powers
  of π. On the 40 gadgets with at most 50,000 probe sets that is 275,200 pairs, including the
  insecure gadgets, where a wrong shift would show. None disagree.
- **The verdicts match.** Necklaces, plain enumeration and the full algorithm give the same
  verdict on all 43 gadgets: 35 secure, 8 insecure.

## Running it

From `lean_ffi/verif`:

```bash
lake exe verif necklace "DOM AND (3 shares)"
```

```bash
lake exe verif bench necklace "DOM AND (3 shares)"
```

The first prints every candidate π with its score, the rings and the loose wires. The second
prints one line of figures.

## Results

"Plain" is the same loop with no symmetry, so one engine call per probe set. "Whole group" is how
many probe sets the walk would keep using every group element instead of the powers of one π; it
was counted, not run through the engine. Times for necklaces and the full algorithm include
setup. Each necklace and plain figure is a single run; each full figure is the best of 3.

| Gadget, order | Probe sets | Group | Period of π | Necklaces | Whole group | Full: engine calls | Plain | Necklaces | Full |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Keccak χ, 4 shares, 3 | 1,873,200 | 30 | 15 | 179,378 | 97,698 | 579 | 18.7 s | 2.3 s | 0.13 s |
| DOM-AND, 5 shares, 4 | 677,040 | 24 | 3 | 363,584 | 90,242 | 239 | 6.5 s | 3.5 s | 0.07 s |
| ISW-AND, 5 shares, 4 | 677,040 | 2 | 2 | 535,690 | 535,690 | 485 | 6.6 s | 5.2 s | 0.07 s |
| DOM-AND, 4 shares, 3 | 9,880 | 24 | 3 | 4,929 | 1,092 | 38 | 66 ms | 39 ms | 7 ms |
| Keccak χ, 3 shares, 2 | 7,750 | 10 | 10 | 860 | 860 | 46 | 49 ms | 14 ms | 6 ms |
| TI Fides AB1, 1 | 592 | 2 | 2 | 592 | 592 | 31 | 7 ms | 12 ms | 24 ms |
| DOM-AND, 3 shares, 2 | 210 | 36 | 3 | 90 | 37 | 9 | 1 ms | 3 ms | 1 ms |
| **All 35 secure gadgets** | **3,257,259** | | | **1,093,983** | **734,935** | **1,743** | **32.0 s** | **11.2 s** | **0.32 s** |

DOM-AND with 5 shares uses a subgroup of 24 elements, because the group is capped at 64. Every
gadget's figures are in
[`results/necklaces_2026-11-01.txt`](../../lean_ffi/verif/results/necklaces_2026-11-01.txt).

## What this version shows

**Symmetry alone cuts the work by about 3.** That is real: the necklace version is 2.8 times
faster than plain enumeration across the secure gadgets, and 8 times faster on Keccak χ with 4
shares. But it cannot get close to the full algorithm, which needs 1,743 engine calls where this
version needs over a million, and is 35 times faster on the suite.

**The limit is not the choice of π.** Even with the whole group, 734,935 probe sets remain. The
reason shows on ISW-AND: its group has 2 elements, so no use of symmetry can save more than half.
Symmetry only says that two probe sets are alike. It never settles a probe set that has no
symmetric partner already checked. That is the job of the extension, the next version.

**One π does leave a gap, on some gadgets.** Whole-group use beats the best π on 9 of the 35
secure gadgets, by up to 4.5 times on DOM-AND with 4 shares. A single π has only its own powers,
while DOM-AND has independent ways to permute its shares. On the other 26 gadgets one π already
does as well as the group.

**The walk is not the bottleneck.** Walking takes 0.7 s of the 11.2 s, even though it visits all
3.2 million probe sets.

**Engine calls are not all equal.** This version asks the engine only for a verdict, at about
10 µs a call on Keccak χ. The full algorithm also needs the certificate that the extension
works from, runs the extension and does its lookups, which comes to about 200 µs per engine
call all told. That is why the necklace version wins on one gadget, TI Fides AB1: the full
algorithm spends 24 ms on 31 calls, while 592 cheap calls take 12 ms. At order 1 there are too
few probe sets for the extension to pay for itself.
