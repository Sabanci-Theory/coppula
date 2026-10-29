# Wall-clock comparison with maskVerif (2026-10-28, branch `engine-speed`)

Same machine (desktop under light load: browser, music player — expect ±20 %), same 44 gadgets.

* **maskVerif**: gitlab.com/benjgregoire/maskverif `master` (2020-07-13), OCaml 4.14.1, `make native`.
  Each gadget translated from our Lean netlist to `.mv` (one observed assignment per wire, inputs as
  sharings) and checked with `noglitch order d Probing G`. maskVerif also probes input shares and
  randoms (e.g. 275 positions vs our 225 on Keccak χ 4). Translator + runner: archive
  `maskverif-comparison-2026-10-28.tar.gz` (see `.ai/MASKVERIF_COMPARISON.md`).
* **ours**: `lake exe verif check <gadget>` — the symmetric cell search (`checkDProbingSym`):
  orbital root, lookups through the automorphisms before every engine call, groups bounded at 64
  elements. Symmetry is always on.
* Both: one process per gadget, best of 3 (1 for maskVerif's three large ones).
  Empty-run start-up: ours 11.4 ms (Lean runtime + every gadget of `Main.lean` built at
  initialisation), maskVerif 2.1 ms. "Adjusted" subtracts each tool's own start-up.

| gadget | maskVerif ms | ours ms | maskVerif adj. | ours adj. |
|---|---|---|---|---|
| DOM Keccak χ 4 shares @3 | 428.3 | 151.6 | 426 | 140 |
| DOM-AND 5 shares @4 | 373.0 | 96.6 | 371 | 85 |
| ISW-AND 5 shares @4 | 214.8 | 77.2 | 213 | 66 |
| DOM-AND 4 shares @3 | 28.7 | 21.9 | 27 | 11 |
| DOM Keccak χ 3 shares @2 | 19.9 | 19.2 | 18 | 8 |
| TI Fides AB1 @1 | 14.3 | 37.6 | 12 | 26 |
| 33 suite entries both call secure (sum) | 402 | 531 | 331 | 156 |

Verdicts: identical on all 44 (8 insecure caught by both; both certify the d+1 S-boxes and Q⁴₁₂).
Only TI Fides AB1 is faster in maskVerif (its coupling relabels input-encoding randoms, so almost
every candidate needs the cone re-evaluation and substitution — see `.ai/ENGINE_SPEED_PLAN.md`).
