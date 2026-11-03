# Simple versions of the verifier

The full algorithm (`docs/algorithm/symmetric-cell-search.pdf`) combines several ideas. These
notes build it up one idea at a time, so that each step shows what the idea buys and what still
goes wrong without the next one. Each version is real code, run on the same 43 gadgets.

| Version | Keeps | Leaves out | Notes |
|---|---|---|---|
| 1. Necklaces | engine, symmetry (one permutation) | cells, extension, stored safe sets | [01-necklaces.md](01-necklaces.md) |
