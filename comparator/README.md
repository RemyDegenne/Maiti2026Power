# Comparator setup

Machine-checkable verification, with [leanprover/comparator](https://github.com/leanprover/comparator),
that this repository proves the headline results claimed in [`formalization.yaml`](../formalization.yaml)
without having to read or trust the Lean development in `Maiti2026Power/`.

**Status.** Every challenge is proved. The challenges were regenerated on 2026-11-09, when the project
moved to LMLExplore; `scripts/comparator-verify.sh` has to be run again on them.

Each challenge is one file that imports LML and Mathlib modules only (the project does not use
LMLExplore's definitions yet), no project modules and no sibling helpers.

## The trust story

For each headline theorem `Maiti2026Power.<name>` there is a challenge file `Challenge_<name>.lean` and a
config `<name>.json`; the list is `targets.txt`:

| paper result | challenge(s) |
|---|---|
| Theorem 1 (fixed-design upper bound) | `exists_isFixedDesign_isPAC` |
| Theorem 2 (adaptive lower bound) | `le_budget_of_isPAC` |
| Theorem 3 (non-adaptive lower bound) | `le_budget_of_isFixedDesign_of_isPAC` |
| Proposition 4 (width bounds) | `gw_le_card`, `gw_le_sqrt_log_ncard`, `sqrt_log_le_gw` |
| Theorem 5 (a set with small width) | `width_separation` |
| Theorem 6 (log gains on finite sets) | `exists_isPAC_of_finite` |
| Table 1 (adaptive lower bounds) | `multitaskSet_lt_budget_of_isPAC`, `hypercubePM_lt_budget_of_isPAC`, `hypercube01_lt_budget_of_isPAC`, `mSet_lt_budget_of_isPAC`, `unitBall_le_budget_of_isPAC` |
| Theorem 7 (polynomial separation) | `blockBallSet_le_budget_of_isFixedDesign_of_isPAC`, `blockBallSet_le_budget_of_isPAC`, `exists_isPAC_blockBallSet` |
| Theorem 8 (ℓ₂-norm estimation) | `exists_isAccurateNormEst` |

Each challenge states the theorem with `sorry`, with every definition of the project that the
statement rests on copied verbatim from its source by
[challenge-gen](https://github.com/LeanTrustBuilders/challenge-gen); the definitions of
LMLExplore, LML, Tau Ceti and Mathlib that it uses are imported. A reader checks the *statement*
(the challenge file) by hand and lets comparator check that the project proves exactly it, with
no axioms beyond `propext`, `Classical.choice` and `Quot.sound`, the proofs replayed through the
kernel. The config also lists the lemmas the definitions use, left `sorry` in the challenge and
proved by the project, and the theorems Lean makes of the proofs inside definitions.

## Regenerating and running

`scripts/make-challenges.py` regenerates every challenge and config from `targets.txt`;
`lake build Comparator` checks that they compile; `scripts/comparator-verify.sh [--insecure]`
runs comparator on every config (see the script header for the sandbox requirements).
