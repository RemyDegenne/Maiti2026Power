# Maiti2026Power

A Lean 4 formalization of *On the Power of Adaptivity for ε-Best Arm Identification in Linear
Bandits* (Arnab Maiti, Yunbei Xu and Kevin Jamieson, COLT 2026,
[arXiv:2605.15663](https://arxiv.org/abs/2605.15663)), on top of
[LMLExplore](https://github.com/LeanMachineLearning/LMLExplore), and so of
[LML](https://github.com/LeanMachineLearning/LML), [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
and [Mathlib](https://github.com/leanprover-community/mathlib4). It follows the layout of
[lml-paper-template](https://github.com/LeanMachineLearning/lml-paper-template).

It formalizes the minimax sample-complexity results of the paper: the non-adaptive fixed-design
upper bound in terms of a Gaussian width of the action set, the matching lower bounds, the
structured action sets on which adaptivity only gives logarithmic gains, the `ℓ₂`-norm estimation
procedure, and the action set on which adaptivity gives a polynomial improvement (Theorems 1–3,
5–8, Proposition 4 and the lower bounds of Table 1). Every headline result is proved, with no
`sorry`, and comparator verifies them.

- Website: https://RemyDegenne.github.io/Maiti2026Power/, with the blueprint, the referee site and
  the literature links (which declarations formalize which results of the paper). CI builds it on
  each push to `master`. `scripts/formalize.sh` also commits the literature links, as
  `literature/annotations.jsonl`, when the paper is formalized and after the final bump.
- The paper: `source/`. Errors found in it, with their corrections: `notes/paper-errata.md`.
- The paper's results: `Maiti2026Power/MXJ2026/`, one file per result, listed with their status in
  `formalization.yaml`; comparator challenges in `comparator/`.
- Library-shaped material: `Maiti2026Power/ForLMLExplore/`, which Tau Ceti workers port to
  LMLExplore; `PAPER_ROADMAP.md` says where each item goes.
- The blueprint outline and the design decisions: `notes/`.

## Building

```bash
scripts/build.sh
```

The script fetches Mathlib's and Tau Ceti's prebuilt files, then runs `lake build`; its arguments go
to `lake build`.

## Working on it

The workflow is the `formalize-paper` skill of the `lml` Claude Code plugin
([lml-claude](https://github.com/LeanMachineLearning/lml-claude)). The paper is formalized; what is
left is to contribute its library-shaped part. `scripts/formalize.sh`, in a terminal or tmux, tags
`PAPER_ROADMAP.md`, sends the reusable parts to LMLExplore, and once they are merged moves the paper
to the current LMLExplore.
