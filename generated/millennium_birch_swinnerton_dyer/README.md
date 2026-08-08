# `millennium_birch_swinnerton_dyer`

Millennium Prize: Birch and Swinnerton-Dyer Conjecture

- Problem ID: `millennium_birch_swinnerton_dyer`
- Test Problem: no
- Submitter: lean-dojo/LeanMillenniumPrizeProblems contributors
- Notes: The target is the Taylor/rank formulation for elliptic curves over Q with explicit L-series data.
- Source: https://github.com/lean-dojo/LeanMillenniumPrizeProblems/tree/fd5207106c8c13c40cd4eeb0acb169c2c4e58aeb/Problems/BirchSwinnertonDyer/Millennium.lean
- Informal solution: Prove the encoded equality between algebraic rank and analytic order of vanishing.

Do not modify `Challenge.lean` or `Solution.lean`. Those files are part of the
trusted benchmark and fixed by the repository.

Write your solution in `Submission.lean` and any additional local modules under
`Submission/`.

Participants may use Mathlib freely. Any helper code not already available in
Mathlib must be inlined into the submission workspace.

Multi-file submissions are allowed through `Submission.lean` and additional local
modules under `Submission/`.

`lake test` runs comparator for this problem. The command expects a comparator
binary in `PATH`, or in the `COMPARATOR_BIN` environment variable.
