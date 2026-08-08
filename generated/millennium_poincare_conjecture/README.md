# `millennium_poincare_conjecture`

Millennium Prize: Poincare Conjecture

- Problem ID: `millennium_poincare_conjecture`
- Test Problem: no
- Submitter: lean-dojo/LeanMillenniumPrizeProblems contributors
- Notes: Perelman proved the mathematical theorem. This challenge asks for the still-missing Lean proof of the encoded closed simply connected 3-manifold statement.
- Source: https://github.com/lean-dojo/LeanMillenniumPrizeProblems/tree/fd5207106c8c13c40cd4eeb0acb169c2c4e58aeb/Problems/Poincare/Millennium.lean
- Informal solution: Formalize a proof that every closed simply connected topological 3-manifold is homeomorphic to S^3.

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
