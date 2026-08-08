# `millennium_yang_mills`

Millennium Prize: Yang-Mills existence and mass gap

- Problem ID: `millennium_yang_mills`
- Test Problem: no
- Submitter: lean-dojo/LeanMillenniumPrizeProblems contributors
- Notes: For every connected compact simple Lie gauge group, construct a nontrivial quantum Yang-Mills theory on R4 whose Hamiltonian spectrum has a positive finite mass gap.
- Source: https://github.com/lean-dojo/LeanMillenniumPrizeProblems/tree/fd5207106c8c13c40cd4eeb0acb169c2c4e58aeb/Problems/YangMills/Millennium.lean
- Informal solution: Construct the encoded quantum field theory and establish its positive finite spectral gap.

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
