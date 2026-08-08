# `millennium_p_versus_np`

Millennium Prize: P versus NP

- Problem ID: `millennium_p_versus_np`
- Test Problem: no
- Submitter: lean-dojo/LeanMillenniumPrizeProblems contributors
- Holes (1): `Millennium.clay_prize_p_versus_np` (def)
- Notes: The target is an explicit resolution type with constructors for both P = NP and P != NP; it is not the classically trivial excluded-middle proposition.
- Source: https://github.com/lean-dojo/LeanMillenniumPrizeProblems/tree/fd5207106c8c13c40cd4eeb0acb169c2c4e58aeb/Problems/PVersusNP/Millennium.lean
- Informal solution: Construct either the positive branch (a deterministic polynomial-time simulation of every NP verifier) or the negative branch (a proof that no such simulation exists).

Do not modify `Challenge.lean` or `Solution.lean`. Those files are part of the
trusted benchmark and fixed by the repository.

This is a multi-hole problem: the challenge declares multiple `def`s,
`instance`s, and/or `theorem`s as `sorry`. Fill all of them in
`Submission.lean` (under `namespace Submission`) for comparator to accept
your solution.

Participants may use Mathlib freely. Any helper code not already available in
Mathlib must be inlined into the submission workspace.

`lake test` runs comparator for this problem. The command expects a comparator
binary in `PATH`, or in the `COMPARATOR_BIN` environment variable.
