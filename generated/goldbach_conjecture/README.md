# `goldbach_conjecture`

Goldbach's Conjecture (not a Millennium Prize problem)

- Problem ID: `goldbach_conjecture`
- Test Problem: no
- Submitter: math-challenge.org
- Notes: The strong (even) form of Goldbach's conjecture — every even integer greater than 2 is the sum of two primes. Included as a well-known open problem for context; it is NOT one of the seven Clay Mathematics Institute Millennium Prize Problems.
- Source: https://github.com/lixiang90/math-challenge-millennium
- Informal solution: Prove that every even integer n with 4 <= n is the sum of two primes.

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
