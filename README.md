# Math-Challenge Millennium Prize Problems

This public repository contains the seven standalone Lean workspaces used by
[math-challenge.org](https://www.math-challenge.org/) for its Millennium Prize
challenges. Each directory under `generated/` follows the official
[`lean-eval`](https://github.com/leanprover/lean-eval) comparator format and is
the exact starting point a participant should use for a submission.

## Quick start

```bash
git clone https://github.com/lixiang90/math-challenge-millennium.git
cd math-challenge-millennium/generated/millennium_p_versus_np
lake exe cache get
lake test
```

Edit `Submission.lean` and, when needed, add supporting Lean files under the
same workspace. Do not modify `Challenge.lean`, `ChallengeDeps.lean`,
`config.json`, or `holes.json`: the website verifier reconstructs those trusted
files independently before running the official comparator.

## Problems

| Problem ID | Comparator target |
| --- | --- |
| `millennium_p_versus_np` | definition `Millennium.clay_prize_p_versus_np` |
| `millennium_riemann_hypothesis` | theorem `clay_prize_riemann_hypothesis` |
| `millennium_navier_stokes` | theorem `clay_prize_navier_stokes` |
| `millennium_hodge_conjecture` | theorem `clay_prize_hodge_conjecture` |
| `millennium_birch_swinnerton_dyer` | theorem `clay_prize_birch_swinnerton_dyer` |
| `millennium_yang_mills` | theorem `clay_prize_yang_mills` |
| `millennium_poincare_conjecture` | theorem `clay_prize_poincare_conjecture` |

## Version and soundness policy

- Lean toolchain: `leanprover/lean4:v4.32.2`.
- Official lean-eval snapshot:
  `3f3786f3b4d9a4b64a5859b3036aca190cd25613`.
- Every workspace contains one and only one trusted prize hole.
- The production verifier additionally runs the comparator sandbox and an
  independent kernel check; this repository is the participant-facing source,
  not the authority used to grade a submission.

Exact pins and problem IDs are recorded in [`provenance.json`](provenance.json).

## Upstream reference

These challenges were adapted from
[`lean-dojo/LeanMillenniumPrizeProblems`](https://github.com/lean-dojo/LeanMillenniumPrizeProblems)
at commit `fd5207106c8c13c40cd4eeb0acb169c2c4e58aeb`, then ported to Lean 4.32.2
and converted with the official lean-eval generator. The lean-dojo repository
is the mathematical/source provenance; use this repository's `generated/`
workspaces when preparing an answer for Math-Challenge.

## License

The adapted upstream material is distributed under the Apache License 2.0; see
[`LICENSE`](LICENSE) and [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).
