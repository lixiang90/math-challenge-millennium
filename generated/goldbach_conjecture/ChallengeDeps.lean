import Mathlib

namespace Goldbach

/-!
# Goldbach's Conjecture

This file states Goldbach's conjecture (the strong, even form) in Lean, following
the classical statement:

> Every even integer strictly greater than 2 can be expressed as the sum of two primes.

We use Mathlib's `Nat.Prime` for the notion of a prime number. The evenness
condition is written directly as `n % 2 = 0`.

`GoldbachConjecture` below is the formal `Prop`. The participant is asked to prove
it — the hole is `goldbach_conjecture` in `Challenge.lean`.

This problem is included as a famous open problem for context. It is **not** one of
the seven Clay Mathematics Institute Millennium Prize Problems.
-/

/--
Goldbach's conjecture (strong form): every even integer `n` with `4 ≤ n` is the
sum of two primes.
-/
def GoldbachConjecture : Prop :=
  ∀ n : ℕ, 4 ≤ n → n % 2 = 0 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

end Goldbach
