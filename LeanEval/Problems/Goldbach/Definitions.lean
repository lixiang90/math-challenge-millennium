import Mathlib

namespace Goldbach

/-!
# Goldbach's Conjecture

This file states the strong (even) form of Goldbach's conjecture: every even
natural number greater than two is the sum of two primes.
-/

/-- Goldbach's conjecture in its strong form. -/
def GoldbachConjecture : Prop :=
  鈭€ n : 鈩? 4 鈮?n 鈫?n % 2 = 0 鈫?    鈭?p q : 鈩? Nat.Prime p 鈭?Nat.Prime q 鈭?p + q = n

end Goldbach

