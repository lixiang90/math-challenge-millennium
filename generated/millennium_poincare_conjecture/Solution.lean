import ChallengeDeps
import Submission

open MillenniumPoincare

universe u_poincare

theorem clay_prize_poincare_conjecture : ClayPoincareConjecture.{u_poincare} := by
  exact Submission.clay_prize_poincare_conjecture
