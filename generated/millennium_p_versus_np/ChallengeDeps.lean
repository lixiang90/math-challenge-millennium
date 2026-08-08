import Mathlib

/-!
# P versus NP definitions (Mathlib 4.32 encoding API)

This is the prize statement from the upstream `Millennium.lean`, ported to the explicit-alphabet
`Encoding α Γ` API introduced after Mathlib 4.31.  The upstream file's auxiliary pair-machine
development is intentionally not copied: it uses the removed implicit-alphabet `FinEncoding` API
and is not part of the type of the prize target.
-/

namespace Millennium

open _root_.Turing
open Computability

/-- A language (decision problem) is a predicate on inputs. -/
def Language (α : Type) := α → Prop

/-- Languages decided by a deterministic polynomial-time two-stack Turing machine. -/
def InPolynomialTime {α Γ : Type} [Fintype Γ]
    (ea : Encoding α Γ) (L : Language α) : Prop :=
  ∃ (f : α → Bool) (_comp : TM2ComputableInPolyTime ea.encode encodingBoolBool.encode f),
    ∀ a, L a ↔ f a = true

/-- A polynomial-time predicate on an input and a certificate. -/
def PolynomialTimeCheckingRelation {α β Γ Δ : Type} [Fintype Γ] [Fintype Δ]
    (ea : Encoding α Γ) (eb : Encoding β Δ) (R : α → β → Prop) : Prop :=
  InPolynomialTime (encodingProd ea eb) (fun p => R p.1 p.2)

/-- Cook's verifier formulation of nondeterministic polynomial time. -/
def InNondeterministicPolynomialTime {α Γ : Type} [Fintype Γ]
    (ea : Encoding α Γ) (L : Language α) : Prop :=
  ∃ (β Δ : Type) (_alphabet : Fintype Δ) (eb : Encoding β Δ)
      (R : α → β → Prop) (k : ℕ),
    PolynomialTimeCheckingRelation ea eb R ∧
      ∀ a, L a ↔ ∃ b, (eb.encode b).length ≤ (ea.encode a).length ^ k ∧ R a b

namespace ClayPVersusNP.Formulations

/-- Literal equality of the finite-alphabet language classes `P` and `NP`. -/
def ClassEquality : Prop :=
  ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
      (L : Language (List alphabet)),
    InPolynomialTime (encodingList alphabet) L ↔
      InNondeterministicPolynomialTime (encodingList alphabet) L

end ClayPVersusNP.Formulations

/-- Stable public name for the checked positive branch of P versus NP. -/
def ClayPVersusNP : Prop :=
  ClayPVersusNP.Formulations.ClassEquality

/-- Positive outcome: the finite-alphabet classes `P` and `NP` agree. -/
abbrev ClayPVersusNP.Formulations.PositiveBranch : Prop := ClayPVersusNP

/-- Negative outcome: the finite-alphabet classes `P` and `NP` differ. -/
def ClayPVersusNP.Formulations.NegativeBranch : Prop := ¬ ClayPVersusNP

/--
An explicit resolution, kept in `Type` so classical excluded middle cannot solve the challenge.
-/
inductive ClayPVersusNPResolution : Type where
  | equal (proof : ClayPVersusNP.Formulations.PositiveBranch)
  | notEqual (proof : ClayPVersusNP.Formulations.NegativeBranch)

namespace ClayPVersusNPResolution

/-- The proposition selected by an explicit resolution. -/
def SelectedStatement : ClayPVersusNPResolution → Prop
  | .equal _ => ClayPVersusNP.Formulations.PositiveBranch
  | .notEqual _ => ClayPVersusNP.Formulations.NegativeBranch

/-- Every explicit resolution carries a proof of the branch it selects. -/
theorem selectedProof (resolution : ClayPVersusNPResolution) :
    resolution.SelectedStatement := by
  cases resolution with
  | equal proof => exact proof
  | notEqual proof => exact proof

end ClayPVersusNPResolution

end Millennium
