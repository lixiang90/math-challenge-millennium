import Mathlib

open scoped BigOperators RealInnerProductSpace

universe u

/-!
# Common Euclidean Coordinate Infrastructure

This module contains small Euclidean-space aliases and calculus helpers shared by multiple
Millennium problem formalizations.
-/

/--
`EuclideanCoordinateSpace 𝕜 n` is `𝕜^n` with the canonical `ℓ²` norm and inner product from
Mathlib, implemented as `EuclideanSpace 𝕜 (Fin n)`.
-/
abbrev EuclideanCoordinateSpace (𝕜 : Type u) (n : ℕ) : Type u :=
  EuclideanSpace 𝕜 (Fin n)

namespace EuclideanCoordinateSpace

variable {𝕜 : Type u} [RCLike 𝕜] {n : ℕ}

/-- Build a vector in `EuclideanCoordinateSpace 𝕜 n` from its coordinate function. -/
noncomputable abbrev of_fun (f : Fin n → 𝕜) : EuclideanCoordinateSpace 𝕜 n :=
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := 𝕜)).symm f

@[simp] theorem of_fun_apply (f : Fin n → 𝕜) (i : Fin n) :
    (of_fun (𝕜 := 𝕜) (n := n) f) i = f i := by
  simp [of_fun, EuclideanSpace.equiv]

end EuclideanCoordinateSpace

section Real

variable {n : ℕ}

/-- Standard basis vector `eᵢ` in `ℝⁿ`. -/
noncomputable def standard_basis (i : Fin n) : EuclideanCoordinateSpace ℝ n :=
  EuclideanSpace.single i (1 : ℝ)

@[simp] theorem standard_basis_apply (i j : Fin n) :
    (standard_basis (n := n) i) j = if j = i then 1 else 0 := by
  simp [standard_basis, eq_comm]

@[simp] theorem standard_basis_self (i : Fin n) : (standard_basis (n := n) i) i = 1 := by
  simp [standard_basis]

@[simp] theorem standard_basis_neq (i j : Fin n) (h : i ≠ j) :
    (standard_basis (n := n) i) j = 0 := by
  simp [standard_basis, Ne.symm h]

/-- Partial derivative `∂ᵢ f(x)` for `f : ℝⁿ → ℝ`, defined via `fderiv`. -/
noncomputable def partial_deriv
    (i : Fin n) (f : EuclideanCoordinateSpace ℝ n → ℝ) (x : EuclideanCoordinateSpace ℝ n) : ℝ :=
  (fderiv ℝ f x) (standard_basis (n := n) i)

/-- Unfolding lemma for `partial_deriv` as `fderiv` applied to the standard basis vector. -/
theorem partial_deriv_eq_fderiv_apply
    (i : Fin n) (f : EuclideanCoordinateSpace ℝ n → ℝ) (x : EuclideanCoordinateSpace ℝ n) :
    partial_deriv (n := n) i f x = (fderiv ℝ f x) (standard_basis (n := n) i) :=
  rfl

/-- Iterated partial derivative in directions specified by a list of indices. -/
noncomputable def iterated_partial_deriv
    (indices : List (Fin n)) (f : EuclideanCoordinateSpace ℝ n → ℝ)
    (x : EuclideanCoordinateSpace ℝ n) : ℝ :=
  match indices with
  | [] => f x
  | i :: rest => partial_deriv (n := n) i (fun y => iterated_partial_deriv rest f y) x

/-- Iterated derivatives of the zero function are zero. -/
@[simp]
theorem iterated_partial_deriv_zero
    (indices : List (Fin n)) (x : EuclideanCoordinateSpace ℝ n) :
    iterated_partial_deriv (n := n) indices (0 : EuclideanCoordinateSpace ℝ n → ℝ) x = 0 := by
  induction indices generalizing x with
  | nil => simp [iterated_partial_deriv]
  | cons i rest ih =>
      simp [iterated_partial_deriv, ih, partial_deriv]

end Real
namespace MillenniumPoincare

universe u_poincare
/-!
# The Poincaré Conjecture

This file states the Clay Millennium problem “Poincaré conjecture” in Lean, following the
Clay problem description:
`Problems/Poincare/references/clay/poincare.pdf`.

Mathlib contains the standard Poincaré conjecture statements in
`Mathlib/Geometry/Manifold/PoincareConjecture.lean`. This file isolates the dimension-`3` case
as `ClayPoincareConjecture.Formulations.SimplyConnectedClosed3Manifold`.

The Poincaré conjecture states that every simply connected, closed 3-manifold
is homeomorphic to the 3-sphere. It was proven by Grigori Perelman in 2003.

## Mathematical statement

In mathematical notation, the conjecture states:

If M is a compact 3-dimensional manifold without boundary such that every simple
closed curve in M can be continuously deformed to a point, then M is homeomorphic
to the 3-sphere.
-/
open scoped Manifold
open Metric (sphere)

/-- The model three-dimensional Euclidean space for topological `3`-manifolds. -/
@[reducible]
def EuclideanThreeSpace : Type :=
  EuclideanCoordinateSpace ℝ 3

/-- The ambient four-dimensional Euclidean space used in Milnor's Clay description of `S³`. -/
@[reducible]
def EuclideanFourSpace : Type :=
  EuclideanCoordinateSpace ℝ 4

/--
Milnor's Clay equation for points on `S³`: points in four-dimensional Euclidean space whose
distance from the origin is exactly `1`.
-/
def three_sphere_equation (x : EuclideanFourSpace) : Prop :=
  ‖x‖ = 1

/-- The Clay `S³` as a subset of `ℝ⁴`, given by the unit-sphere equation. -/
def three_sphere_set : Set EuclideanFourSpace :=
  {x | three_sphere_equation x}

/-- The 3-sphere `S³` as the unit sphere in `ℝ⁴`, matching the Clay description. -/
@[reducible]
def ThreeSphere : Type :=
  sphere (0 : EuclideanFourSpace) 1

/-- The metric-sphere definition of `S³` is the Clay unit-sphere equation in `ℝ⁴`. -/
theorem ThreeSphere.mem_iff_equation (x : EuclideanFourSpace) :
    x ∈ sphere (0 : EuclideanFourSpace) 1 ↔ three_sphere_equation x := by
  simp [three_sphere_equation]

/-- The subset form of `S³` agrees with the metric sphere used for `ThreeSphere`. -/
theorem three_sphere_set.eq_sphere :
    three_sphere_set = sphere (0 : EuclideanFourSpace) 1 := by
  ext x
  exact (ThreeSphere.mem_iff_equation x).symm

/--
The topological Poincaré conjecture in dimension `3`, stated as a proposition.

The `SecondCountableTopology` hypothesis is the standard Lean/topological-manifold regularity
condition used here to model Clay's phrase “3-manifold”; it is not a separate geometric conclusion.
-/
def ClayPoincareConjecture.Formulations.SimplyConnectedClosed3Manifold : Prop :=
  ∀ (M : Type u_poincare)
    [TopologicalSpace M]
    [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace EuclideanThreeSpace M]
    [SimplyConnectedSpace M]
    [CompactSpace M],
      Nonempty (Homeomorph M ThreeSphere)

/--
The Clay Poincare Conjecture statement: every simply connected closed
3-manifold is homeomorphic to the 3-sphere.

In this repository, “3-manifold” is represented by the usual Hausdorff, second-countable
topological manifold typeclass package modeled on `ℝ³`.
-/
def ClayPoincareConjecture : Prop :=
  ClayPoincareConjecture.Formulations.SimplyConnectedClosed3Manifold.{u_poincare}

/--
Clay's wording “every simple closed curve can be deformed continuously to a point”, represented by
the standard simply-connected-space hypothesis used by Mathlib.
-/
def ClosedCurvesContract (M : Type u_poincare) [TopologicalSpace M] : Prop :=
  SimplyConnectedSpace M

/-- The fundamental group `pi_1(M, x)` appearing in Milnor's Clay discussion. -/
@[reducible]
def FundamentalGroupAt (M : Type u_poincare) [TopologicalSpace M] (x : M) : Type _ :=
  FundamentalGroup M x

/--
Clay's equivalent modern wording that the fundamental group is trivial, represented by
Mathlib's simply-connected-space hypothesis.
-/
abbrev TrivialFundamentalGroup (M : Type u_poincare) [TopologicalSpace M] : Prop :=
  SimplyConnectedSpace M

/-- A `TrivialFundamentalGroup` hypothesis gives a subsingleton fundamental group. -/
theorem TrivialFundamentalGroup.fundamental_group_subsingleton
    {M : Type u_poincare} [TopologicalSpace M] (h : TrivialFundamentalGroup M) (x : M) :
    Subsingleton (FundamentalGroupAt (M := M) x) := by
  letI : SimplyConnectedSpace M := h
  infer_instance

/--
Clay's question wording: if a compact 3-manifold has every closed curve deformable to a point, then
it is homeomorphic to `S³`.
-/
def ClayPoincareConjecture.Formulations.ClosedCurves : Prop :=
  ∀ (M : Type u_poincare)
    [TopologicalSpace M]
    [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace EuclideanThreeSpace M]
    [CompactSpace M],
      ClosedCurvesContract M →
        Nonempty (Homeomorph M ThreeSphere)

/--
Clay's modern `π₁` wording: if a compact 3-manifold has trivial `π₁`,
then it is homeomorphic to `S³`.
-/
def ClayPoincareConjecture.Formulations.TrivialPi1 : Prop :=
  ∀ (M : Type u_poincare)
    [TopologicalSpace M]
    [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace EuclideanThreeSpace M]
    [CompactSpace M],
      TrivialFundamentalGroup M →
        Nonempty (Homeomorph M ThreeSphere)

/-- The closed-curve formulation is equivalent to the simply-connected statement. -/
theorem ClayPoincareConjecture.iff_closed_curves :
    ClayPoincareConjecture.{u_poincare} ↔ ClayPoincareConjecture.Formulations.ClosedCurves.{u_poincare} := by
  constructor
  · intro h M _top _t2 _second _charted _compact hcurves
    haveI : SimplyConnectedSpace M := by
      simpa [ClosedCurvesContract] using hcurves
    exact h M
  · intro h M _top _t2 _second _charted _simple _compact
    have hcurves : ClosedCurvesContract M := by
      dsimp [ClosedCurvesContract]
      infer_instance
    exact h M hcurves

/-- The `π₁` formulation is equivalent to the simply-connected statement. -/
theorem ClayPoincareConjecture.iff_fundamental_group :
    ClayPoincareConjecture.{u_poincare} ↔ ClayPoincareConjecture.Formulations.TrivialPi1.{u_poincare} := by
  constructor
  · intro h M _top _t2 _second _charted _compact hpi
    haveI : SimplyConnectedSpace M := by
      simpa [TrivialFundamentalGroup] using hpi
    exact h M
  · intro h M _top _t2 _second _charted _simple _compact
    exact h M (by
      dsimp [TrivialFundamentalGroup]
      infer_instance)

/-- The closed-curve and `π₁` global formulations are equivalent. -/
theorem ClayPoincareConjecture.Formulations.ClosedCurves.iff_fundamental_group :
    ClayPoincareConjecture.Formulations.ClosedCurves.{u_poincare} ↔
      ClayPoincareConjecture.Formulations.TrivialPi1.{u_poincare} :=
  ClayPoincareConjecture.iff_closed_curves.symm.trans
    ClayPoincareConjecture.iff_fundamental_group

/-!
`SimplyConnectedSpace` already captures trivial `π₁`, so `ClayPoincareConjecture.Formulations.SimplyConnectedClosed3Manifold` already
matches the usual “π₁(M) is trivial” formulation.
-/


end MillenniumPoincare
