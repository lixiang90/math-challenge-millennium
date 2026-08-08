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
namespace NavierStokes

open EuclideanSpace MeasureTheory Order

/-- Spatial coordinate space `ℝⁿ`. -/
abbrev Space (n : ℕ) : Type :=
  EuclideanCoordinateSpace ℝ n

/-- Ambient spacetime coordinates for `ℝⁿ × [0,∞)`, represented as `ℝⁿ⁺¹`. -/
abbrev Spacetime (n : ℕ) : Type :=
  Space (n + 1)

/-- Clay's whole-space spatial domain `ℝ³`. -/
abbrev Space3 : Type :=
  Space 3

/-- Ambient coordinates for Clay's whole-space spacetime `ℝ³ × [0,∞)`. -/
abbrev Spacetime3 : Type :=
  Spacetime 3

/-- Initial velocity field `u₀ : ℝⁿ → ℝⁿ`. -/
abbrev InitialVelocityField (n : ℕ) : Type :=
  Space n → Space n

/-- A velocity field `u : ℝⁿ × [0,∞) → ℝⁿ`, represented on ambient spacetime. -/
abbrev VelocityField (n : ℕ) : Type :=
  Spacetime n → Space n

/-- A pressure field `p : ℝⁿ × [0,∞) → ℝ`, represented on ambient spacetime. -/
abbrev PressureField (n : ℕ) : Type :=
  Spacetime n → ℝ

/-- An external force field acting on the fluid. -/
abbrev ForceField (n : ℕ) : Type :=
  VelocityField n

/--
The material derivative operator `∂/∂t + (u · ∇)`, i.e. the total derivative following the fluid
motion.
-/
noncomputable def material_derivative (n : ℕ) (u : VelocityField n) :
    (Spacetime n → Space n) → (Spacetime n → Space n) :=
  λ v x =>
    EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := n) (fun i : Fin n =>
      -- Time derivative term: ∂v/∂t
      partial_deriv (n := n + 1) 0 (fun y => v y i) x +
      -- Convective term: (u·∇)v
      ∑ j : Fin n, u x j * partial_deriv (n := n + 1) (j.succ) (fun y => v y i) x)

/-- Divergence of a velocity field at a spacetime point: `div u = ∑ᵢ ∂ᵢ uᵢ`. -/
noncomputable def divergence {n : ℕ} (u : VelocityField n) (x : Spacetime n) : ℝ :=
  ∑ i : Fin n, partial_deriv (n := n + 1) (i.succ) (fun y => u y i) x

/-- Divergence-free condition at a spacetime point. -/
def divergence_free_at {n : ℕ} (u : VelocityField n) (x : Spacetime n) : Prop :=
  divergence u x = 0

/-- The viscous term `ν Δu`. -/
noncomputable def viscous_term (n : ℕ) (viscosity : ℝ) (u : VelocityField n) (x : Spacetime n) : Space n :=
  EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := n) (fun i : Fin n =>
    viscosity *
      (∑ j : Fin n,
        partial_deriv (n := n + 1) (j.succ)
          (fun y => partial_deriv (n := n + 1) (j.succ) (fun z => u z i) y) x))

/-- The spatial gradient of the pressure, `∇p`. -/
noncomputable def pressure_gradient {n : ℕ} (p : PressureField n) (x : Spacetime n) : Space n :=
  EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := n) (fun i : Fin n => partial_deriv (n := n + 1) (i.succ) p x)

/-- Convert a pair `(time, space)` to a point in spacetime. -/
noncomputable def spacetime_point {n : ℕ} (t : ℝ) (x : Space n) : Spacetime n :=
  EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := n + 1) (fun i : Fin (n + 1) =>
    if h : i = 0 then t else x (Fin.pred i h))

/-- Extract the time component from a spacetime point. -/
def time {n : ℕ} (x : Spacetime n) : ℝ := x 0

/-- Extract the spatial component from a spacetime point. -/
noncomputable def space {n : ℕ} (x : Spacetime n) : Space n :=
  EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := n) (fun i : Fin n => x (i.succ))

-- ===========================================================================
/--
  The Navier-Stokes equations in differential form for actually any general n.

  This structure encapsulates the core components of the Navier-Stokes equations,
  which describe the motion of viscous fluid substances. These equations are
  a set of nonlinear partial differential equations that govern fluid dynamics
  under the assumption of constant density.
-/
structure NavierStokesEquations (n : ℕ) where
  /--
    Viscosity coefficient (ν > 0).

    This parameter represents the fluid's resistance to flow or deformation.
    Higher values indicate more viscous fluids (like honey), while lower values
    indicate less viscous fluids (like water). In the Millennium Problem,
    we typically use ν = 1 to normalize the equations.

    It appears in the diffusion term ν·Δu, which models how momentum diffuses
    through the fluid due to molecular interactions.
  -/
  viscosity : ℝ

  /--
    External force field acting on the fluid.

    This represents any external forces applied to the fluid, such as:
    - Gravity
    - Magnetic fields
    - Mechanical forcing
    - Other body forces

    The force field is a function of both space and time, allowing for
    spatially and temporally varying external influences.
  -/
  external_force : ForceField n

  /--
    Viscosity is positive - a physical requirement.

    This constraint ensures the model is physically valid. A negative viscosity
    would violate the second law of thermodynamics, as it would cause energy to
    spontaneously concentrate rather than dissipate.
  -/
  viscosity_positive : viscosity > 0

  /--
    Initial velocity field at time t=0.

    This defines the starting configuration of the fluid flow. In the Millennium
    Problem, this initial condition is assumed to be smooth and have finite energy.

    The evolution of this initial state according to the Navier-Stokes equations
    is the central focus of the Millennium Problem - specifically whether this
    evolution remains smooth for all time or develops singularities.
  -/
  initial_velocity : InitialVelocityField n

  /--
    Initial velocity is divergence free - the incompressibility condition.

    This mathematical statement expresses that the fluid is incompressible
    (its density remains constant) at the initial time. Specifically:

    ∇·u = ∑(∂uⱼ/∂xⱼ) = 0

    Physically, this means the fluid's volume doesn't change as it flows.
    This constraint must be maintained throughout the flow evolution.
  -/
  initial_divergence_free : ∀ x, ∑ i : Fin n, partial_deriv i (λ y => initial_velocity y i) x = 0

-- ===========================================================================

/-- Spacetime domain `ℝⁿ × [0,∞)` viewed inside `ℝ^{n+1}`. -/
def global_spacetime_domain (n : ℕ) : Set (Spacetime n) :=
  {x | 0 ≤ x 0}

/--
Smoothness of a velocity field on Clay's global time domain.

The fields are still ambient functions on `ℝⁿ⁺¹`, which is convenient for partial derivatives, but
the regularity demanded by the Millennium statement is imposed on the half-space
`ℝⁿ × [0,∞)`.
-/
def velocity_smooth_on_global_spacetime_domain {n : ℕ} (u : VelocityField n) : Prop :=
  ContDiffOn ℝ ⊤ (fun y => u y) (global_spacetime_domain n)

/--
Smoothness of a pressure field on Clay's global time domain.

This is the scalar analogue of `velocity_smooth_on_global_spacetime_domain`.
-/
def pressure_smooth_on_global_spacetime_domain {n : ℕ} (p : PressureField n) : Prop :=
  ContDiffOn ℝ ⊤ (fun y => p y) (global_spacetime_domain n)

/--
Smoothness of a force field on Clay's global time domain.

This matches the force hypotheses in Fefferman's conditions (5) and (9), where `f` is smooth on
`ℝⁿ × [0,∞)` rather than on all of ambient spacetime.
-/
def force_smooth_on_global_spacetime_domain {n : ℕ} (f : ForceField n) : Prop :=
  ContDiffOn ℝ ⊤ (fun y => f y) (global_spacetime_domain n)

/--
A global-in-time Navier–Stokes solution on `ℝⁿ × [0,∞)`.

This matches the Clay statement's use of solutions on `ℝ³ × [0,∞)`, avoiding the finite-horizon
parameter `T` used by `Solution`.
-/
structure GlobalSolution {n : ℕ} (nse : NavierStokesEquations n) where
  /-- Velocity field `u : ℝ^{n+1} → ℝⁿ`. -/
  velocity : VelocityField n
  /-- Pressure field `p : ℝ^{n+1} → ℝ`. -/
  pressure : PressureField n

  /-- Momentum equation (Navier–Stokes) on `t ≥ 0`. -/
  momentum_equation :
    ∀ x : Spacetime n,
      x ∈ global_spacetime_domain n →
        material_derivative n velocity velocity x + pressure_gradient pressure x =
          viscous_term n nse.viscosity velocity x + nse.external_force x

  /-- Incompressibility `div u = 0` on `t ≥ 0`. -/
  incompressible :
    ∀ x : Spacetime n, x ∈ global_spacetime_domain n → divergence_free_at velocity x

  /-- Initial condition at time `t = 0`. -/
  initial_condition :
    ∀ x : Space n, velocity (spacetime_point 0 x) = nse.initial_velocity x

/-- A global solution whose fields are smooth on `ℝⁿ × [0,∞)`. -/
structure GlobalSmoothSolution {n : ℕ} (nse : NavierStokesEquations n) extends GlobalSolution nse where
  velocity_smooth : velocity_smooth_on_global_spacetime_domain velocity
  pressure_smooth : pressure_smooth_on_global_spacetime_domain pressure

-- ===========================================================================
/--
  The energy of a fluid flow at time t.

  This function captures the total kinetic energy of the fluid at a given time t.
  It is defined as the integral of the squared velocity field over the spatial domain.
-/
noncomputable def energy_integral {n : ℕ} (u : VelocityField n) (t : ℝ) : ℝ :=
  ∫ x : Space n, ∑ i : Fin n, (u (spacetime_point t x) i)^2

end NavierStokes
namespace NavierStokesOnR3

open EuclideanSpace MeasureTheory Order NavierStokes
open scoped BigOperators

/-!
# Navier–Stokes Millennium problem (Fefferman) on `ℝ³`

This file states Fefferman's parts (A) and (C) from the Clay problem description
`Problems/NavierStokes/references/clay/navierstokes.pdf`.

We follow the PDF's numbering:

* (4) decay of the initial velocity and its spatial derivatives
* (5) decay of the force and its space/time derivatives
* (6) smoothness of the solution `(p,u)` on `ℝ³ × [0,∞)`
* (7) bounded energy: `∫_{ℝ³} |u(x,t)|^2 dx < C` uniformly in `t ≥ 0`
-/

/-- Initial velocity field `u₀ : ℝ³ → ℝ³` in Fefferman's statements (A) and (C). -/
def InitialVelocity : Type := Space3 → Space3

/-- Force field `f : (t,x) ∈ ℝ × ℝ³ ↦ ℝ³`, i.e. a function on spacetime `ℝ⁴`. -/
def SpacetimeForce : Type := Spacetime3 → Space3

/-- Divergence-free condition for an initial velocity field on `ℝ³`. -/
def DivergenceFreeInitial (u₀ : InitialVelocity) : Prop :=
  ∀ x, ∑ i : Fin 3, partial_deriv i (fun y => u₀ y i) x = 0

/-! ## Fefferman's conditions (4)–(7) -/

/-- Spatial derivatives of a vector field as an `ℝ³`-vector. -/
noncomputable def spatial_derivative_vector (u₀ : InitialVelocity) (α : List (Fin 3)) (x : Space3) : Space3 :=
  EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := 3) (fun i : Fin 3 => iterated_partial_deriv (n := 3) α (fun y => u₀ y i) x)

/--
Fefferman's decay condition (4) for the initial velocity `u₀` on `ℝ³`.

We encode multi-indices as lists of coordinate directions, giving a direct coordinate form of the
derivative decay condition.
-/
def SmoothRapidDecayInitial (u₀ : InitialVelocity) : Prop :=
  ContDiff ℝ ⊤ u₀ ∧
    ∀ (α : List (Fin 3)) (K : ℕ),
      ∃ C : ℝ, 0 < C ∧ ∀ x : Space3,
        ‖spatial_derivative_vector u₀ α x‖ ≤ C / (1 + ‖x‖) ^ K

/-- Mixed (time + space) derivatives of a force field as an `ℝ³`-vector. -/
noncomputable def spacetime_derivative_vector (f : SpacetimeForce) (α : List (Fin 3)) (m : ℕ) (x : Spacetime3) : Space3 :=
  let idx : List (Fin 4) := (List.replicate m (0 : Fin 4)) ++ (α.map Fin.succ)
  EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := 3) (fun i : Fin 3 => iterated_partial_deriv (n := 4) idx (fun y => f y i) x)

/-- Every mixed derivative of the zero force field is the zero vector. -/
@[simp] theorem spacetime_derivative_vector_zero (α : List (Fin 3)) (m : ℕ) (x : Spacetime3) :
    spacetime_derivative_vector (fun _ : Spacetime3 => (0 : Space3)) α m x = 0 := by
  ext i
  simp only [spacetime_derivative_vector, EuclideanCoordinateSpace.of_fun_apply]
  change iterated_partial_deriv (n := 4)
    (List.replicate m (0 : Fin 4) ++ α.map Fin.succ) (0 : Spacetime3 → ℝ) x = 0
  exact iterated_partial_deriv_zero
    (List.replicate m (0 : Fin 4) ++ α.map Fin.succ) x

/--
Fefferman's decay condition (5) for the forcing term `f` on `ℝ³ × [0,∞)`.

We express the weight as `(1 + |x| + t)^{-K}` using `‖space x‖` for `|x|` and the time coordinate `x 0 = t`.
-/
def SmoothRapidDecayForce (f : SpacetimeForce) : Prop :=
  force_smooth_on_global_spacetime_domain f ∧
    ∀ (α : List (Fin 3)) (m K : ℕ),
      ∃ C : ℝ, 0 < C ∧
        ∀ x : Spacetime3, 0 ≤ x 0 →
          ‖spacetime_derivative_vector f α m x‖ ≤ C / (1 + ‖space x‖ + x 0) ^ K

/-- The zero force satisfies Fefferman's forcing decay condition (5). -/
theorem zero_force_smooth_rapid_decay :
    SmoothRapidDecayForce (fun _ : Spacetime3 => (0 : Space3)) := by
  refine ⟨?_, ?_⟩
  · change ContDiffOn ℝ ⊤ (fun _ : Spacetime3 => (0 : Space3)) (global_spacetime_domain 3)
    fun_prop
  intro α m K
  refine ⟨1, by norm_num, ?_⟩
  intro x hx_nonneg
  rw [spacetime_derivative_vector_zero, norm_zero]
  positivity

/-- Fefferman's smoothness condition (6) for a solution `(p,u)` on `ℝ³ × [0,∞)`. -/
def SmoothSolutionFields (u : VelocityField 3) (p : PressureField 3) : Prop :=
  velocity_smooth_on_global_spacetime_domain u ∧ pressure_smooth_on_global_spacetime_domain p

/-- A `GlobalSmoothSolution` automatically satisfies Fefferman's smoothness condition (6). -/
theorem GlobalSmoothSolution.smooth_fields {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse) : SmoothSolutionFields sol.velocity sol.pressure :=
  ⟨sol.velocity_smooth, sol.pressure_smooth⟩

/-- Fefferman's bounded-energy condition (7) for a velocity field `u`. -/
def FiniteEnergy (u : VelocityField 3) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 0 ≤ t →
      HasFiniteIntegral (fun x : Space3 => ∑ i : Fin 3, (u (spacetime_point t x) i) ^ 2) ∧
        energy_integral u t < C

/-! ## Fefferman's statements (A) and (C) -/

/-- Navier–Stokes equations on `ℝ³` for given `ν`, initial data, and forcing. -/
def equations (ν : ℝ) (ν_pos : ν > 0) (u₀ : InitialVelocity) (u₀_div : DivergenceFreeInitial u₀)
    (f : ForceField 3) : NavierStokesEquations 3 :=
  { viscosity := ν
    external_force := f
    viscosity_positive := ν_pos
    initial_velocity := u₀
    initial_divergence_free := u₀_div }

/--
Fefferman's statement (A): Existence and smoothness on `ℝ³`, with `f ≡ 0`.

This asks for a global smooth solution on `ℝ³ × [0,∞)` satisfying (6) and (7), for every smooth
divergence-free initial velocity satisfying (4).
-/
def SmoothExistence : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0) (u₀ : InitialVelocity),
    SmoothRapidDecayInitial u₀ →
      ∀ hdiv : DivergenceFreeInitial u₀,
      ∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun _ => 0)),
        SmoothSolutionFields sol.velocity sol.pressure ∧ FiniteEnergy sol.velocity

/--
In statement (A), condition (6) is already part of `GlobalSmoothSolution`; the substantive extra
solution-side condition is the bounded energy condition (7).
-/
theorem SmoothExistence.iff_finite_energy :
    SmoothExistence ↔
      ∀ (ν : ℝ) (ν_pos : ν > 0) (u₀ : InitialVelocity),
        SmoothRapidDecayInitial u₀ →
        ∀ hdiv : DivergenceFreeInitial u₀,
          ∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun _ => 0)),
            FiniteEnergy sol.velocity := by
  constructor
  · intro hA ν ν_pos u₀ h4 hdiv
    rcases hA ν ν_pos u₀ h4 hdiv with ⟨sol, _h6, h7⟩
    exact ⟨sol, h7⟩
  · intro hA ν ν_pos u₀ h4 hdiv
    rcases hA ν ν_pos u₀ h4 hdiv with ⟨sol, h7⟩
    exact ⟨sol, GlobalSmoothSolution.smooth_fields sol, h7⟩

/--
Fefferman's statement (C): Breakdown on `ℝ³` (forcing allowed).

For any fixed viscosity `ν > 0`, there exist smooth data `u₀,f` satisfying (4) and (5) for which
there is **no** global smooth solution on `ℝ³ × [0,∞)` satisfying (6) and (7).
-/
def Breakdown : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0),
  ∃ (u₀ : InitialVelocity) (f : SpacetimeForce),
    SmoothRapidDecayInitial u₀ ∧
    DivergenceFreeInitial u₀ ∧
    SmoothRapidDecayForce f ∧
      ∀ hdiv : DivergenceFreeInitial u₀,
        ¬ (∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun x => f x)),
              SmoothSolutionFields sol.velocity sol.pressure ∧ FiniteEnergy sol.velocity)

/--
In statement (C), condition (6) is automatic for `GlobalSmoothSolution`, so the nonexistence clause
can equivalently rule out global smooth finite-energy solutions.
-/
theorem Breakdown.iff_no_finite_energy_solution :
    Breakdown ↔
      ∀ (ν : ℝ) (ν_pos : ν > 0),
      ∃ (u₀ : InitialVelocity) (f : SpacetimeForce),
        SmoothRapidDecayInitial u₀ ∧
        DivergenceFreeInitial u₀ ∧
        SmoothRapidDecayForce f ∧
          ∀ hdiv : DivergenceFreeInitial u₀,
            ¬ (∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun x => f x)),
                  FiniteEnergy sol.velocity) := by
  constructor
  · intro hC ν ν_pos
    rcases hC ν ν_pos with ⟨u₀, f, h4, hdiv₀, h5, hNo⟩
    refine ⟨u₀, f, h4, hdiv₀, h5, ?_⟩
    intro hdiv hExists
    apply hNo hdiv
    rcases hExists with ⟨sol, h7⟩
    exact ⟨sol, GlobalSmoothSolution.smooth_fields sol, h7⟩
  · intro hC ν ν_pos
    rcases hC ν ν_pos with ⟨u₀, f, h4, hdiv₀, h5, hNo⟩
    refine ⟨u₀, f, h4, hdiv₀, h5, ?_⟩
    intro hdiv hExists
    apply hNo hdiv
    rcases hExists with ⟨sol, _h6, h7⟩
    exact ⟨sol, h7⟩

end NavierStokesOnR3
open EuclideanSpace MeasureTheory Order NavierStokes

/-!
`ThreeTorus` is implemented as the Mathlib product torus `(ℝ/ℤ)³`.

The PDE operators in the Navier--Stokes files are still written on coordinate lifts `ℝ³` or
`ℝ³ × [0,∞)`. The maps below connect those lifted statements to the actual quotient torus used
for Clay's periodic domain `ℝ³/ℤ³`.
-/

/-- Clay's periodic spatial domain `ℝ³/ℤ³`, as a product of three unit additive circles. -/
def ThreeTorus : Type :=
  UnitAddTorus (Fin 3)

/-- The quotient map from coordinates on `ℝ³` to the torus `(ℝ/ℤ)³`. -/
noncomputable def torus_quotient_map (x : Space3) : ThreeTorus :=
  fun i => (x i : UnitAddCircle)

@[simp] theorem torus_quotient_map_apply (x : Space3) (i : Fin 3) :
    torus_quotient_map x i = (x i : UnitAddCircle) :=
  rfl

/-- Integer coordinates vanish in `ℝ/ℤ`. -/
@[simp] theorem unit_add_circle_int_cast_eq_zero (n : ℤ) :
    ((n : ℝ) : UnitAddCircle) = 0 := by
  simp

/-- The coordinate quotient map is unchanged by integer shifts in any standard basis direction. -/
@[simp] theorem torus_quotient_map_add_int_standard_basis
    (x : Space3) (i : Fin 3) (n : ℤ) :
    torus_quotient_map (x + n • standard_basis (n := 3) i) = torus_quotient_map x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [torus_quotient_map]
  · simp [torus_quotient_map, hji]

/-- The coordinate lift of a function on the quotient torus. -/
noncomputable def torus_lift {α : Type*} (F : ThreeTorus → α) : Space3 → α :=
  fun x => F (torus_quotient_map x)

/-- A coordinate function factors through the quotient torus if it is a torus lift. -/
def factors_through_torus {α : Type*} (f : Space3 → α) : Prop :=
  ∃ F : ThreeTorus → α, f = torus_lift F

/-- Every torus lift factors through the quotient torus. -/
theorem torus_lift_factors_through_torus {α : Type*} (F : ThreeTorus → α) :
    factors_through_torus (torus_lift F) :=
  ⟨F, rfl⟩
namespace NavierStokesPeriodic

open EuclideanSpace MeasureTheory Order NavierStokes
open NavierStokesOnR3
open scoped BigOperators

/-!
# Navier–Stokes Millennium problem: periodic setting (`ℝ³/ℤ³`)

This file states Fefferman's parts (B) and (D) from the Clay problem description
`Problems/NavierStokes/references/clay/navierstokes.pdf`.

The periodic hypotheses are numbered (8)–(11) in the PDF.
-/

/-- Periodicity in each coordinate direction with period `1`. -/
def IsPeriodic {α : Type} (f : Space3 → α) : Prop :=
  ∀ (x : Space3) (i : Fin 3) (n : ℤ),
    let e_i : Space3 := standard_basis (n := 3) i
    f (x + n • e_i) = f x

/-- A function on the quotient torus pulls back to a `ℤ³`-periodic coordinate function. -/
theorem IsPeriodic.torus_lift {α : Type} (F : ThreeTorus → α) :
    IsPeriodic (torus_lift F) := by
  intro x i n
  change F (torus_quotient_map (x + n • standard_basis (n := 3) i)) = F (torus_quotient_map x)
  rw [torus_quotient_map_add_int_standard_basis]

/-- Spatial periodicity (in the `ℝ³` directions) for a spacetime function `ℝ⁴ → _`. -/
def IsSpatiallyPeriodicForce (f : ForceField 3) : Prop :=
  ∀ (x : Spacetime3), 0 ≤ x 0 → ∀ (i : Fin 3) (n : ℤ),
    let e_i : Spacetime3 := standard_basis (n := 4) i.succ
    f (x + n • e_i) = f x

/-- Spatial periodicity (in the `ℝ³` directions) for a pressure field `ℝ⁴ → ℝ`. -/
def IsSpatiallyPeriodicPressure (p : PressureField 3) : Prop :=
  ∀ (x : Spacetime3), 0 ≤ x 0 → ∀ (i : Fin 3) (n : ℤ),
    let e_i : Spacetime3 := standard_basis (n := 4) i.succ
    p (x + n • e_i) = p x

/-! ## Fefferman's conditions (8)–(11) -/

/--
Fefferman's periodicity condition (8) for an initial velocity field on `ℝ³`.
-/
def PeriodicInitial (u₀ : Space3 → Space3) : Prop :=
  IsPeriodic u₀

/-- Fefferman's periodicity condition (8) for a force field on `ℝ³ × [0,∞)`. -/
def PeriodicForce (f : ForceField 3) : Prop :=
  IsSpatiallyPeriodicForce f

/-- The zero force is spatially periodic. -/
theorem zero_force_periodic :
    PeriodicForce (fun _ : Spacetime3 => (0 : Space3)) := by
  intro x _hx i n
  rfl

/--
Fefferman's time-decay condition (9) for the force in the periodic setting.

This is the same mixed-derivative expression as in (5), but the weight depends only on time.
-/
def PeriodicForceDecay (f : ForceField 3) : Prop :=
  force_smooth_on_global_spacetime_domain f ∧
    ∀ (α : List (Fin 3)) (m K : ℕ),
      ∃ C : ℝ, 0 < C ∧
        ∀ x : Spacetime3, 0 ≤ x 0 →
          ‖spacetime_derivative_vector f α m x‖ ≤ C / (1 + |x 0|) ^ K

/-- The zero force satisfies Fefferman's periodic-setting force decay condition (9). -/
theorem zero_force_periodic_decay :
    PeriodicForceDecay (fun _ : Spacetime3 => (0 : Space3)) := by
  refine ⟨?_, ?_⟩
  · change ContDiffOn ℝ ⊤ (fun _ : Spacetime3 => (0 : Space3)) (global_spacetime_domain 3)
    fun_prop
  intro α m K
  refine ⟨1, by norm_num, ?_⟩
  intro x hx_nonneg
  rw [spacetime_derivative_vector_zero, norm_zero]
  positivity

/--
Fefferman's periodicity condition (10) in the periodic setting.

The main text states periodicity for the velocity field `u` in (10); the local PDF errata says
pressure periodicity should also be made explicit in the periodic setting.
-/
def PeriodicSolutionFields (u : VelocityField 3) (p : PressureField 3) : Prop :=
  (∀ t : ℝ, 0 ≤ t → IsPeriodic (fun x : Space3 => u (spacetime_point t x))) ∧
    IsSpatiallyPeriodicPressure p

/-- Fefferman's smoothness condition (11) for a solution `(p,u)` on `ℝ³ × [0,∞)`. -/
def SmoothPeriodicSolutionFields (u : VelocityField 3) (p : PressureField 3) : Prop :=
  velocity_smooth_on_global_spacetime_domain u ∧ pressure_smooth_on_global_spacetime_domain p

/-- A `GlobalSmoothSolution` automatically satisfies Fefferman's smoothness condition (11). -/
theorem GlobalSmoothSolution.smooth_periodic_fields {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse) : SmoothPeriodicSolutionFields sol.velocity sol.pressure :=
  ⟨sol.velocity_smooth, sol.pressure_smooth⟩

/-! ## Fefferman's statements (B) and (D) -/

/--
Fefferman's statement (B): Existence and smoothness in the periodic setting, with `f ≡ 0`.
-/
def SmoothExistence : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0) (u₀ : Space3 → Space3),
    ContDiff ℝ ⊤ u₀ →
    PeriodicInitial u₀ →
      ∀ hdiv : DivergenceFreeInitial u₀,
      ∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun _ => 0)),
        PeriodicSolutionFields sol.velocity sol.pressure ∧
          SmoothPeriodicSolutionFields sol.velocity sol.pressure

/--
In statement (B), condition (11) is already part of `GlobalSmoothSolution`; the substantive extra
solution-side condition is periodicity (10).
-/
theorem SmoothExistence.iff_periodic_fields :
    SmoothExistence ↔
      ∀ (ν : ℝ) (ν_pos : ν > 0) (u₀ : Space3 → Space3),
        ContDiff ℝ ⊤ u₀ →
        PeriodicInitial u₀ →
        ∀ hdiv : DivergenceFreeInitial u₀,
          ∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun _ => 0)),
            PeriodicSolutionFields sol.velocity sol.pressure := by
  constructor
  · intro hB ν ν_pos u₀ hSmooth hPeriodic hdiv
    rcases hB ν ν_pos u₀ hSmooth hPeriodic hdiv with ⟨sol, h10, _h11⟩
    exact ⟨sol, h10⟩
  · intro hB ν ν_pos u₀ hSmooth hPeriodic hdiv
    rcases hB ν ν_pos u₀ hSmooth hPeriodic hdiv with ⟨sol, h10⟩
    exact ⟨sol, h10, GlobalSmoothSolution.smooth_periodic_fields sol⟩

/--
Fefferman's statement (D): Breakdown in the periodic setting (forcing allowed).
-/
def Breakdown : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0),
  ∃ (u₀ : Space3 → Space3) (f : ForceField 3),
    ContDiff ℝ ⊤ u₀ ∧
    PeriodicInitial u₀ ∧
    DivergenceFreeInitial u₀ ∧
    PeriodicForce f ∧
    PeriodicForceDecay f ∧
      ∀ hdiv : DivergenceFreeInitial u₀,
        ¬ (∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv f),
              PeriodicSolutionFields sol.velocity sol.pressure ∧
                SmoothPeriodicSolutionFields sol.velocity sol.pressure)

/--
In statement (D), condition (11) is automatic for `GlobalSmoothSolution`, so the nonexistence
clause can equivalently rule out global smooth periodic solutions.
-/
theorem Breakdown.iff_no_periodic_solution :
    Breakdown ↔
      ∀ (ν : ℝ) (ν_pos : ν > 0),
      ∃ (u₀ : Space3 → Space3) (f : ForceField 3),
        ContDiff ℝ ⊤ u₀ ∧
        PeriodicInitial u₀ ∧
        DivergenceFreeInitial u₀ ∧
        PeriodicForce f ∧
        PeriodicForceDecay f ∧
          ∀ hdiv : DivergenceFreeInitial u₀,
            ¬ (∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv f),
                  PeriodicSolutionFields sol.velocity sol.pressure) := by
  constructor
  · intro hD ν ν_pos
    rcases hD ν ν_pos with ⟨u₀, f, hSmooth, hPeriodic₀, hdiv₀, hPeriodicf, h9, hNo⟩
    refine ⟨u₀, f, hSmooth, hPeriodic₀, hdiv₀, hPeriodicf, h9, ?_⟩
    intro hdiv hExists
    apply hNo hdiv
    rcases hExists with ⟨sol, h10⟩
    exact ⟨sol, h10, GlobalSmoothSolution.smooth_periodic_fields sol⟩
  · intro hD ν ν_pos
    rcases hD ν ν_pos with ⟨u₀, f, hSmooth, hPeriodic₀, hdiv₀, hPeriodicf, h9, hNo⟩
    refine ⟨u₀, f, hSmooth, hPeriodic₀, hdiv₀, hPeriodicf, h9, ?_⟩
    intro hdiv hExists
    apply hNo hdiv
    rcases hExists with ⟨sol, h10, _h11⟩
    exact ⟨sol, h10⟩

end NavierStokesPeriodic
/-!
# Navier–Stokes Millennium problem (Fefferman)

Top-level statement for Clay Navier--Stokes, following:
`Problems/NavierStokes/references/clay/navierstokes.pdf`.

Fefferman's accepted Clay cases are formalized directly as:
- `NavierStokesOnR3.SmoothExistence`
- `NavierStokesPeriodic.SmoothExistence`
- `NavierStokesOnR3.Breakdown`
- `NavierStokesPeriodic.Breakdown`

This file just packages those four cases into the single public Clay proposition.
-/

namespace MillenniumNavierStokes

/-- Clay's Navier--Stokes statement: prove one of Fefferman's cases (A)--(D). -/
def ClayNavierStokes : Prop :=
  NavierStokesOnR3.SmoothExistence ∨ NavierStokesPeriodic.SmoothExistence ∨
    NavierStokesOnR3.Breakdown ∨ NavierStokesPeriodic.Breakdown

/-- `ClayNavierStokes` is exactly the disjunction of Fefferman's four accepted cases. -/
theorem ClayNavierStokes.iff_cases :
    ClayNavierStokes ↔
      NavierStokesOnR3.SmoothExistence ∨ NavierStokesPeriodic.SmoothExistence ∨
        NavierStokesOnR3.Breakdown ∨ NavierStokesPeriodic.Breakdown :=
  Iff.rfl

/-- Whole-space smooth existence proves the Clay statement. -/
theorem ClayNavierStokes.of_whole_space_smooth_existence
    (h : NavierStokesOnR3.SmoothExistence) :
    ClayNavierStokes :=
  Or.inl h

/-- Periodic smooth existence proves the Clay statement. -/
theorem ClayNavierStokes.of_periodic_smooth_existence
    (h : NavierStokesPeriodic.SmoothExistence) :
    ClayNavierStokes :=
  Or.inr (Or.inl h)

/-- Whole-space breakdown proves the Clay statement. -/
theorem ClayNavierStokes.of_whole_space_breakdown
    (h : NavierStokesOnR3.Breakdown) :
    ClayNavierStokes :=
  Or.inr (Or.inr (Or.inl h))

/-- Periodic breakdown proves the Clay statement. -/
theorem ClayNavierStokes.of_periodic_breakdown
    (h : NavierStokesPeriodic.Breakdown) :
    ClayNavierStokes :=
  Or.inr (Or.inr (Or.inr h))

/-- Case analysis on `ClayNavierStokes` using the four accepted Fefferman cases directly. -/
theorem ClayNavierStokes.elim
    {P : Prop} (h : ClayNavierStokes)
    (hA : NavierStokesOnR3.SmoothExistence → P)
    (hB : NavierStokesPeriodic.SmoothExistence → P)
    (hC : NavierStokesOnR3.Breakdown → P)
    (hD : NavierStokesPeriodic.Breakdown → P) :
    P := by
  rcases h with hA' | hBCD
  · exact hA hA'
  rcases hBCD with hB' | hCD
  · exact hB hB'
  rcases hCD with hC' | hD'
  · exact hC hC'
  · exact hD hD'


end MillenniumNavierStokes
