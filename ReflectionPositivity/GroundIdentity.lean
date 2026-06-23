/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.GroundSemigroup
import ReflectionPositivity.MultiplicationCLM

/-!
# Exact GNS / ground-state two-point identity

Piece E0 of the GNS / ground-state-transform construction.

The only ingredients are `W`, its Hilbert adjoint `W†`, and Piece C's
`U_t = W† ∘ T̂^t ∘ W`; no spectral gap hypothesis is used. Since Piece A
currently gives `W` as an isometry rather than a unitary equivalence, the
unconditional identity keeps the range projection `W W†`. The unprojected
identity is also stated under the explicit right-inverse hypothesis
`W W† = id`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace ReflectionPositivity

variable {S : Type*} [MeasurableSpace S]

namespace MultiplicationCLMContract

variable {ν : Measure S}

/-- Transport a multiplication operator to `L²(μ_Ω)` as `W† M W`. -/
noncomputable def M_on_ground_via_W (C : MultiplicationCLMContract ν)
    (D : GroundSemigroupData ν) : Lp ℝ 2 D.μΩ →L[ℝ] Lp ℝ 2 D.μΩ :=
  D.WAdjoint.comp (C.M.comp D.W)

@[simp] theorem M_on_ground_via_W_apply (C : MultiplicationCLMContract ν)
    (D : GroundSemigroupData ν) (f : Lp ℝ 2 D.μΩ) :
    C.M_on_ground_via_W D f = D.WAdjoint (C.M (D.W f)) := rfl

end MultiplicationCLMContract

namespace GroundSemigroupData

variable {ν : Measure S} (D : GroundSemigroupData ν)

/-- The range projection `W W†`, which becomes `id` after the unitary upgrade. -/
noncomputable def WProjection : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  D.W.comp D.WAdjoint

@[simp] theorem WProjection_apply (f : Lp ℝ 2 ν) :
    D.WProjection f = D.W (D.WAdjoint f) := rfl

/-- Applying `W` after a transported multiplication operator gives the
projected original multiplication operator. -/
theorem W_M_on_ground_via_W (C : MultiplicationCLMContract ν)
    (f : Lp ℝ 2 D.μΩ) :
    D.W (C.M_on_ground_via_W D f) = D.WProjection (C.M (D.W f)) := rfl

/-- Under `W W† = id`, transported multiplication conjugates exactly. -/
theorem W_M_on_ground_via_W_of_WAdjoint_rightInverse
    (hW : ∀ f : Lp ℝ 2 ν, D.W (D.WAdjoint f) = f)
    (C : MultiplicationCLMContract ν) (f : Lp ℝ 2 D.μΩ) :
    D.W (C.M_on_ground_via_W D f) = C.M (D.W f) := by
  rw [D.W_M_on_ground_via_W, WProjection_apply, hW]

/-- **Exact adjoint-compressed GNS identity.** This is the no-gap,
unconditional form available from the current Piece A-C API; the two
`WProjection` factors are the missing `W W† = id` reductions. -/
theorem groundSemigroup_two_point_eq_lift_projected
    (MA MB : MultiplicationCLMContract ν) (t : ℕ) :
    inner ℝ D.one
        ((MA.M_on_ground_via_W D)
          (D.groundSemigroup t ((MB.M_on_ground_via_W D) D.one)))
      =
      inner ℝ D.omegaL2
        (MA.M
          (D.WProjection
            ((D.normalizedTransfer ^ t) (D.WProjection (MB.M D.omegaL2))))) := by
  calc
    inner ℝ D.one
        ((MA.M_on_ground_via_W D)
          (D.groundSemigroup t ((MB.M_on_ground_via_W D) D.one)))
        =
        inner ℝ (D.W D.one)
          (MA.M (D.W (D.groundSemigroup t ((MB.M_on_ground_via_W D) D.one)))) := by
          rw [MultiplicationCLMContract.M_on_ground_via_W_apply]
          exact ContinuousLinearMap.adjoint_inner_right D.W D.one
            (MA.M (D.W (D.groundSemigroup t ((MB.M_on_ground_via_W D) D.one))))
    _ =
        inner ℝ D.omegaL2
          (MA.M
            (D.WProjection
              ((D.normalizedTransfer ^ t)
                (D.W ((MB.M_on_ground_via_W D) D.one))))) := by
          rw [D.W_one, D.groundSemigroup_apply, D.WProjection_apply]
    _ =
        inner ℝ D.omegaL2
          (MA.M
            (D.WProjection
              ((D.normalizedTransfer ^ t)
                (D.WProjection (MB.M (D.W D.one)))))) := by
          rw [D.W_M_on_ground_via_W]
    _ =
        inner ℝ D.omegaL2
          (MA.M
            (D.WProjection
              ((D.normalizedTransfer ^ t) (D.WProjection (MB.M D.omegaL2))))) := by
          rw [D.W_one]

/-- **Exact GNS / ground-state identity under `W W† = id`.** This is the
normalized-transfer version of

`⟪1, M_A U_t M_B 1⟫ = (1 / λ₀^t) * ⟪Ω, M_A T^t M_B Ω⟫`.

The extra assumption is the right-inverse half of the planned unitary upgrade,
not a gap hypothesis. -/
theorem groundSemigroup_two_point_eq_lift
    (hW : ∀ f : Lp ℝ 2 ν, D.W (D.WAdjoint f) = f)
    (MA MB : MultiplicationCLMContract ν) (t : ℕ) :
    inner ℝ D.one
        ((MA.M_on_ground_via_W D)
          (D.groundSemigroup t ((MB.M_on_ground_via_W D) D.one)))
      =
      inner ℝ D.omegaL2 (MA.M ((D.normalizedTransfer ^ t) (MB.M D.omegaL2))) := by
  rw [D.groundSemigroup_two_point_eq_lift_projected MA MB t]
  simp [WProjection_apply, hW]

end GroundSemigroupData

/-- Top-level convenience form of
`GroundSemigroupData.groundSemigroup_two_point_eq_lift`. -/
theorem groundSemigroup_two_point_eq_lift
    {ν : Measure S} (D : GroundSemigroupData ν)
    (hW : ∀ f : Lp ℝ 2 ν, D.W (D.WAdjoint f) = f)
    (MA MB : MultiplicationCLMContract ν) (t : ℕ) :
    inner ℝ D.one
        ((MA.M_on_ground_via_W D)
          (D.groundSemigroup t ((MB.M_on_ground_via_W D) D.one)))
      =
      inner ℝ D.omegaL2 (MA.M ((D.normalizedTransfer ^ t) (MB.M D.omegaL2))) :=
  D.groundSemigroup_two_point_eq_lift hW MA MB t

end ReflectionPositivity
