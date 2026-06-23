/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.GroundMeasure
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Ground-state Markov time maps

Piece C of the GNS / ground-state-transform construction.

This file packages the hypotheses for a bounded transfer operator `T` on
`L²(ν)`, a strictly positive normalized ground-state density `Ω`, and a
positive top eigenvalue `λ₀`. It then defines the ground-state time maps on
`L²(μ_Ω)`, where `μ_Ω = Ω² · dν`.

## Design choice

Piece A currently provides the forward isometry

`W : L²(μ_Ω) →ₗᵢ[ℝ] L²(ν)`, `W f = f · Ω`,

but not yet its surjective `LinearIsometryEquiv` form. Therefore this file
implements the time maps by adjoint transport:

`U_t := W† ∘ ((1 / λ₀) • T)^t ∘ W`.

When the planned `Ω > 0` a.e. surjectivity upgrade is added, `W†` agrees with
`W⁻¹` and this is exactly the usual Doob/GNS formula
`U_t f = λ₀^{-t} · T^t(f Ω) / Ω`. The adjoint-transport form is already enough
for the two essential Piece C facts:

* `U_t 1 = 1` from the top-eigenvector equation.
* `‖U_t‖ ≤ 1` from the normalized-transfer contraction.

The semigroup law is intentionally not stated here: with only an isometric
embedding, `W W†` is the projection onto `range W`, so `U_t U_s = U_{t+s}`
requires either the forthcoming unitary upgrade or an explicit `T`-invariance
of `range W`.
-/

open MeasureTheory

namespace ReflectionPositivity

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {S : Type*} [MeasurableSpace S]

/-! ## Hypotheses for the adjoint-transport time maps -/

/-- Hypotheses for the ground-state Markov time maps.

The field `hT_normContract` is the substantive contraction assumption:
the normalized transfer operator `(1 / λ₀) • T` is norm-nonincreasing on
`L²(ν)`. The pointwise positivity and normalization of `Ω` are retained in
the bundle because they identify `μ_Ω` as the ground-state probability
measure and are the inputs for the later `W`-unitarity upgrade.

The field `omegaL2_eq_W_one` records that the L² ground vector is the Piece A
lift `W 1`. This keeps the Piece C construction independent of the still-open
surjectivity/division-by-`Ω` upgrade. -/
structure GroundSemigroupData (ν : Measure S) where
  /-- The pointwise ground state. -/
  Ω : S → ℝ
  /-- The pointwise ground state is measurable. -/
  Ω_meas : Measurable Ω
  /-- The pointwise ground state is strictly positive `ν`-a.e. -/
  Ω_pos_ae : ∀ᵐ x ∂ν, 0 < Ω x
  /-- L²-normalization, equivalently total mass one for `μ_Ω`. -/
  Ω_norm : ∫ x, Ω x ^ 2 ∂ν = 1
  /-- The lifted ground vector in `L²(ν)`. -/
  omegaL2 : Lp ℝ 2 ν
  /-- The lifted ground vector has pointwise representative `Ω`, `ν`-a.e. -/
  omegaL2_coeFn : (omegaL2 : S → ℝ) =ᵐ[ν] Ω
  /-- The transfer operator on `L²(ν)`. -/
  T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν
  /-- The top eigenvalue. -/
  lambda0 : ℝ
  /-- The top eigenvalue is positive. -/
  lambda0_pos : 0 < lambda0
  /-- The lifted ground state is a `T`-eigenvector with eigenvalue `λ₀`. -/
  hΩ_eigen : T omegaL2 = lambda0 • omegaL2
  /-- The normalized transfer `(1 / λ₀) • T` is a contraction on `L²(ν)`. -/
  hT_normContract : ∀ f : Lp ℝ 2 ν, ‖((1 / lambda0) • T) f‖ ≤ ‖f‖
  /-- The lifted ground vector is exactly `W 1`, where `1` is formed using
  the probability measure proof from `Ω_norm`. -/
  omegaL2_eq_W_one :
    (letI : IsProbabilityMeasure (groundMeasure ν Ω) :=
      groundMeasure_isProbabilityMeasure ν Ω Ω_meas Ω_norm
    groundIsometry Ω_meas (Lp.const 2 (groundMeasure ν Ω) (1 : ℝ))) = omegaL2

namespace GroundSemigroupData

variable {ν : Measure S} (D : GroundSemigroupData ν)

/-- The ground-state measure associated to the packaged data. -/
noncomputable def μΩ : Measure S :=
  groundMeasure ν D.Ω

/-- The ground measure is a probability measure under the packaged
normalization hypothesis. -/
theorem isProbabilityMeasure_μΩ : IsProbabilityMeasure D.μΩ :=
  groundMeasure_isProbabilityMeasure ν D.Ω D.Ω_meas D.Ω_norm

/-- The constant-one vector in `L²(μ_Ω)`. -/
noncomputable def one : Lp ℝ 2 D.μΩ :=
  letI : IsProbabilityMeasure D.μΩ := D.isProbabilityMeasure_μΩ
  Lp.const 2 D.μΩ (1 : ℝ)

/-- The forward ground-state isometry `W : L²(μ_Ω) → L²(ν)`. -/
noncomputable def W : Lp ℝ 2 D.μΩ →L[ℝ] Lp ℝ 2 ν :=
  (groundIsometry D.Ω_meas).toContinuousLinearMap

/-- The Hilbert adjoint `W† : L²(ν) → L²(μ_Ω)`. This is the inverse of `W`
once the `Ω > 0` a.e. surjectivity upgrade is available. -/
noncomputable def WAdjoint : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 D.μΩ :=
  ContinuousLinearMap.adjoint D.W

/-- The normalized transfer operator `T̂ = (1 / λ₀) • T`. -/
noncomputable def normalizedTransfer : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (1 / D.lambda0) • D.T

/-- The ground-state time map
`U_t = W† ∘ ((1 / λ₀) • T)^t ∘ W` on `L²(μ_Ω)`. -/
noncomputable def groundSemigroup (t : ℕ) : Lp ℝ 2 D.μΩ →L[ℝ] Lp ℝ 2 D.μΩ :=
  D.WAdjoint.comp ((D.normalizedTransfer ^ t).comp D.W)

@[simp] theorem W_apply (f : Lp ℝ 2 D.μΩ) :
    D.W f = groundIsometry D.Ω_meas f := rfl

@[simp] theorem W_one : D.W D.one = D.omegaL2 := by
  rw [W, one]
  exact D.omegaL2_eq_W_one

@[simp] theorem normalizedTransfer_apply (f : Lp ℝ 2 ν) :
    D.normalizedTransfer f = ((1 / D.lambda0) • D.T) f := rfl

@[simp] theorem groundSemigroup_apply (t : ℕ) (f : Lp ℝ 2 D.μΩ) :
    D.groundSemigroup t f =
      D.WAdjoint ((D.normalizedTransfer ^ t) (D.W f)) := rfl

/-- `W† W = 1` because `W` is an isometry. -/
theorem WAdjoint_comp_W : D.WAdjoint.comp D.W = ContinuousLinearMap.id ℝ (Lp ℝ 2 D.μΩ) := by
  have hnorm : ∀ f : Lp ℝ 2 D.μΩ, ‖D.W f‖ = ‖f‖ := by
    intro f
    exact (groundIsometry D.Ω_meas).norm_map f
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self D.W).mp hnorm

/-- Pointwise form of `W† (W f) = f`. -/
theorem WAdjoint_W (f : Lp ℝ 2 D.μΩ) : D.WAdjoint (D.W f) = f := by
  have h := congrArg (fun A : Lp ℝ 2 D.μΩ →L[ℝ] Lp ℝ 2 D.μΩ => A f)
    D.WAdjoint_comp_W
  simpa using h

/-- The normalized transfer fixes the lifted ground vector. -/
theorem normalizedTransfer_omegaL2 : D.normalizedTransfer D.omegaL2 = D.omegaL2 := by
  have hlambda : D.lambda0 ≠ 0 := ne_of_gt D.lambda0_pos
  calc
    D.normalizedTransfer D.omegaL2
        = (1 / D.lambda0) • D.T D.omegaL2 := rfl
    _ = (1 / D.lambda0) • (D.lambda0 • D.omegaL2) := by rw [D.hΩ_eigen]
    _ = D.omegaL2 := by
      rw [smul_smul, one_div_mul_cancel hlambda, one_smul]

/-- All iterates of the normalized transfer fix the lifted ground vector. -/
theorem normalizedTransfer_pow_omegaL2 (t : ℕ) :
    (D.normalizedTransfer ^ t) D.omegaL2 = D.omegaL2 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, D.normalizedTransfer_omegaL2]

/-- Iterates of the normalized transfer are contractions. -/
theorem normalizedTransfer_pow_norm_le (t : ℕ) (f : Lp ℝ 2 ν) :
    ‖(D.normalizedTransfer ^ t) f‖ ≤ ‖f‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      exact (D.hT_normContract ((D.normalizedTransfer ^ t) f)).trans ih

/-- The adjoint of `W` is norm-nonincreasing. -/
theorem WAdjoint_norm_le (f : Lp ℝ 2 ν) : ‖D.WAdjoint f‖ ≤ ‖f‖ := by
  let x : Lp ℝ 2 D.μΩ := D.WAdjoint f
  change ‖x‖ ≤ ‖f‖
  by_cases hx : ‖x‖ = 0
  · rw [hx]
    exact norm_nonneg _
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    have hWnorm : ‖D.W x‖ = ‖x‖ := by
      change ‖groundIsometry D.Ω_meas x‖ = ‖x‖
      exact (groundIsometry D.Ω_meas).norm_map x
    have hsq_le : ‖x‖ ^ 2 ≤ ‖f‖ * ‖x‖ := by
      calc
        ‖x‖ ^ 2 = ⟪x, x⟫ := by rw [real_inner_self_eq_norm_sq]
        _ = ⟪D.WAdjoint f, x⟫ := rfl
        _ = ⟪f, D.W x⟫ := ContinuousLinearMap.adjoint_inner_left D.W x f
        _ ≤ |⟪f, D.W x⟫| := le_abs_self _
        _ ≤ ‖f‖ * ‖D.W x‖ := abs_real_inner_le_norm _ _
        _ = ‖f‖ * ‖x‖ := by rw [hWnorm]
    by_contra hnot
    have hf_lt : ‖f‖ < ‖x‖ := lt_of_not_ge hnot
    have hmul_lt : ‖f‖ * ‖x‖ < ‖x‖ * ‖x‖ :=
      mul_lt_mul_of_pos_right hf_lt hxpos
    have hsq_eq : ‖x‖ ^ 2 = ‖x‖ * ‖x‖ := by ring
    rw [hsq_eq] at hsq_le
    linarith

/-- **Markov property.** The ground-state time maps fix the constant vector. -/
theorem groundSemigroup_one (t : ℕ) :
    D.groundSemigroup t D.one = D.one := by
  calc
    D.groundSemigroup t D.one
        = D.WAdjoint ((D.normalizedTransfer ^ t) (D.W D.one)) := rfl
    _ = D.WAdjoint ((D.normalizedTransfer ^ t) D.omegaL2) := by rw [D.W_one]
    _ = D.WAdjoint D.omegaL2 := by rw [D.normalizedTransfer_pow_omegaL2 t]
    _ = D.one := by
      rw [← D.W_one]
      exact D.WAdjoint_W D.one

/-- Pointwise contraction of the ground-state time maps. -/
theorem groundSemigroup_norm_le (t : ℕ) (f : Lp ℝ 2 D.μΩ) :
    ‖D.groundSemigroup t f‖ ≤ ‖f‖ := by
  calc
    ‖D.groundSemigroup t f‖
        = ‖D.WAdjoint ((D.normalizedTransfer ^ t) (D.W f))‖ := rfl
    _ ≤ ‖(D.normalizedTransfer ^ t) (D.W f)‖ := D.WAdjoint_norm_le _
    _ ≤ ‖D.W f‖ := D.normalizedTransfer_pow_norm_le t (D.W f)
    _ = ‖f‖ := by
      exact (groundIsometry D.Ω_meas).norm_map f

/-- **Operator-norm contraction.** `‖U_t‖ ≤ 1` for every `t`. -/
theorem groundSemigroup_opNorm_le (t : ℕ) : ‖D.groundSemigroup t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro f
  simpa using D.groundSemigroup_norm_le t f

end GroundSemigroupData

end ReflectionPositivity
