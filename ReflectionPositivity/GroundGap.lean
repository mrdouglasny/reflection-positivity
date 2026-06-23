/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.GroundMeasure
import ReflectionPositivity.TransferMatrix

/-!
# Spectral gap after the ground-state transform

Piece D of the GNS / ground-state-transform construction.

The ground-state isometry
`W : L²(groundMeasure ν Ω) →ₗᵢ[ℝ] L²(ν)`, `W f = f · Ω`, transports the
vacuum-orthogonal complement of the constant-one vector in `L²(μ_Ω)` to the
`Ω`-orthogonal complement in `L²(ν)`. Consequently, any spectral gap for the
normalized transfer on `L²(ν)` immediately gives the same geometric decay for
the ground semigroup `U_t`, provided `U_t` is intertwined with the normalized
transfer by `W`.

This file deliberately does not construct `U_t`; Piece C supplies that
construction. Here we package only the data needed for the gap inheritance:
the `L²(ν)` `GappedTransfer`, the family `U_t` on `L²(μ_Ω)`, and the
intertwining equation

`W (U_t f) = T̂^t (W f)`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace ReflectionPositivity

variable {S : Type*} [MeasurableSpace S]

section GroundOne

variable {ν : Measure S} {Ω : S → ℝ} [IsFiniteMeasure (groundMeasure ν Ω)]

/-- The constant-one vector in `L²(groundMeasure ν Ω)`. -/
noncomputable def groundOne : Lp ℝ 2 (groundMeasure ν Ω) :=
  Lp.const 2 (groundMeasure ν Ω) (1 : ℝ)

/-- The `L²(ν)` vacuum vector obtained by applying the ground-state isometry to
the constant-one vector in `L²(groundMeasure ν Ω)`. This is the formal
`Ω_L²`; pointwise it is represented by `Ω` wherever the ground-state transform
identifies representatives. -/
noncomputable def groundVacuum (hΩ_meas : Measurable Ω) : Lp ℝ 2 ν :=
  groundIsometry hΩ_meas (groundOne (ν := ν) (Ω := Ω))

/-- The ground-state isometry transports the `1`-orthogonality condition in
`L²(μ_Ω)` to `Ω`-orthogonality in `L²(ν)`. -/
theorem groundIsometry_perp_iff (hΩ_meas : Measurable Ω)
    (f : Lp ℝ 2 (groundMeasure ν Ω)) :
    inner ℝ (groundOne (ν := ν) (Ω := Ω)) f = 0 ↔
      inner ℝ (groundVacuum (ν := ν) (Ω := Ω) hΩ_meas) (groundIsometry hΩ_meas f) = 0 := by
  rw [groundVacuum, (groundIsometry hΩ_meas).inner_map_map]

end GroundOne

/-- Data needed to inherit the normalized-transfer gap through the
ground-state transform.

`transfer` is the normalized transfer `T̂` on `L²(ν)`, packaged as an existing
`GappedTransfer`. Its vacuum is required to be the `L²(ν)` image of the
constant-one vector under `groundIsometry`. The family `groundSemigroup t` is
the ground-state-transform semigroup `U_t`, supplied by Piece C or by any
downstream construction, and `intertwines` records `W U_t = T̂^t W`. -/
structure GroundGapData (ν : Measure S) (Ω : S → ℝ)
    [IsFiniteMeasure (groundMeasure ν Ω)] where
  /-- Measurability of the ground-state function. -/
  omega_meas : Measurable Ω
  /-- The normalized transfer on `L²(ν)`, with its spectral gap. -/
  transfer : GappedTransfer (Lp ℝ 2 ν)
  /-- The transfer vacuum is the image of the constant-one ground vector. -/
  vacuum_eq_ground :
    transfer.vacuum = groundVacuum (ν := ν) (Ω := Ω) omega_meas
  /-- The ground-state semigroup `U_t` on `L²(μ_Ω)`. -/
  groundSemigroup :
    ℕ → Lp ℝ 2 (groundMeasure ν Ω) →L[ℝ] Lp ℝ 2 (groundMeasure ν Ω)
  /-- Intertwining with the normalized transfer:
  `W (U_t f) = T̂^t (W f)`. -/
  intertwines : ∀ t f,
    groundIsometry omega_meas (groundSemigroup t f)
      = (transfer.T ^ t) (groundIsometry omega_meas f)

namespace GroundGapData

variable {ν : Measure S} {Ω : S → ℝ} [IsFiniteMeasure (groundMeasure ν Ω)]
variable (D : GroundGapData ν Ω)

/-- The `L²(ν)` gap parameter inherited by the ground semigroup. -/
abbrev gap : ℝ := D.transfer.gap

/-- Orthogonality to `1` in `L²(μ_Ω)` is orthogonality to the packaged transfer
vacuum after applying the ground-state isometry. -/
theorem transfer_perp_of_ground_perp {f : Lp ℝ 2 (groundMeasure ν Ω)}
    (hf : inner ℝ (groundOne (ν := ν) (Ω := Ω)) f = 0) :
    inner ℝ D.transfer.vacuum (groundIsometry D.omega_meas f) = 0 := by
  rw [D.vacuum_eq_ground]
  exact (groundIsometry_perp_iff (ν := ν) (Ω := Ω) D.omega_meas f).1 hf

/-- **Gap on the `1`-orthogonal complement.** If `f ⊥ 1` in
`L²(groundMeasure ν Ω)`, then the ground-state semigroup decays with the same
geometric rate as the normalized transfer on `L²(ν)`. -/
theorem groundSemigroup_pow_norm_le_of_perp
    {f : Lp ℝ 2 (groundMeasure ν Ω)}
    (hf : inner ℝ (groundOne (ν := ν) (Ω := Ω)) f = 0) (t : ℕ) :
    ‖D.groundSemigroup t f‖ ≤ D.gap ^ t * ‖f‖ := by
  calc
    ‖D.groundSemigroup t f‖
        = ‖groundIsometry D.omega_meas (D.groundSemigroup t f)‖ := by
          rw [(groundIsometry D.omega_meas).norm_map]
    _ = ‖(D.transfer.T ^ t) (groundIsometry D.omega_meas f)‖ := by
          rw [D.intertwines]
    _ ≤ D.transfer.gap ^ t * ‖groundIsometry D.omega_meas f‖ :=
          D.transfer.norm_T_pow_le (D.transfer_perp_of_ground_perp hf) t
    _ = D.gap ^ t * ‖f‖ := by
          rw [(groundIsometry D.omega_meas).norm_map]

end GroundGapData

/-- Top-level convenience form of `GroundGapData.groundSemigroup_pow_norm_le_of_perp`. -/
theorem groundSemigroup_pow_norm_le_of_perp
    {ν : Measure S} {Ω : S → ℝ} [IsFiniteMeasure (groundMeasure ν Ω)]
    (D : GroundGapData ν Ω) {f : Lp ℝ 2 (groundMeasure ν Ω)}
    (hf : inner ℝ (groundOne (ν := ν) (Ω := Ω)) f = 0) (t : ℕ) :
    ‖D.groundSemigroup t f‖ ≤ D.gap ^ t * ‖f‖ :=
  D.groundSemigroup_pow_norm_le_of_perp hf t

end ReflectionPositivity
