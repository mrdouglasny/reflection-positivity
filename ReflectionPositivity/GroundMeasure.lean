/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Ground-state distribution

The **ground-state distribution** `μ_Ω := Ω² · dν` associated to a base
measure `ν` and a top-eigenvector `Ω : S → ℝ` of a transfer operator.
This is the natural probability measure for the **ground-state /
Doob `h`-transform** (i.e., GNS) representation of the transfer system —
see `docs/gns-construction-plan.md` for the full route.

This file (Piece A of the GNS construction) provides:

* `groundMeasure ν Ω` — the measure `Ω² · dν` as `ν.withDensity`.
* `groundMeasure_isProbabilityMeasure` — `μ_Ω` is a probability measure
  when `‖Ω‖_{L²(ν)} = 1` (i.e., `∫ Ω² dν = 1`).
* `groundIsometry` — the linear isometry `W : L²(μ_Ω) → L²(ν)`,
  `(W f) := f · Ω`. Bijective (in fact unitary) when `Ω > 0` ν-a.e.
  (the W-unitarity itself is in a follow-up; this file establishes
  the isometric embedding.)

References:
* Doob, *Classical Potential Theory and Its Probabilistic Counterpart*
  Ch. 2 (the `h`-transform).
* Reed, Simon, *Methods of Modern Mathematical Physics II* §XII.1 (GNS).
* `docs/gns-construction-plan.md` for the role this piece plays in
  the path-measure ↔ operator-form bridge.
-/

open MeasureTheory

namespace ReflectionPositivity

variable {S : Type*} [MeasurableSpace S]

/-! ## The ground-state measure `μ_Ω := Ω² · dν` -/

/-- The ground-state distribution `μ_Ω := Ω² · dν` for a base measure `ν`
and a function `Ω : S → ℝ`. Defined via `withDensity` with density
`ENNReal.ofReal (Ω x ^ 2)`. -/
noncomputable def groundMeasure (ν : Measure S) (Ω : S → ℝ) : Measure S :=
  ν.withDensity (fun x => ENNReal.ofReal (Ω x ^ 2))

/-- The mass of the ground measure equals `∫⁻ Ω² dν`. -/
theorem groundMeasure_apply_univ (ν : Measure S) (Ω : S → ℝ) :
    (groundMeasure ν Ω) Set.univ = ∫⁻ x, ENNReal.ofReal (Ω x ^ 2) ∂ν := by
  unfold groundMeasure
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  simp

/-- The ground measure of any measurable set equals the integral of `Ω²` over
that set. -/
theorem groundMeasure_apply (ν : Measure S) (Ω : S → ℝ)
    {s : Set S} (hs : MeasurableSet s) :
    (groundMeasure ν Ω) s = ∫⁻ x in s, ENNReal.ofReal (Ω x ^ 2) ∂ν := by
  unfold groundMeasure
  rw [MeasureTheory.withDensity_apply _ hs]

/-- The ground measure is a probability measure when `Ω` is L²(ν)-normalized
to 1: `∫ Ω² dν = 1`. -/
theorem groundMeasure_isProbabilityMeasure (ν : Measure S) (Ω : S → ℝ)
    (hΩ_meas : Measurable Ω)
    (hΩ_norm : ∫ x, Ω x ^ 2 ∂ν = 1) :
    IsProbabilityMeasure (groundMeasure ν Ω) := by
  refine ⟨?_⟩
  rw [groundMeasure_apply_univ ν Ω]
  -- The Bochner integral hypothesis `∫ Ω² dν = 1` plus pointwise nonnegativity
  -- lifts to the lintegral equality `∫⁻ ENNReal.ofReal (Ω²) dν = 1`.
  have hnonneg : ∀ᵐ x ∂ν, 0 ≤ Ω x ^ 2 :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  have hsm : AEStronglyMeasurable (fun x => Ω x ^ 2) ν :=
    (hΩ_meas.pow_const 2).aestronglyMeasurable
  have h := MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg hsm
  -- `h : ∫ x, Ω x ^ 2 ∂ν = (∫⁻ x, ENNReal.ofReal (Ω x ^ 2) ∂ν).toReal`.
  rw [hΩ_norm] at h
  -- So `1 = (∫⁻ ... ).toReal`, hence the lintegral is finite and equals 1.
  set L : ENNReal := ∫⁻ x, ENNReal.ofReal (Ω x ^ 2) ∂ν
  have hlt : L ≠ ⊤ := by
    intro habs; rw [habs] at h; simp at h
  rw [← ENNReal.ofReal_toReal hlt, ← h, ENNReal.ofReal_one]

/-! ## L²-norm identity (the isometry W's witness equation)

The pointwise function `W f := f · Ω` lifts the L²(μ_Ω) norm-squared
to the L²(ν) norm-squared. This identity is the witness that the
ground-state Hilbert space `L²(μ_Ω)` embeds isometrically into `L²(ν)`
via multiplication by `Ω`. The full `LinearIsometry` packaging is in
a follow-up piece; this file establishes the integral identity.
-/

/-- **L²-norm identity** for the ground-state transform. For any real-valued
function `f`, the L²(μ_Ω)-norm-squared of `f` equals the L²(ν)-norm-squared
of `f · Ω`:

`∫ x, f x ^ 2 ∂(groundMeasure ν Ω) = ∫ x, (f x * Ω x) ^ 2 ∂ν`.

This is the witness equation for the isometry `W : L²(μ_Ω) → L²(ν)`
defined by `W f := f · Ω`. -/
theorem integral_sq_groundMeasure_eq (ν : Measure S) (Ω : S → ℝ)
    (hΩ_meas : Measurable Ω) (f : S → ℝ) :
    ∫ x, f x ^ 2 ∂(groundMeasure ν Ω) = ∫ x, (f x * Ω x) ^ 2 ∂ν := by
  unfold groundMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
        (f := fun x => ENNReal.ofReal (Ω x ^ 2)) (g := fun x => f x ^ 2)
        (ENNReal.measurable_ofReal.comp (hΩ_meas.pow_const 2))
        (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show (ENNReal.ofReal (Ω x ^ 2)).toReal • f x ^ 2 = (f x * Ω x) ^ 2
  rw [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]; ring

end ReflectionPositivity
