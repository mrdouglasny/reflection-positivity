/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Reflection-positive measures: definition and basic API

The abstract setup: a measure `μ` on `(Ω, Σ)` with a measurable
involution `θ : Ω → Ω` preserving `μ`, and a sub-σ-algebra `mPos ⊂ Σ`
("positive-time" observables). The reflection bilinear form is

  `⟨F, G⟩_θ := ∫ F · (G ∘ θ) dμ`,

and `μ` is **reflection-positive** when this form is positive
semi-definite on `mPos`-measurable functions.

## Main definitions

* `MeasureTheory.Measure.reflectionInnerProduct μ θ F G` — the
  bilinear form `∫ F · (G ∘ θ) dμ`.
* `MeasureTheory.Measure.IsReflectionPositive μ θ mPos` — the form
  is positive semi-definite on `mPos`-measurable functions.

## Main theorems

* `reflectionInnerProduct_comm` — symmetry `⟨F, G⟩_θ = ⟨G, F⟩_θ`
  (uses `θ ∘ θ = id` + `MeasurePreserving θ μ μ`).
* `reflectionInnerProduct_add_right` / `reflectionInnerProduct_smul_right` —
  bilinearity.

## References

* Glimm-Jaffe Ch. 6 §6.2 (lattice transfer matrix and RP).
* Osterwalder-Schrader (1973, 1975) — OS3 axiom.
* Simon, *P(φ)₂*, §III.
-/

namespace MeasureTheory.Measure

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- The reflection bilinear form `⟨F, G⟩_θ := ∫ F · (G ∘ θ) dμ`, for
real-valued observables `F, G : Ω → ℝ` and a reflection `θ : Ω → Ω`. -/
noncomputable def reflectionInnerProduct (μ : Measure Ω) (θ : Ω → Ω) (F G : Ω → ℝ) : ℝ :=
  ∫ x, F x * G (θ x) ∂μ

@[simp] theorem reflectionInnerProduct_apply (μ : Measure Ω) (θ : Ω → Ω) (F G : Ω → ℝ) :
    reflectionInnerProduct μ θ F G = ∫ x, F x * G (θ x) ∂μ := rfl

/-- Symmetry of the reflection form: when `θ` is a measure-preserving
involution, `⟨F, G⟩_θ = ⟨G, F⟩_θ`. The substitution `x ↦ θ x` (valid by
measure preservation) followed by `θ (θ x) = x` swaps the roles of the
two arguments. -/
theorem reflectionInnerProduct_comm {μ : Measure Ω} {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) (hinv : Function.Involutive θ)
    {F G : Ω → ℝ} (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ) :
    reflectionInnerProduct μ θ F G = reflectionInnerProduct μ θ G F := by
  simp only [reflectionInnerProduct_apply]
  -- Substitute x ↦ θ x in the RHS via measure preservation.
  have hg : AEStronglyMeasurable (fun x => G x * F (θ x)) μ :=
    hG.mul (hF.comp_measurePreserving hθ)
  have hinv' : ∀ x, θ (θ x) = x := hinv
  have key : ∫ x, G x * F (θ x) ∂μ = ∫ x, G (θ x) * F x ∂μ := by
    have h := integral_map (φ := θ) (f := fun y => G y * F (θ y))
      hθ.measurable.aemeasurable (by rw [hθ.map_eq]; exact hg)
    rw [hθ.map_eq] at h
    simp only [hinv'] at h
    exact h
  rw [key]
  simp_rw [mul_comm]

/-- **Self-adjointness of time translation under the reflection form.**
If `τ` is a measure-preserving map satisfying the OS commutation relation
`τ (θ (τ x)) = θ x` (i.e. `θ τ θ = τ⁻¹`, the reflection inverts the
translation), then translating the first argument equals translating the
second: `⟨F ∘ τ, G⟩_θ = ⟨F, G ∘ τ⟩_θ`. This is what makes the transfer
operator `[f] ↦ [f ∘ τ]` self-adjoint on the physical Hilbert space. -/
theorem reflectionInnerProduct_comp_left {μ : Measure Ω} {θ τ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) (hτ : MeasurePreserving τ μ μ)
    (hcomm : ∀ x, τ (θ (τ x)) = θ x)
    {F G : Ω → ℝ} (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ) :
    reflectionInnerProduct μ θ (fun x => F (τ x)) G
      = reflectionInnerProduct μ θ F (fun x => G (τ x)) := by
  simp only [reflectionInnerProduct_apply]
  -- rewrite `G (θ x) = G (τ (θ (τ x)))` (by `hcomm`), exposing `φ ∘ τ`
  have hL : (fun x => F (τ x) * G (θ x))
      = fun x => (fun y => F y * G (τ (θ y))) (τ x) := by
    funext x; simp only [hcomm]
  rw [hL]
  -- `∫ φ (τ x) ∂μ = ∫ φ ∂μ` by measure preservation
  have hφ : AEStronglyMeasurable (fun y => F y * G (τ (θ y))) μ :=
    hF.mul (hG.comp_measurePreserving (hτ.comp hθ))
  have h := integral_map (φ := τ) (f := fun y => F y * G (τ (θ y)))
    hτ.measurable.aemeasurable (by rw [hτ.map_eq]; exact hφ)
  rw [hτ.map_eq] at h
  exact h.symm

/-- Additivity in the second argument (given integrability of the two
pieces). -/
theorem reflectionInnerProduct_add_right {μ : Measure Ω} {θ : Ω → Ω} {F G H : Ω → ℝ}
    (hG : Integrable (fun x => F x * G (θ x)) μ)
    (hH : Integrable (fun x => F x * H (θ x)) μ) :
    reflectionInnerProduct μ θ F (G + H)
      = reflectionInnerProduct μ θ F G + reflectionInnerProduct μ θ F H := by
  simp only [reflectionInnerProduct_apply, Pi.add_apply, mul_add]
  exact integral_add hG hH

/-- Homogeneity in the second argument. -/
theorem reflectionInnerProduct_smul_right {μ : Measure Ω} {θ : Ω → Ω} (c : ℝ) (F G : Ω → ℝ) :
    reflectionInnerProduct μ θ F (c • G) = c * reflectionInnerProduct μ θ F G := by
  simp only [reflectionInnerProduct_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- A measure `μ` is **reflection-positive** with respect to a
reflection `θ` and a sub-σ-algebra `m₊` (the "positive-time"
observables) when the reflection form `⟨F, F⟩_θ` is nonnegative for
every `m₊`-measurable `F` for which the form is defined.

This is the Osterwalder-Schrader OS3 axiom in abstract form. -/
def IsReflectionPositive (μ : Measure Ω) (θ : Ω → Ω) (mPos : MeasurableSpace Ω) : Prop :=
  ∀ F : Ω → ℝ, Measurable[mPos] F → Integrable (fun x => F x * F (θ x)) μ →
    0 ≤ @reflectionInnerProduct Ω m0 μ θ F F

end MeasureTheory.Measure
