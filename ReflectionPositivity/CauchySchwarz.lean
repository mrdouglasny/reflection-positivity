/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.Abstract
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Reflection Cauchy-Schwarz and the physical Hilbert space

For any reflection-positive measure, the bilinear form
`⟨F, G⟩_θ := ∫ F · (G ∘ θ) dμ` satisfies the Cauchy-Schwarz inequality

  `|⟨F, G⟩_θ|² ≤ ⟨F, F⟩_θ · ⟨G, G⟩_θ`,

and the quotient of `L²(mPos)` by the kernel of `⟨·, ·⟩_θ` carries a
genuine inner product. Its Hilbert completion is the **physical
Hilbert space** of the OS reconstruction direction.

## Main theorems

* `inner_mul_self_le_of_posSemidef` — the engine: Cauchy-Schwarz for an
  arbitrary symmetric positive-semidefinite bilinear form on a real
  vector space, via the quadratic-discriminant argument. This is the
  algebraic core shared by the OS reflection form and the FLS
  connection-matrix PSD argument.

## Planned (Phase 1 cont.)

* `MeasureTheory.Measure.IsReflectionPositive.cauchySchwarz` —
  specialization to `reflectionInnerProduct` on the `L²(mPos)`
  subspace, where bilinearity is unconditional.
* `MeasureTheory.Measure.IsReflectionPositive.physicalHilbertSpace` —
  quotient by the kernel + completion.

## References

* Osterwalder-Schrader (1973, 1975).
* Glimm-Jaffe Ch. 6 (the construction in the lattice setting).
* Simon, *P(φ)₂*, §III.5 (OS reconstruction).
-/

/-- **Cauchy-Schwarz for a symmetric positive-semidefinite bilinear
form.** If `B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ` is symmetric (`B u v = B v u`) and
positive semidefinite (`0 ≤ B u u` for all `u`), then

  `(B u v) ^ 2 ≤ B u u * B v v`.

The proof is the classical discriminant argument: the quadratic
`t ↦ B (u - t • v) (u - t • v) ≥ 0` is everywhere nonnegative, so its
discriminant is `≤ 0`.

This is the algebraic heart of the reflection Cauchy-Schwarz inequality
(specialized to `B = reflectionInnerProduct μ θ` on `L²(mPos)`) and of
the Freedman-Lovász-Schrijver connection-matrix `2 × 2` minor bound. -/
theorem inner_mul_self_le_of_posSemidef {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ u v, B u v = B v u)
    (hpos : ∀ u, 0 ≤ B u u) (u v : V) :
    (B u v) ^ 2 ≤ B u u * B v v := by
  have key : ∀ t : ℝ, 0 ≤ (B v v) * (t * t) + (-(2 * B u v)) * t + B u u := by
    intro t
    have h := hpos (u - t • v)
    have expand : B (u - t • v) (u - t • v)
        = (B v v) * (t * t) + (-(2 * B u v)) * t + B u u := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul]
      rw [hsymm v u]; ring
    rwa [expand] at h
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-- **The radical of a symmetric PSD bilinear form.** If `B u u = 0`
then `B u v = 0` for every `v` — a degenerate vector pairs to zero with
everything. Immediate from Cauchy-Schwarz: `(B u v)² ≤ B u u · B v v = 0`.

This is why the null set `{u : B u u = 0}` is a *subspace* and why the
reflection form descends to a genuine inner product on the quotient. -/
theorem inner_eq_zero_of_self_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ u v, B u v = B v u)
    (hpos : ∀ u, 0 ≤ B u u) {u : V} (hu : B u u = 0) (v : V) :
    B u v = 0 := by
  have h := inner_mul_self_le_of_posSemidef B hsymm hpos u v
  rw [hu, zero_mul] at h
  have hsq : (B u v) ^ 2 = 0 := le_antisymm h (sq_nonneg _)
  exact pow_eq_zero_iff (by norm_num) |>.mp hsq

namespace MeasureTheory.Measure

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- **Reflection Cauchy-Schwarz.** For a reflection-positive measure
`μ` (with a measure-preserving involution `θ` and positive-time
sub-σ-algebra `mPos ≤ m0`), and any two `mPos`-measurable observables
`F, G` whose pairwise products with reflections are integrable,

  `⟨F, G⟩_θ ^ 2 ≤ ⟨F, F⟩_θ · ⟨G, G⟩_θ`.

This is the basic inequality of the OS reflection-positivity framework.
The four integrability hypotheses hold automatically once `F, G` lie in
`L²(mPos)` (Hölder); they are taken as hypotheses here pending the
`L²(mPos)` subspace construction. -/
theorem IsReflectionPositive.cauchySchwarz {μ : Measure Ω} {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) (hinv : Function.Involutive θ)
    {mPos : MeasurableSpace Ω} (hRP : @IsReflectionPositive Ω m0 μ θ mPos) (hm : mPos ≤ m0)
    {F G : Ω → ℝ} (hF : Measurable[mPos] F) (hG : Measurable[mPos] G)
    (iFF : Integrable (fun x => F x * F (θ x)) μ)
    (iFG : Integrable (fun x => F x * G (θ x)) μ)
    (iGF : Integrable (fun x => G x * F (θ x)) μ)
    (iGG : Integrable (fun x => G x * G (θ x)) μ) :
    (@reflectionInnerProduct Ω m0 μ θ F G) ^ 2
      ≤ @reflectionInnerProduct Ω m0 μ θ F F * @reflectionInnerProduct Ω m0 μ θ G G := by
  -- In tactic mode the loose `mPos` becomes a local instance; pin the ground
  -- σ-algebra `m0` explicitly wherever the ambient one is intended.
  have hFm : @Measurable Ω ℝ m0 _ F := hF.mono hm le_rfl
  have hGm : @Measurable Ω ℝ m0 _ G := hG.mono hm le_rfl
  have hsymmGF : (∫ x, G x * F (θ x) ∂μ) = ∫ x, F x * G (θ x) ∂μ := by
    simpa only [reflectionInnerProduct_apply]
      using @reflectionInnerProduct_comm Ω m0 μ θ hθ hinv G F hGm hFm
  have key : ∀ t : ℝ,
      0 ≤ (@reflectionInnerProduct Ω m0 μ θ G G) * (t * t)
        + (-(2 * @reflectionInnerProduct Ω m0 μ θ F G)) * t
        + @reflectionInnerProduct Ω m0 μ θ F F := by
    intro t
    -- the four-term split of (F - t•G)·((F - t•G) ∘ θ)
    have e : (fun x => (F x - t * G x) * (F (θ x) - t * G (θ x)))
        = fun x => F x * F (θ x) - t * (F x * G (θ x))
            - t * (G x * F (θ x)) + (t * t) * (G x * G (θ x)) := by
      funext x; ring
    -- integrability of the partial sums, in explicit pointwise-lambda shape so
    -- that `integral_add`/`integral_sub` patterns match after `rw [e]`.
    have h3 : Integrable (fun x => F x * F (θ x) - t * (F x * G (θ x))) μ :=
      iFF.sub (iFG.const_mul t)
    have h1 : Integrable
        (fun x => F x * F (θ x) - t * (F x * G (θ x)) - t * (G x * F (θ x))) μ :=
      h3.sub (iGF.const_mul t)
    have h2 : Integrable (fun x => (t * t) * (G x * G (θ x))) μ := iGG.const_mul (t * t)
    have hHmeas : Measurable[mPos] (fun x => F x - t * G x) :=
      hF.sub (measurable_const.mul hG)
    have hHint : Integrable (fun x => (F x - t * G x) * (F (θ x) - t * G (θ x))) μ := by
      rw [e]; exact h1.add h2
    have hpos := hRP (fun x => F x - t * G x) hHmeas hHint
    -- expand ⟨F - t•G, F - t•G⟩_θ into the quadratic in t
    have expand : @reflectionInnerProduct Ω m0 μ θ (fun x => F x - t * G x)
          (fun x => F x - t * G x)
        = (@reflectionInnerProduct Ω m0 μ θ G G) * (t * t)
          + (-(2 * @reflectionInnerProduct Ω m0 μ θ F G)) * t
          + @reflectionInnerProduct Ω m0 μ θ F F := by
      simp only [reflectionInnerProduct_apply]
      rw [e, integral_add h1 h2, integral_sub h3 (iGF.const_mul t),
        integral_sub iFF (iFG.const_mul t)]
      simp only [integral_const_mul]
      rw [hsymmGF]; ring
    rw [expand] at hpos
    exact hpos
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-- For `L²` observables `F, G` and a measure-preserving `θ`, the
reflection-form integrand `x ↦ F x · G (θ x)` is integrable: `G ∘ θ`
is again `L²` (measure preservation) and the product of two `L²`
functions is `L¹` (Hölder, `1/2 + 1/2 = 1`). -/
theorem integrable_mul_comp {μ : Measure Ω} {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) {F G : Ω → ℝ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    Integrable (fun x => F x * G (θ x)) μ :=
  hF.integrable_mul (hG.comp_measurePreserving hθ)

/-- **Reflection Cauchy-Schwarz for `L²` observables.** The `L²`
membership of `F, G` makes the four product-integrability hypotheses of
`IsReflectionPositive.cauchySchwarz` automatic (`integrable_mul_comp`),
so the inequality holds for any `mPos`-measurable `F, G ∈ L²(μ)`. -/
theorem IsReflectionPositive.cauchySchwarz_memLp {μ : Measure Ω} {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) (hinv : Function.Involutive θ)
    {mPos : MeasurableSpace Ω} (hRP : @IsReflectionPositive Ω m0 μ θ mPos) (hm : mPos ≤ m0)
    {F G : Ω → ℝ} (hF : Measurable[mPos] F) (hG : Measurable[mPos] G)
    (hFL2 : MemLp F 2 μ) (hGL2 : MemLp G 2 μ) :
    (@reflectionInnerProduct Ω m0 μ θ F G) ^ 2
      ≤ @reflectionInnerProduct Ω m0 μ θ F F * @reflectionInnerProduct Ω m0 μ θ G G :=
  -- fully `@`-pinned: with `mPos` in scope it would otherwise shadow `m0`.
  @IsReflectionPositive.cauchySchwarz Ω m0 μ θ hθ hinv mPos hRP hm F G hF hG
    (@integrable_mul_comp Ω m0 μ θ hθ F F hFL2 hFL2)
    (@integrable_mul_comp Ω m0 μ θ hθ F G hFL2 hGL2)
    (@integrable_mul_comp Ω m0 μ θ hθ G F hGL2 hFL2)
    (@integrable_mul_comp Ω m0 μ θ hθ G G hGL2 hGL2)

/-- **A null vector of the reflection form pairs to zero with every
other `L²` observable.** If `⟨F, F⟩_θ = 0` then `⟨F, G⟩_θ = 0` for all
`mPos`-measurable `G ∈ L²(μ)`. This is the measure-theoretic radical
lemma: the null set is closed under the form, the seed of the kernel
submodule and the quotient inner product (`physicalHilbertSpace`). -/
theorem IsReflectionPositive.reflectionInnerProduct_eq_zero_of_self_eq_zero
    {μ : Measure Ω} {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) (hinv : Function.Involutive θ)
    {mPos : MeasurableSpace Ω} (hRP : @IsReflectionPositive Ω m0 μ θ mPos) (hm : mPos ≤ m0)
    {F G : Ω → ℝ} (hF : Measurable[mPos] F) (hG : Measurable[mPos] G)
    (hFL2 : MemLp F 2 μ) (hGL2 : MemLp G 2 μ)
    (hFF : @reflectionInnerProduct Ω m0 μ θ F F = 0) :
    @reflectionInnerProduct Ω m0 μ θ F G = 0 := by
  have h := @IsReflectionPositive.cauchySchwarz_memLp Ω m0 μ θ hθ hinv mPos hRP hm
    F G hF hG hFL2 hGL2
  rw [hFF, zero_mul] at h
  have hsq : (@reflectionInnerProduct Ω m0 μ θ F G) ^ 2 = 0 := le_antisymm h (sq_nonneg _)
  exact pow_eq_zero_iff (by norm_num) |>.mp hsq

/-! ### The reflection form at the `L²` level

To build the physical Hilbert space we lift the reflection form to
`L²(μ) = Lp ℝ 2 μ`, where it is the L²-inner product twisted by the
**reflection operator** `R : g ↦ g ∘ θ`. This packages bilinearity and
continuity for free (from the L² inner product) and is the input to the
`PreInnerProductSpace.Core`/`Completion` construction of `H_phys`. -/

open scoped RealInnerProductSpace in
/-- The reflection operator `R : g ↦ g ∘ θ` on `L²(μ)`, as the
norm-preserving additive map `Lp.compMeasurePreserving`. -/
noncomputable def reflectionLp {μ : Measure Ω} {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) : Lp ℝ 2 μ →+ Lp ℝ 2 μ :=
  Lp.compMeasurePreserving θ hθ

open scoped RealInnerProductSpace in
/-- **Bridge to the concrete form.** The L²-inner product twisted by the
reflection operator is the reflection form on representatives:
`⟪f, R g⟫ = ∫ f · (g ∘ θ) dμ = reflectionInnerProduct μ θ f g`. -/
theorem inner_reflectionLp {μ : Measure Ω} {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) (f g : Lp ℝ 2 μ) :
    ⟪f, reflectionLp hθ g⟫ = ∫ x, f x * g (θ x) ∂μ := by
  simp only [reflectionLp, MeasureTheory.L2.inner_def, RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving g hθ] with a ha
  rw [ha, Function.comp_apply, mul_comm]

end MeasureTheory.Measure
