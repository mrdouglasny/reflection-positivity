/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.PhysicalHilbertSpace
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Transfer operators on the physical Hilbert space

This file packages the first bridge from an Osterwalder-Schrader time
translation on a reflection-positive system to the induced operator on the
physical Hilbert space.

The structure `TimeTranslatedSystem` extends `ReflectionSystem` by a
measure-preserving time translation `τ`, the OS relation
`τ (θ (τ x)) = θ x`, preservation of positive-time observables under
composition by `τ`, and the reflection-norm contraction estimate needed
to descend the map to the physical Hilbert space.

For such a system we define:

* `TimeTranslatedSystem.transferOperatorPre`, the contraction on
  positive-time observables `f ↦ f ∘ τ`;
* `TimeTranslatedSystem.transferOperator`, its continuous linear
  extension to the completed physical Hilbert space;
* self-adjointness of the transfer operator;
* the vacuum vector, under the additional hypothesis that the underlying
  measure is a probability measure.
-/

open MeasureTheory MeasureTheory.Measure
open scoped RealInnerProductSpace

namespace ReflectionPositivity

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- A reflection-positive system equipped with a time translation.

The relation `τθ` is the OS covariance relation saying that reflection
inverts time translation, in the form `τ (θ (τ x)) = θ x`.  The field
`τPos` says that composition by `τ` preserves the positive-time
sub-σ-algebra at the `L²` level, and `contraction` is the reflection-norm
contraction estimate used to construct a bounded operator on the
physical Hilbert space. -/
structure TimeTranslatedSystem (Ω : Type*) [m0 : MeasurableSpace Ω]
    extends ReflectionSystem Ω where
  /-- The time translation. -/
  τ : Ω → Ω
  /-- The time translation preserves the Euclidean measure. -/
  τmp : @MeasurePreserving Ω Ω m0 m0 τ μ μ
  /-- Reflection inverts time translation: `θ τ θ = τ⁻¹` in this form. -/
  τθ : ∀ x, τ (θ (τ x)) = θ x
  /-- Composition by `τ` preserves positive-time `L²` observables. -/
  τPos : ∀ f : @Lp Ω ℝ m0 _ 2 μ, AEStronglyMeasurable[mPos] (⇑f) μ →
    AEStronglyMeasurable[mPos] (fun x => f (τ x)) μ
  /-- Composition by `τ` is a contraction for the reflection seminorm. -/
  contraction : ∀ f : @ReflectionSystem.PosObs Ω m0 toReflectionSystem,
    @reflectionInnerProduct Ω m0 μ θ
        (fun x =>
          ((@ReflectionSystem.PosObs.toLp Ω m0 toReflectionSystem f :
              @Lp Ω ℝ m0 _ 2 μ) : Ω → ℝ) (τ x))
        (fun x =>
          ((@ReflectionSystem.PosObs.toLp Ω m0 toReflectionSystem f :
              @Lp Ω ℝ m0 _ 2 μ) : Ω → ℝ) (τ x))
      ≤ @reflectionInnerProduct Ω m0 μ θ
        ((@ReflectionSystem.PosObs.toLp Ω m0 toReflectionSystem f : @Lp Ω ℝ m0 _ 2 μ) : Ω → ℝ)
        ((@ReflectionSystem.PosObs.toLp Ω m0 toReflectionSystem f : @Lp Ω ℝ m0 _ 2 μ) : Ω → ℝ)

namespace TimeTranslatedSystem

variable (S : TimeTranslatedSystem Ω)

/-- Positive-time observables of the underlying reflection system. -/
abbrev PosObs : Type _ :=
  S.toReflectionSystem.PosObs

/-- The physical Hilbert space of the underlying reflection system. -/
abbrev physicalHilbertSpace : Type _ :=
  S.toReflectionSystem.physicalHilbertSpace

namespace PosObs

variable {S}

/-- Coercion of a time-translated system's positive-time observable to
its ambient `L²` class. -/
abbrev toLp (f : S.PosObs) : Lp ℝ 2 S.μ :=
  @ReflectionSystem.PosObs.toLp Ω m0 S.toReflectionSystem f

/-- Positive-time observables are `mPos`-a.e.-strongly-measurable. -/
theorem aestronglyMeasurable (f : S.PosObs) :
    AEStronglyMeasurable[S.mPos] f.toLp S.μ :=
  @ReflectionSystem.PosObs.aestronglyMeasurable Ω m0 S.toReflectionSystem f

end PosObs

/-- The linear map on positive-time observables induced by composition
with the time translation. -/
noncomputable def transferOperatorLinear : S.PosObs →ₗ[ℝ] S.PosObs where
  toFun f :=
    ⟨Lp.compMeasurePreserving S.τ S.τmp f.toLp, by
      rw [mem_lpMeas_iff_aestronglyMeasurable]
      exact (S.τPos f.toLp f.aestronglyMeasurable).congr
        (Lp.coeFn_compMeasurePreserving f.toLp S.τmp).symm⟩
  map_add' f g := by
    apply Subtype.ext
    change Lp.compMeasurePreserving S.τ S.τmp (f.toLp + g.toLp)
      = Lp.compMeasurePreserving S.τ S.τmp f.toLp
        + Lp.compMeasurePreserving S.τ S.τmp g.toLp
    simp
  map_smul' c f := by
    apply Subtype.ext
    change Lp.compMeasurePreserving S.τ S.τmp (c • f.toLp)
      = c • Lp.compMeasurePreserving S.τ S.τmp f.toLp
    exact (Lp.compMeasurePreservingₗ ℝ S.τ S.τmp).map_smul c f.toLp

/-- The `L²` representative of `transferOperatorLinear f` is
`f.toLp ∘ τ`. -/
theorem transferOperatorLinear_toLp_ae (f : S.PosObs) :
    (S.transferOperatorLinear f).toLp =ᵐ[S.μ] fun x => f.toLp (S.τ x) :=
  Lp.coeFn_compMeasurePreserving f.toLp S.τmp

/-- The reflection-form value with a translated left input, expressed on
representatives. -/
theorem innerForm_transferOperatorLinear_left (f g : S.PosObs) :
    S.toReflectionSystem.innerForm (S.transferOperatorLinear f) g =
      reflectionInnerProduct S.μ S.θ (fun x => f.toLp (S.τ x)) g.toLp := by
  rw [ReflectionSystem.innerForm, inner_reflectionLp]
  simp only [reflectionInnerProduct_apply]
  refine integral_congr_ae ?_
  filter_upwards [S.transferOperatorLinear_toLp_ae f] with x hx
  rw [hx]

/-- The reflection-form value with a translated right input, expressed on
representatives. -/
theorem innerForm_transferOperatorLinear_right (f g : S.PosObs) :
    S.toReflectionSystem.innerForm f (S.transferOperatorLinear g) =
      reflectionInnerProduct S.μ S.θ f.toLp (fun x => g.toLp (S.τ x)) := by
  rw [ReflectionSystem.innerForm, inner_reflectionLp]
  simp only [reflectionInnerProduct_apply]
  refine integral_congr_ae ?_
  have hg := S.transferOperatorLinear_toLp_ae g
  have hgθ := S.mp.quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [hgθ] with x hx
  simpa only [Function.comp_apply] using congrArg (fun y => f.toLp x * y) hx

/-- The reflection form on positive-time observables is the concrete
reflection inner product on their `L²` representatives. -/
theorem innerForm_eq_reflectionInnerProduct (f g : S.PosObs) :
    S.toReflectionSystem.innerForm f g =
      reflectionInnerProduct S.μ S.θ f.toLp g.toLp := by
  rw [ReflectionSystem.innerForm, inner_reflectionLp]
  rfl

/-- The reflection-form value of two translated copies of the same
positive-time observable. -/
theorem innerForm_transferOperatorLinear_self (f : S.PosObs) :
    S.toReflectionSystem.innerForm (S.transferOperatorLinear f) (S.transferOperatorLinear f) =
      reflectionInnerProduct S.μ S.θ (fun x => f.toLp (S.τ x))
        (fun x => f.toLp (S.τ x)) := by
  rw [S.innerForm_transferOperatorLinear_left]
  simp only [reflectionInnerProduct_apply]
  refine integral_congr_ae ?_
  have hf := S.transferOperatorLinear_toLp_ae f
  have hfθ := S.mp.quasiMeasurePreserving.ae_eq_comp hf
  filter_upwards [hfθ] with x hx
  simpa only [Function.comp_apply] using
    congrArg (fun y => f.toLp (S.τ x) * y) hx

/-- The reflection-form contraction estimate for the translated
positive-time observable. -/
theorem innerForm_transferOperatorLinear_self_le (f : S.PosObs) :
    S.toReflectionSystem.innerForm (S.transferOperatorLinear f) (S.transferOperatorLinear f)
      ≤ S.toReflectionSystem.innerForm f f := by
  rw [S.innerForm_transferOperatorLinear_self, S.innerForm_eq_reflectionInnerProduct]
  simpa only [PosObs.toLp] using S.contraction f

/-- The time-translation map is norm-contracting on positive-time
observables with the reflection seminorm. -/
theorem norm_transferOperatorLinear_le (f : S.PosObs) :
    ‖S.transferOperatorLinear f‖ ≤ ‖f‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg f)
  rw [← inner_self_eq_norm_sq (𝕜 := ℝ) (S.transferOperatorLinear f),
    ← inner_self_eq_norm_sq (𝕜 := ℝ) f]
  change S.toReflectionSystem.innerForm (S.transferOperatorLinear f) (S.transferOperatorLinear f)
    ≤ S.toReflectionSystem.innerForm f f
  exact S.innerForm_transferOperatorLinear_self_le f

/-- The transfer operator on positive-time observables, as a continuous
linear contraction for the reflection seminorm. -/
noncomputable def transferOperatorPre : S.PosObs →L[ℝ] S.PosObs :=
  (S.transferOperatorLinear).mkContinuous 1 fun f => by
    simpa only [one_mul] using S.norm_transferOperatorLinear_le f

/-- The `L²` representative of `transferOperatorPre f` is
`f.toLp ∘ τ`. -/
theorem transferOperatorPre_toLp_ae (f : S.PosObs) :
    (S.transferOperatorPre f).toLp =ᵐ[S.μ] fun x => f.toLp (S.τ x) :=
  S.transferOperatorLinear_toLp_ae f

/-- On positive-time observables, the pre-transfer operator is symmetric
for the physical inner product. -/
theorem transferOperatorPre_symmetric (f g : S.PosObs) :
    ⟪S.transferOperatorPre f, g⟫ = ⟪f, S.transferOperatorPre g⟫ := by
  change S.toReflectionSystem.innerForm (S.transferOperatorLinear f) g =
    S.toReflectionSystem.innerForm f (S.transferOperatorLinear g)
  rw [innerForm_transferOperatorLinear_left, innerForm_transferOperatorLinear_right]
  letI : MeasurableSpace Ω := m0
  exact reflectionInnerProduct_comp_left S.mp S.τmp S.τθ
    ((f.aestronglyMeasurable).mono S.le)
    ((g.aestronglyMeasurable).mono S.le)

/-- The transfer operator on the physical Hilbert space, obtained by
continuously extending `transferOperatorPre` to the completion. -/
noncomputable def transferOperator : S.physicalHilbertSpace →L[ℝ] S.physicalHilbertSpace :=
  S.transferOperatorPre.completion

/-- The extension agrees with `transferOperatorPre` on the dense image of
positive-time observables. -/
@[simp]
theorem transferOperator_coe (f : S.PosObs) :
    S.transferOperator (f : S.physicalHilbertSpace) =
      ((S.transferOperatorPre f : S.PosObs) : S.physicalHilbertSpace) := by
  simp [transferOperator]

/-- The transfer operator is self-adjoint on the physical Hilbert space. -/
theorem transferOperator_selfAdjoint (x y : S.physicalHilbertSpace) :
    ⟪S.transferOperator x, y⟫ = ⟪x, S.transferOperator y⟫ := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro f g
    rw [S.transferOperator_coe f, S.transferOperator_coe g]
    simpa only [UniformSpace.Completion.inner_coe] using
      S.transferOperatorPre_symmetric f g

/-- The constant-one positive-time observable. This requires the
underlying measure to be finite; we use the natural OS normalization
assumption that `μ` is a probability measure. -/
noncomputable def vacuumPosObs [IsProbabilityMeasure S.μ] : S.PosObs :=
  ⟨Lp.const 2 S.μ (1 : ℝ), by
    rw [mem_lpMeas_iff_aestronglyMeasurable]
    have hconst : AEStronglyMeasurable[S.mPos] (fun _ : Ω => (1 : ℝ)) S.μ :=
      aestronglyMeasurable_const
    exact hconst.congr (Lp.coeFn_const (μ := S.μ) (p := 2) (c := (1 : ℝ))).symm⟩

/-- The vacuum vector in the physical Hilbert space, represented by the
constant-one positive-time observable. -/
noncomputable def vacuum [IsProbabilityMeasure S.μ] : S.physicalHilbertSpace :=
  (S.vacuumPosObs : S.PosObs)

/-- The pre-transfer operator fixes the constant-one positive-time
observable. -/
theorem transferOperatorPre_vacuumPosObs [IsProbabilityMeasure S.μ] :
    S.transferOperatorPre S.vacuumPosObs = S.vacuumPosObs := by
  apply Subtype.ext
  change Lp.compMeasurePreserving S.τ S.τmp (Lp.const 2 S.μ (1 : ℝ))
    = Lp.const 2 S.μ (1 : ℝ)
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving (Lp.const 2 S.μ (1 : ℝ)) S.τmp
  have hconst := Lp.coeFn_const (μ := S.μ) (p := 2) (c := (1 : ℝ))
  exact hcomp.trans ((S.τmp.quasiMeasurePreserving.ae_eq_comp hconst).trans hconst.symm)

/-- The transfer operator fixes the vacuum vector. -/
theorem transferOperator_vacuum [IsProbabilityMeasure S.μ] :
    S.transferOperator S.vacuum = S.vacuum := by
  change S.transferOperator ((S.vacuumPosObs : S.PosObs) : S.physicalHilbertSpace) =
    ((S.vacuumPosObs : S.PosObs) : S.physicalHilbertSpace)
  rw [S.transferOperator_coe]
  exact congrArg (fun f : S.PosObs => (f : S.physicalHilbertSpace))
    S.transferOperatorPre_vacuumPosObs

end TimeTranslatedSystem

end ReflectionPositivity
