/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.CauchySchwarz
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# The physical Hilbert space of a reflection-positive system

Given a reflection-positive measure `μ` with a measure-preserving
involution `θ` and positive-time sub-σ-algebra `mPos`, the
Osterwalder-Schrader **physical Hilbert space** `H_phys` is the Hilbert
space obtained from the positive-time `L²` observables by the reflection
form `B(f, g) = ∫ f · (g ∘ θ) dμ`, quotiented by its null space and
completed.

We package the data as a `ReflectionSystem` and reuse Mathlib's prebuilt
pipeline: a `PreInnerProductSpace.Core` (possibly degenerate inner
product) → `InnerProductSpace.ofCore` (seminormed inner product space) →
`UniformSpace.Completion` (which separates the null space *and*
completes, yielding a genuine Hilbert space).

## Main definitions

* `ReflectionSystem` — bundled RP data (`μ, θ, mPos`, measure
  preservation, involution, RP, `mPos ≤ m0`).
* `ReflectionSystem.PosObs` — the positive-time observables `lpMeas mPos`
  as a fresh `Module ℝ` carrier (so the reflection seminorm does not
  clash with the ambient `L²` norm).
* `ReflectionSystem.physicalHilbertSpace` — `H_phys`, the completion.

## References

* Osterwalder-Schrader (1973, 1975); Glimm-Jaffe Ch. 6.
* Template: `Mathlib/Analysis/InnerProductSpace/Reproducing.lean`.
-/

open MeasureTheory MeasureTheory.Measure
open scoped RealInnerProductSpace

namespace ReflectionPositivity

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- A **reflection-positive system** on `(Ω, m0)`: a measure `μ`, a
measure-preserving involution `θ`, and a positive-time sub-σ-algebra
`mPos ≤ m0` for which `μ` is reflection-positive. -/
structure ReflectionSystem (Ω : Type*) [m0 : MeasurableSpace Ω] where
  /-- The (Euclidean) measure. -/
  μ : Measure Ω
  /-- The reflection. -/
  θ : Ω → Ω
  /-- `θ` preserves `μ`. (Declared before `mPos` so the ambient `m0` is the
  only `MeasurableSpace Ω` in scope here.) -/
  mp : MeasurePreserving θ μ μ
  /-- `θ` is an involution. -/
  inv : Function.Involutive θ
  /-- The positive-time sub-σ-algebra. -/
  mPos : MeasurableSpace Ω
  /-- `mPos` is coarser than the ambient σ-algebra. -/
  le : mPos ≤ m0
  /-- `μ` is reflection-positive for `θ` and `mPos`. -/
  rp : @IsReflectionPositive Ω m0 μ θ mPos

namespace ReflectionSystem

variable (S : ReflectionSystem Ω)

/-- The positive-time `L²` observables, as a fresh `Module ℝ` carrier.
We use a `def` (not `abbrev`) so the carrier does **not** inherit the
ambient `L²` norm on `lpMeas`, leaving room for the reflection seminorm
installed by `InnerProductSpace.ofCore`. -/
def PosObs : Type _ := ↥(lpMeas ℝ ℝ S.mPos 2 S.μ)

noncomputable instance : AddCommGroup S.PosObs :=
  inferInstanceAs (AddCommGroup ↥(lpMeas ℝ ℝ S.mPos 2 S.μ))

noncomputable instance : Module ℝ S.PosObs :=
  inferInstanceAs (Module ℝ ↥(lpMeas ℝ ℝ S.mPos 2 S.μ))

/-- Coercion of a positive-time observable to its `L²` class. -/
def PosObs.toLp (f : S.PosObs) : Lp ℝ 2 S.μ :=
  ((show ↥(lpMeas ℝ ℝ S.mPos 2 S.μ) from f) : Lp ℝ 2 S.μ)

/-- Membership witness: the `L²` class of a positive-time observable is
`mPos`-a.e.-strongly-measurable. -/
theorem PosObs.aestronglyMeasurable (f : S.PosObs) :
    AEStronglyMeasurable[S.mPos] f.toLp S.μ :=
  mem_lpMeas_iff_aestronglyMeasurable.mp (show ↥(lpMeas ℝ ℝ S.mPos 2 S.μ) from f).2

/-- The reflection inner product on the positive-time observables:
`⟪f, g⟫ := ⟪f, R g⟫_{L²} = ∫ f·(g∘θ) dμ`. -/
noncomputable def innerForm (f g : S.PosObs) : ℝ :=
  ⟪f.toLp, reflectionLp S.mp g.toLp⟫

/-- The (possibly degenerate) inner-product core on the positive-time
observables, from reflection positivity. -/
noncomputable instance instPreCore : PreInnerProductSpace.Core ℝ S.PosObs where
  inner f g := S.innerForm f g
  conj_inner_symm f g := by
    simp only [conj_trivial, innerForm]
    exact inner_reflectionLp_comm S.mp S.inv g.toLp f.toLp
  re_inner_nonneg f := by
    simp only [RCLike.re_to_real, innerForm]
    rw [inner_reflectionLp]
    exact reflectionInnerProduct_self_nonneg S.mp S.rp f.toLp f.aestronglyMeasurable
  add_left f g h := by
    simp only [innerForm]
    rw [show (f + g).toLp = f.toLp + g.toLp from rfl, inner_add_left]
  smul_left f g r := by
    simp only [innerForm]
    rw [show (r • f).toLp = r • f.toLp from rfl, inner_smul_left]

noncomputable instance : SeminormedAddCommGroup S.PosObs :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

noncomputable instance : InnerProductSpace ℝ S.PosObs :=
  InnerProductSpace.ofCore _

/-- The **physical Hilbert space** of a reflection-positive system: the
completion of the positive-time observables under the reflection
seminorm. The null space of the reflection form is separated and the
space is completed in one step by `UniformSpace.Completion`. -/
abbrev physicalHilbertSpace : Type _ := UniformSpace.Completion S.PosObs

-- `H_phys` is complete, hence a genuine real Hilbert space: the
-- `InnerProductSpace ℝ` and `CompleteSpace` instances are synthesized
-- through `UniformSpace.Completion`. (`CompleteSpace` is a `Prop`.)
example : CompleteSpace S.physicalHilbertSpace := inferInstance

end ReflectionSystem

end ReflectionPositivity
