/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.TransferSystem
import ReflectionPositivity.MultiplicationCLM
import ReflectionPositivity.ConnectedTwoPoint

/-!
# Finite-periodic bridge for the GNS construction

Piece E1 of `docs/gns-construction-plan.md`.

This file is the finite-periodic dictionary bridge between the path-measure
two-point function supplied by `TransferSystem.twoPoint_dictionary` and the
ground/vacuum-perpendicular norm data used by the GNS spectral-gap API.

The present `reflection-positivity` API has a fully proved kernel dictionary,
but it deliberately has no abstract trace-class/signed-kernel operator API for
`T' = T - lambda_0 P_0`.  Consequently the genuinely analytic estimate that
turns the rank-one split into a uniform finite-periodic remainder is packaged
as `RemainderHypothesis.remainder_bound`.  This is the documented discharge
point for downstream concrete models: pphi2 should prove that field from its
explicit kernel/HS estimates.

No Lean `axiom` is introduced here.  The gap is represented as ordinary
structure data, so users cannot apply the main theorem without supplying the
finite-periodic remainder proof.

## The eight steps represented here

1. `pathTwoPointNat_eq_traceRatio` wraps `twoPoint_dictionary`.
2. `rankOne_kernel_split` defines and proves the rank-one/remainder split.
3. `trace_product_integrand_expansion` expands the four trace integrand terms.
4. `partition_ge_groundEigenvalue_pow` exposes the denominator lower bound as
   a named hypothesis, since positivity of the concrete transfer operator is
   not part of `TransferSystem`.
5. One-point finite-volume corrections are included in
   `finitePeriodicBridgeResidual`.
6. The one-perp legs are represented by `finitePeriodicPerpEnvelope`, using
   the existing `GappedTransfer.vacuumPerp` projection in `L^2(nu)`.
7. The `R*R`, denominator, and one-point corrections are exactly the residual
   controlled by `RemainderHypothesis.remainder_bound`.
8. `observable_vacuum_coeFn` records the bridge from the abstract
   multiplication CLM applied to the vacuum to the pointwise function
   `A * Omega` in `L^2(nu)`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace ReflectionPositivity

variable {S : Type*} [MeasurableSpace S]

/-! ## Path and trace dictionary terms -/

/-- The path-measure two-point observable at times `0` and `t`. -/
noncomputable def pathTwoPoint (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν) (Nt : ℕ) [NeZero Nt]
    (t : ZMod Nt) : ℝ :=
  ∫ ψ, A.A (ψ 0) * B.A (ψ t) ∂(Ts.pathMeasure Nt)

/-- The same two-point observable, indexed by a natural representative.  This
is the form used by `TransferSystem.twoPoint_dictionary`. -/
noncomputable def pathTwoPointNat (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν) (Nt : ℕ) [NeZero Nt]
    (t : ℕ) : ℝ :=
  ∫ ψ, A.A (ψ 0) * B.A (ψ (t : ZMod Nt)) ∂(Ts.pathMeasure Nt)

/-- One-point finite-volume mean at a periodic time. -/
noncomputable def finiteVolumeMean (Ts : TransferSystem S)
    (A : MultiplicationCLMContract Ts.ν) (Nt : ℕ) [NeZero Nt]
    (t : ZMod Nt) : ℝ :=
  ∫ ψ, A.A (ψ t) ∂(Ts.pathMeasure Nt)

/-- Connected finite-periodic path-measure two-point function. -/
noncomputable def pathConnectedTwoPoint (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν) (Nt : ℕ) [NeZero Nt]
    (t : ZMod Nt) : ℝ :=
  pathTwoPoint Ts A B Nt t
    - finiteVolumeMean Ts A Nt 0 * finiteVolumeMean Ts B Nt t

/-- The kernel trace-ratio side of the two-point dictionary.  Here
`kPow (t-1)` is the kernel of `T^t`, and `kPow (Nt-t-1)` is the kernel of
`T^(Nt-t)`. -/
noncomputable def traceRatioTwoPoint (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν) (Nt : ℕ) [NeZero Nt]
    (t : ℕ) : ℝ :=
  (Ts.partition Nt)⁻¹ *
    ∫ x, ∫ y, A.A x * Ts.kPow (t - 1) x y *
      (B.A y * Ts.kPow (Nt - t - 1) y x) ∂Ts.ν ∂Ts.ν

/-- The raw trace integrand before normalization by `Z_Nt`. -/
noncomputable def traceProductIntegrand (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν) (a b : ℕ) (x y : S) : ℝ :=
  A.A x * Ts.kPow a x y * (B.A y * Ts.kPow b y x)

/-- Dictionary bridge in the natural-indexed form supplied by
`TransferSystem.twoPoint_dictionary`. -/
theorem pathTwoPointNat_eq_traceRatio (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν) (Nt : ℕ) [NeZero Nt]
    {t : ℕ} (ht0 : 0 < t) (htn : t < Nt)
    (hAB : Integrable (twoPointSplitDensity Ts.k (t - 1) (Nt - t - 1) A.A B.A)
      (Ts.ν.prod (Ts.ν.prod
        ((Measure.pi (fun _ : Fin (t - 1) => Ts.ν)).prod
          (Measure.pi (fun _ : Fin (Nt - t - 1) => Ts.ν))))))
    (hSlice : ∀ x : S, Integrable
        (fun p : S × ((Fin (t - 1) → S) × (Fin (Nt - t - 1) → S)) =>
          twoPointSplitDensity Ts.k (t - 1) (Nt - t - 1) A.A B.A (x, p))
      (Ts.ν.prod ((Measure.pi (fun _ : Fin (t - 1) => Ts.ν)).prod
        (Measure.pi (fun _ : Fin (Nt - t - 1) => Ts.ν))))) :
    pathTwoPointNat Ts A B Nt t = traceRatioTwoPoint Ts A B Nt t := by
  simpa [pathTwoPointNat, traceRatioTwoPoint] using
    Ts.twoPoint_dictionary Nt ht0 htn A.A B.A hAB hSlice

/-- Dictionary bridge for a `ZMod Nt` time, after passing to its natural
representative. -/
theorem pathTwoPoint_eq_traceRatio_val (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν) (Nt : ℕ) [NeZero Nt]
    (t : ZMod Nt) (ht0 : 0 < t.val) (htn : t.val < Nt)
    (hAB : Integrable
      (twoPointSplitDensity Ts.k (t.val - 1) (Nt - t.val - 1) A.A B.A)
      (Ts.ν.prod (Ts.ν.prod
        ((Measure.pi (fun _ : Fin (t.val - 1) => Ts.ν)).prod
          (Measure.pi (fun _ : Fin (Nt - t.val - 1) => Ts.ν))))))
    (hSlice : ∀ x : S, Integrable
        (fun p : S × ((Fin (t.val - 1) → S) × (Fin (Nt - t.val - 1) → S)) =>
          twoPointSplitDensity Ts.k (t.val - 1) (Nt - t.val - 1) A.A B.A (x, p))
      (Ts.ν.prod ((Measure.pi (fun _ : Fin (t.val - 1) => Ts.ν)).prod
        (Measure.pi (fun _ : Fin (Nt - t.val - 1) => Ts.ν))))) :
    pathTwoPoint Ts A B Nt t = traceRatioTwoPoint Ts A B Nt t.val := by
  have hpath : pathTwoPoint Ts A B Nt t = pathTwoPointNat Ts A B Nt t.val := by
    simp [pathTwoPoint, pathTwoPointNat]
  rw [hpath]
  exact pathTwoPointNat_eq_traceRatio Ts A B Nt ht0 htn hAB hSlice

/-! ## Rank-one split and four-term trace expansion -/

/-- The formal rank-one ground kernel
`lambda_0^(m+1) Omega(x) Omega(y)`. -/
noncomputable def rankOneKernel (Ω : S → ℝ) (lambda0 : ℝ) (m : ℕ)
    (x y : S) : ℝ :=
  lambda0 ^ (m + 1) * Ω x * Ω y

/-- The signed kernel remainder left after subtracting the rank-one ground
piece from `kPow m`.  In concrete models this is the kernel of
`T'^(m+1)`, with `T' = T - lambda_0 P_0`. -/
noncomputable def kernelRemainder (Ts : TransferSystem S)
    (Ω : S → ℝ) (lambda0 : ℝ) (m : ℕ) (x y : S) : ℝ :=
  Ts.kPow m x y - rankOneKernel Ω lambda0 m x y

/-- Rank-one plus signed-remainder split of the iterated transfer kernel.
This is definitionally true for the signed remainder introduced above. -/
theorem rankOne_kernel_split (Ts : TransferSystem S)
    (Ω : S → ℝ) (lambda0 : ℝ) (m : ℕ) (x y : S) :
    Ts.kPow m x y
      = rankOneKernel Ω lambda0 m x y
        + kernelRemainder Ts Ω lambda0 m x y := by
  simp [kernelRemainder]

/-- The disconnected `P0*P0` trace-integrand term. -/
noncomputable def traceTermP0P0 (Ts : TransferSystem S)
    (Ω : S → ℝ) (lambda0 : ℝ) (A B : MultiplicationCLMContract Ts.ν)
    (a b : ℕ) (x y : S) : ℝ :=
  A.A x * rankOneKernel Ω lambda0 a x y *
    (B.A y * rankOneKernel Ω lambda0 b y x)

/-- The one-perp-leg `P0*R` trace-integrand term. -/
noncomputable def traceTermP0R (Ts : TransferSystem S)
    (Ω : S → ℝ) (lambda0 : ℝ) (A B : MultiplicationCLMContract Ts.ν)
    (a b : ℕ) (x y : S) : ℝ :=
  A.A x * rankOneKernel Ω lambda0 a x y *
    (B.A y * kernelRemainder Ts Ω lambda0 b y x)

/-- The one-perp-leg `R*P0` trace-integrand term. -/
noncomputable def traceTermRP0 (Ts : TransferSystem S)
    (Ω : S → ℝ) (lambda0 : ℝ) (A B : MultiplicationCLMContract Ts.ν)
    (a b : ℕ) (x y : S) : ℝ :=
  A.A x * kernelRemainder Ts Ω lambda0 a x y *
    (B.A y * rankOneKernel Ω lambda0 b y x)

/-- The doubly-perpendicular `R*R` trace-integrand term. -/
noncomputable def traceTermRR (Ts : TransferSystem S)
    (Ω : S → ℝ) (lambda0 : ℝ) (A B : MultiplicationCLMContract Ts.ν)
    (a b : ℕ) (x y : S) : ℝ :=
  A.A x * kernelRemainder Ts Ω lambda0 a x y *
    (B.A y * kernelRemainder Ts Ω lambda0 b y x)

/-- Pointwise four-term expansion of the trace integrand after splitting both
kernel powers into their rank-one and signed-remainder parts. -/
theorem trace_product_integrand_expansion (Ts : TransferSystem S)
    (Ω : S → ℝ) (lambda0 : ℝ) (A B : MultiplicationCLMContract Ts.ν)
    (a b : ℕ) (x y : S) :
    traceProductIntegrand Ts A B a b x y
      = traceTermP0P0 Ts Ω lambda0 A B a b x y
        + traceTermP0R Ts Ω lambda0 A B a b x y
        + traceTermRP0 Ts Ω lambda0 A B a b x y
        + traceTermRR Ts Ω lambda0 A B a b x y := by
  rw [traceProductIntegrand, rankOne_kernel_split Ts Ω lambda0 a x y,
    rankOne_kernel_split Ts Ω lambda0 b y x]
  simp [traceTermP0P0, traceTermP0R, traceTermRP0, traceTermRR]
  ring

/-! ## Denominator and L2 observable bridge -/

/-- Named form of the denominator lower bound `Z_Nt >= lambda_0^Nt`.
The concrete positivity/eigenvalue proof is supplied as a hypothesis because
`TransferSystem` stores only kernels and path-measure dictionaries, not an
operator-level positive trace API. -/
theorem partition_ge_groundEigenvalue_pow (Ts : TransferSystem S)
    (lambda0 : ℝ)
    (hZ : ∀ (Nt : ℕ) [NeZero Nt], lambda0 ^ Nt ≤ Ts.partition Nt)
    (Nt : ℕ) [NeZero Nt] :
    lambda0 ^ Nt ≤ Ts.partition Nt :=
  hZ Nt

/-- The one-perp envelope supplied by the GNS spectral gap.  The two summands
correspond to the two ways around the finite periodic circle. -/
noncomputable def finitePeriodicPerpEnvelope (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν)
    (G : GappedTransfer (Lp ℝ 2 Ts.ν)) (γ : ℝ)
    (Nt : ℕ) [NeZero Nt] (t : ZMod Nt) : ℝ :=
  ‖G.vacuumPerp (A.M G.vacuum)‖ * ‖G.vacuumPerp (B.M G.vacuum)‖ *
    (γ ^ t.val + γ ^ (Nt - t.val))

/-- Nonnegativity of the one-perp envelope when the supplied decay parameter
is nonnegative. -/
theorem finitePeriodicPerpEnvelope_nonneg (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν)
    (G : GappedTransfer (Lp ℝ 2 Ts.ν)) {γ : ℝ} (hγ : 0 ≤ γ)
    (Nt : ℕ) [NeZero Nt] (t : ZMod Nt) :
    0 ≤ finitePeriodicPerpEnvelope Ts A B G γ Nt t := by
  unfold finitePeriodicPerpEnvelope
  exact mul_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (add_nonneg (pow_nonneg hγ _) (pow_nonneg hγ _))

/-- Residual left after removing the two one-perp finite-periodic legs from
the absolute connected path-measure two-point function.

This is intentionally the combined `R*R + denominator + one-point
finite-volume correction` object from the design document.  It is defined
at the scalar bridge level because the current abstract kernel API has no
trace-class representation of the signed kernel `T'`. -/
noncomputable def finitePeriodicBridgeResidual (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν)
    (G : GappedTransfer (Lp ℝ 2 Ts.ν)) (γ : ℝ)
    (Nt : ℕ) [NeZero Nt] (t : ZMod Nt) : ℝ :=
  |pathConnectedTwoPoint Ts A B Nt t|
    - finitePeriodicPerpEnvelope Ts A B G γ Nt t

/-- Observable-vector bridge: applying a multiplication CLM to the packaged
vacuum has pointwise representative `A * Omega`. -/
theorem observable_vacuum_coeFn (Ts : TransferSystem S)
    (Ω : S → ℝ) (A : MultiplicationCLMContract Ts.ν)
    (G : GappedTransfer (Lp ℝ 2 Ts.ν))
    (hVac : (⇑G.vacuum : S → ℝ) =ᵐ[Ts.ν] Ω) :
    (⇑(A.M G.vacuum) : S → ℝ) =ᵐ[Ts.ν] fun x => A.A x * Ω x := by
  exact (A.spec G.vacuum).trans (hVac.mono fun x hx => by simp [hx])

/-- Hypothesis package for the finite-periodic remainder.

`remainder_bound` is the isolated analytic input of Piece E1.  For a concrete
kernel model it should be proved by:

* using the rank-one split `rankOne_kernel_split` on both kernel powers,
* bounding the two one-perp legs through the GNS gap estimate,
* controlling the `R*R` term by the model's trace/HS estimate,
* bounding the denominator correction with `partition_ground_bound`,
* bounding finite-volume one-point corrections.

The structure keeps `C_rem` and its nonnegativity visible while making the
combined scalar estimate an explicit proof obligation. -/
structure RemainderHypothesis (Ts : TransferSystem S) (Ω : S → ℝ)
    (lambda0 γ : ℝ) (A B : MultiplicationCLMContract Ts.ν) where
  /-- The gapped normalized transfer acting on `L^2(nu)`. -/
  G : GappedTransfer (Lp ℝ 2 Ts.ν)
  /-- The packaged vacuum is represented by the ground-state function `Omega`. -/
  vacuum_coeFn : (⇑G.vacuum : S → ℝ) =ᵐ[Ts.ν] Ω
  /-- The gap parameter in `G` is the scalar `gamma` used in this bridge. -/
  gap_eq : G.gap = γ
  /-- Constant controlling the combined finite-periodic remainder. -/
  C_rem : ℝ
  /-- The remainder constant is nonnegative. -/
  C_rem_nonneg : 0 ≤ C_rem
  /-- Denominator lower bound `Z_Nt >= lambda_0^Nt`. -/
  partition_ground_bound : ∀ (Nt : ℕ) [NeZero Nt], lambda0 ^ Nt ≤ Ts.partition Nt
  /-- Combined `R*R + denominator + finite-volume one-point` remainder
  estimate, after the two one-perp legs have been removed. -/
  remainder_bound : ∀ (Nt : ℕ) [NeZero Nt] (t : ZMod Nt),
    0 < t.val → t.val < Nt →
      finitePeriodicBridgeResidual Ts A B G γ Nt t ≤ C_rem * γ ^ Nt

namespace RemainderHypothesis

variable {Ts : TransferSystem S} {Ω : S → ℝ} {lambda0 γ : ℝ}
variable {A B : MultiplicationCLMContract Ts.ν}

/-- The denominator lower bound as a theorem attached to the remainder
hypothesis. -/
theorem partition_ge (hRem : RemainderHypothesis Ts Ω lambda0 γ A B)
    (Nt : ℕ) [NeZero Nt] :
    lambda0 ^ Nt ≤ Ts.partition Nt :=
  partition_ge_groundEigenvalue_pow Ts lambda0 hRem.partition_ground_bound Nt

/-- The observable-vector bridge for `A`, using the vacuum stored in the
remainder hypothesis. -/
theorem observable_left_coeFn (hRem : RemainderHypothesis Ts Ω lambda0 γ A B) :
    (⇑(A.M hRem.G.vacuum) : S → ℝ) =ᵐ[Ts.ν] fun x => A.A x * Ω x :=
  observable_vacuum_coeFn Ts Ω A hRem.G hRem.vacuum_coeFn

/-- The observable-vector bridge for `B`, using the vacuum stored in the
remainder hypothesis. -/
theorem observable_right_coeFn (hRem : RemainderHypothesis Ts Ω lambda0 γ A B) :
    (⇑(B.M hRem.G.vacuum) : S → ℝ) =ᵐ[Ts.ν] fun x => B.A x * Ω x :=
  observable_vacuum_coeFn Ts Ω B hRem.G hRem.vacuum_coeFn

end RemainderHypothesis

/-- Algebraic conversion from a residual estimate to the final connected
finite-periodic bound. -/
theorem pathConnectedTwoPoint_le_of_remainder
    (Ts : TransferSystem S) (Ω : S → ℝ) (lambda0 γ : ℝ)
    (A B : MultiplicationCLMContract Ts.ν)
    (hRem : RemainderHypothesis Ts Ω lambda0 γ A B)
    (Nt : ℕ) [NeZero Nt] (t : ZMod Nt)
    (ht : 0 < t.val) (htn : t.val < Nt) :
    |pathConnectedTwoPoint Ts A B Nt t|
      ≤ finitePeriodicPerpEnvelope Ts A B hRem.G γ Nt t
        + hRem.C_rem * γ ^ Nt := by
  have h := hRem.remainder_bound Nt t ht htn
  unfold finitePeriodicBridgeResidual at h
  linarith

/-- **Finite-periodic GNS dictionary bridge.**

The connected path-measure two-point function is bounded by the two
one-perp legs around the periodic circle plus the supplied finite-periodic
remainder.  The remainder hypothesis is the concrete model's obligation to
discharge the `R*R`, denominator, and one-point finite-volume corrections.
-/
theorem pathMeasure_connected_two_point_finite_periodic_bound
    (Ts : TransferSystem S) (Ω : S → ℝ) (lambda0 γ : ℝ)
    (A B : MultiplicationCLMContract Ts.ν)
    (hRem : RemainderHypothesis Ts Ω lambda0 γ A B)
    (Nt : ℕ) [NeZero Nt] (t : ZMod Nt)
    (ht : 0 < t.val) (htn : t.val < Nt) :
    |∫ ψ, A.A (ψ 0) * B.A (ψ t) ∂(Ts.pathMeasure Nt)
        - (∫ ψ, A.A (ψ 0) ∂(Ts.pathMeasure Nt)) *
          (∫ ψ, B.A (ψ t) ∂(Ts.pathMeasure Nt))|
      ≤ ‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖ *
          ‖hRem.G.vacuumPerp (B.M hRem.G.vacuum)‖ *
          (γ ^ t.val + γ ^ (Nt - t.val))
        + hRem.C_rem * γ ^ Nt := by
  simpa [pathConnectedTwoPoint, pathTwoPoint, finiteVolumeMean,
    finitePeriodicPerpEnvelope] using
    pathConnectedTwoPoint_le_of_remainder Ts Ω lambda0 γ A B hRem Nt t ht htn

end ReflectionPositivity
