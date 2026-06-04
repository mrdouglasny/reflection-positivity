/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ZMod.Basic

/-!
# Abstract periodic transfer-matrix (Feynman–Kac) dictionary

The transfer-matrix / Feynman–Kac correspondence at its natural generality: a single
time-slice state space `(S, ν)` together with a symmetric nonnegative **transfer kernel**
`k : S → S → ℝ`. On the periodic time lattice `ZMod n` it induces the **path measure**
with density `∏_t k(ψ_t, ψ_{t+1})` against `ν^{⊗n}`, and its time-correlations are given by
compositions of `k` — the kernel-iterate form of `Tr(M_A Tᵗ M_B T^{n−t}) / Tr(Tⁿ)`. No
Gaussian, no field theory, and (crucially for formalization) **no abstract trace-class
operator API**: everything is iterated integrals (Fubini) of kernel products. A concrete
lattice QFT (e.g. pphi2's φ⁴₂ cylinder, with `k(x,y) = w(x)·G(x−y)·w(y)`) instantiates this.

## Main definitions
* `TransferSystem S` — `(ν, k)` with `k` symmetric, nonnegative, measurable.
* `TransferSystem.kPow Ts m` — the `(m+1)`-fold composition of `k` (kernel of `T^{m+1}`).
* `TransferSystem.partition Ts n` — `Z_n = ∫ ∏_t k(ψ_t,ψ_{t+1}) dν^{⊗n} = Tr(Tⁿ)`.
* `TransferSystem.pathMeasure Ts n` — the normalized periodic path measure on `ZMod n → S`.

## Main results (in progress)
* `partition_eq_trace` — `Z_n = ∫ x, kPow (n−1) x x dν`.
* `twoPoint_dictionary` — `∫ A(ψ₀)·B(ψ_t) dμ_n = Z_n⁻¹ · ∫∫ A·kPow_{t}·B·kPow_{n−t}`.
-/

open MeasureTheory

namespace ReflectionPositivity

variable {S : Type*} [MeasurableSpace S]

/-- An abstract transfer system: a single-time-slice state space `(S, ν)` with a symmetric
nonnegative transfer kernel `k`. The periodic path measure on `ZMod n → S` has density
`∏_t k(ψ_t, ψ_{t+1})` against `ν^{⊗n}`. -/
structure TransferSystem (S : Type*) [MeasurableSpace S] where
  /-- The single-slice reference measure. -/
  ν : Measure S
  /-- The transfer kernel. -/
  k : S → S → ℝ
  /-- The kernel is symmetric (the transfer operator is self-adjoint). -/
  k_symm : ∀ x y, k x y = k y x
  /-- The kernel is nonnegative (positivity-improving / Perron–Frobenius setting). -/
  k_nonneg : ∀ x y, 0 ≤ k x y
  /-- The kernel is measurable. -/
  k_meas : Measurable (Function.uncurry k)

namespace TransferSystem

/-- The `(m+1)`-fold composition of the kernel: `kPow 0 = k` (kernel of `T¹`), and
`kPow (m+1) x y = ∫ kPow m x z · k z y dν z` (kernel of `T^{m+2}`). So `kPow m` is the
kernel of `T^{m+1}`, i.e. the integral over `m` intermediate slices. -/
noncomputable def kPow (Ts : TransferSystem S) : ℕ → S → S → ℝ
  | 0 => Ts.k
  | (m + 1) => fun x y => ∫ z, kPow Ts m x z * Ts.k z y ∂Ts.ν

@[simp] theorem kPow_zero (Ts : TransferSystem S) : Ts.kPow 0 = Ts.k := rfl

theorem kPow_succ (Ts : TransferSystem S) (m : ℕ) (x y : S) :
    Ts.kPow (m + 1) x y = ∫ z, Ts.kPow m x z * Ts.k z y ∂Ts.ν := rfl

/-- The path density on `ZMod n → S`: `∏_t k(ψ_t, ψ_{t+1})`. -/
noncomputable def pathDensity (Ts : TransferSystem S) (n : ℕ) [NeZero n]
    (ψ : ZMod n → S) : ℝ :=
  ∏ t : ZMod n, Ts.k (ψ t) (ψ (t + 1))

/-- The partition function `Z_n = ∫ ∏_t k(ψ_t,ψ_{t+1}) dν^{⊗n} = Tr(Tⁿ)`. -/
noncomputable def partition (Ts : TransferSystem S) (n : ℕ) [NeZero n] : ℝ :=
  ∫ ψ, Ts.pathDensity n ψ ∂(Measure.pi (fun _ : ZMod n => Ts.ν))

/-- The normalized periodic path (Gibbs) measure on `ZMod n → S`. -/
noncomputable def pathMeasure (Ts : TransferSystem S) (n : ℕ) [NeZero n] :
    Measure (ZMod n → S) :=
  (ENNReal.ofReal (Ts.partition n))⁻¹ •
    (Measure.pi (fun _ : ZMod n => Ts.ν)).withDensity
      (fun ψ => ENNReal.ofReal (Ts.pathDensity n ψ))

/-- **Partition = trace.** `Z_n = ∫ x, kPow (n−1) x x dν` — integrating the closed periodic
chain of `n` kernels down to the diagonal of the `n`-step kernel. -/
theorem partition_eq_trace (Ts : TransferSystem S) (n : ℕ) [NeZero n] :
    Ts.partition n = ∫ x, Ts.kPow (n - 1) x x ∂Ts.ν := by
  sorry

/-- **The two-point Feynman–Kac dictionary.** For `0 < t < n` and bounded observables
`A B : S → ℝ`, the time-`(0,t)` correlation of the path measure is the kernel-composition
("trace") ratio
`∫ A(ψ₀)·B(ψ_t) dμ_n = Z_n⁻¹ · ∫∫ A(x)·kPow_{t−1}(x,y)·B(y)·kPow_{n−t−1}(y,x) dν dν`,
i.e. `Tr(M_A Tᵗ M_B T^{n−t})/Tr(Tⁿ)`. Proved by integrating out the `n−2` intermediate
slices (iterated Fubini), composing the bonds `0→t` into `T^t`'s kernel and `t→0` (around
the circle) into `T^{n−t}`'s kernel. -/
theorem twoPoint_dictionary (Ts : TransferSystem S) (n : ℕ) [NeZero n]
    {t : ℕ} (ht0 : 0 < t) (htn : t < n) (A B : S → ℝ)
    (hA : Measurable A) (hB : Measurable B) :
    ∫ ψ, A (ψ 0) * B (ψ (t : ZMod n)) ∂(Ts.pathMeasure n)
      = (Ts.partition n)⁻¹ *
        ∫ x, ∫ y, A x * Ts.kPow (t - 1) x y * (B y * Ts.kPow (n - t - 1) y x)
          ∂Ts.ν ∂Ts.ν := by
  sorry

end TransferSystem

end ReflectionPositivity
