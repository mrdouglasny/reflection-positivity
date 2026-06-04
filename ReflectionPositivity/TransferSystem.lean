/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.Fin.Tuple.Basic
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

noncomputable def kernelPower (ν : Measure S) (k : S → S → ℝ) : ℕ → S → S → ℝ
  | 0 => k
  | (m + 1) => fun x y => ∫ z, kernelPower ν k m x z * k z y ∂ν

noncomputable def openChainDensity (k : S → S → ℝ) : (m : ℕ) → S → S → (Fin m → S) → ℝ
  | 0 => fun x y _ => k x y
  | m + 1 => fun x y q => openChainDensity k m x (q (Fin.last m)) (Fin.init q) *
      k (q (Fin.last m)) y

def openChainVertices (m : ℕ) (x y : S) (q : Fin m → S) : Fin (m + 2) → S :=
  Fin.snoc (Fin.cons x q) y

noncomputable def openChainProduct (k : S → S → ℝ) (m : ℕ) (x y : S)
    (q : Fin m → S) : ℝ :=
  ∏ i : Fin (m + 1),
    k (openChainVertices m x y q i.castSucc) (openChainVertices m x y q i.succ)

noncomputable def periodicPathDensity (k : S → S → ℝ) (n : ℕ) [NeZero n]
    (ψ : ZMod n → S) : ℝ :=
  ∏ t : ZMod n, k (ψ t) (ψ (t + 1))

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
  /-- The reference measure is sigma-finite, as required by the product-integral API. -/
  ν_sigmaFinite : SigmaFinite ν
  /-- Integrability for the open-chain Fubini step defining kernel composition. -/
  openChain_step_integrable : ∀ (m : ℕ) (x y : S),
    Integrable
      (fun p : S × (Fin m → S) => openChainDensity k m x p.1 p.2 * k p.1 y)
      (ν.prod (Measure.pi (fun _ : Fin m => ν)))
  /-- Integrability for peeling one vertex off the closed chain. -/
  partition_integrable : ∀ (m : ℕ),
    Integrable
      (fun p : S × (Fin m → S) => openChainProduct k m p.1 p.1 p.2)
      (ν.prod (Measure.pi (fun _ : Fin m => ν)))
  /-- The periodic path density is measurable. -/
  pathDensity_measurable : ∀ (n : ℕ) [NeZero n], Measurable (periodicPathDensity k n)
  /-- ⚠ TEMPORARY ASSUMED HYPOTHESIS (NOT a side-condition — this is the two-point
  numerator identity itself, i.e. essentially the conclusion of `twoPoint_dictionary`).
  It must be **proved and removed**: the two-arc generalization of `partition_eq_trace`
  (peel slices `0` and `t`, fold the arcs `0→t` and `t→0` into `kPow (t-1)` / `kPow (n-t-1)`
  via the same `openChain_fold` machinery). Until then `twoPoint_dictionary` is only
  conditional. -/
  twoPoint_fubini : ∀ (n : ℕ) [NeZero n] {t : ℕ} (_ : 0 < t) (_ : t < n)
      (A B : S → ℝ),
    ∫ ψ, periodicPathDensity k n ψ * (A (ψ 0) * B (ψ (t : ZMod n)))
      ∂(Measure.pi (fun _ : ZMod n => ν)) =
    ∫ x, ∫ y, A x * kernelPower ν k (t - 1) x y *
        (B y * kernelPower ν k (n - t - 1) y x) ∂ν ∂ν

namespace TransferSystem

/-- The `(m+1)`-fold composition of the kernel: `kPow 0 = k` (kernel of `T¹`), and
`kPow (m+1) x y = ∫ kPow m x z · k z y dν z` (kernel of `T^{m+2}`). So `kPow m` is the
kernel of `T^{m+1}`, i.e. the integral over `m` intermediate slices. -/
noncomputable def kPow (Ts : TransferSystem S) : ℕ → S → S → ℝ
  := kernelPower Ts.ν Ts.k

@[simp] theorem kPow_zero (Ts : TransferSystem S) : Ts.kPow 0 = Ts.k := rfl

theorem kPow_succ (Ts : TransferSystem S) (m : ℕ) (x y : S) :
    Ts.kPow (m + 1) x y = ∫ z, Ts.kPow m x z * Ts.k z y ∂Ts.ν := rfl

/-- The transfer step on slice-amplitudes: `(applyT g) y = ∫ z, g z · k z y dν`
(the action of the transfer operator `T` on a function of the slice). -/
noncomputable def applyT (Ts : TransferSystem S) (g : S → ℝ) (y : S) : ℝ :=
  ∫ z, g z * Ts.k z y ∂Ts.ν

/-- `kPow m x` is the `m`-fold transfer step applied to `k x`: `kPow m x = Tᵐ (k x ·)`. -/
theorem kPow_eq_iterT (Ts : TransferSystem S) (m : ℕ) (x : S) :
    Ts.kPow m x = (Ts.applyT)^[m] (Ts.k x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      funext y
      rw [kPow_succ, Function.iterate_succ_apply', ← ih]
      rfl

/-- The iterated kernels are nonnegative. -/
theorem kPow_nonneg (Ts : TransferSystem S) (m : ℕ) (x y : S) : 0 ≤ Ts.kPow m x y := by
  induction m generalizing x y with
  | zero => exact Ts.k_nonneg x y
  | succ m ih =>
      rw [kPow_succ]
      exact integral_nonneg (fun z => mul_nonneg (ih x z) (Ts.k_nonneg z y))

omit [MeasurableSpace S] in
lemma cons_comp_castSucc_eq_cons_init (m : ℕ) (x : S) (q : Fin (m + 1) → S) :
    (fun i : Fin (m + 1) => @Fin.cons (m + 1) (fun _ => S) x q i.castSucc)
      = @Fin.cons m (fun _ => S) x (Fin.init q) := by
  ext i
  cases i using Fin.cases with
  | zero =>
      simp [Fin.cons]
  | succ i =>
      rw [show i.succ.castSucc = i.castSucc.succ by rfl]
      simp [Fin.cons, Fin.init]

omit [MeasurableSpace S] in
lemma cons_last_eq (m : ℕ) (x : S) (q : Fin (m + 1) → S) :
    @Fin.cons (m + 1) (fun _ => S) x q (Fin.last (m + 1)) = q (Fin.last m) := by
  rw [show Fin.last (m + 1) = (Fin.last m).succ by rfl]
  exact @Fin.cons_succ (m + 1) (fun _ => S) x q (Fin.last m)

set_option linter.flexible false in
omit [MeasurableSpace S] in
lemma openChainVertices_prefix_current (m : ℕ) (x y : S) (q : Fin (m + 1) → S)
    (i : Fin (m + 1)) :
    openChainVertices (m + 1) x y q i.castSucc.castSucc =
      openChainVertices m x (q (Fin.last m)) (Fin.init q) i.castSucc := by
  have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.2
  simpa [openChainVertices, Fin.snoc, hi] using
    congr_fun (cons_comp_castSucc_eq_cons_init m x q) i

set_option linter.flexible false in
omit [MeasurableSpace S] in
lemma openChainVertices_prefix_next (m : ℕ) (x y : S) (q : Fin (m + 1) → S)
    (i : Fin (m + 1)) :
    openChainVertices (m + 1) x y q i.castSucc.succ =
      openChainVertices m x (q (Fin.last m)) (Fin.init q) i.succ := by
  cases i using Fin.lastCases with
  | last =>
      simp [openChainVertices, Fin.snoc]
      change @Fin.cons (m + 1) (fun _ => S) x q (Fin.last (m + 1)) = q (Fin.last m)
      exact cons_last_eq m x q
  | cast i =>
      simpa [openChainVertices, Fin.snoc] using
        congr_fun (cons_comp_castSucc_eq_cons_init m x q) i.succ

lemma openChain_fold (Ts : TransferSystem S) (m : ℕ) (x y : S) :
    ∫ q : Fin m → S, openChainDensity Ts.k m x y q
      ∂(Measure.pi (fun _ : Fin m => Ts.ν)) = Ts.kPow m x y := by
  letI := Ts.ν_sigmaFinite
  induction m generalizing x y with
  | zero =>
      simp [openChainDensity, measureReal_def, kPow, kernelPower]
  | succ m ih =>
      rw [kPow_succ]
      rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => Ts.ν)
        (Fin.last m)).symm).integral_comp']
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      simp_rw [Fin.insertNthEquiv_last]
      simp only [Fin.snocEquiv_apply, openChainDensity, Fin.snoc_last]
      have hinit : ∀ p : S × (Fin m → S),
          Fin.init ((Fin.snocEquiv (fun _ : Fin (m + 1) => S)) p) = p.2 := by
        intro p
        ext i
        simp [Fin.snocEquiv_apply, Fin.init]
      simp_rw [hinit]
      rw [integral_prod _ (Ts.openChain_step_integrable m x y)]
      simp_rw [integral_mul_const]
      simp_rw [ih]

omit [MeasurableSpace S] in
lemma openChainProduct_eq_density (k : S → S → ℝ) (m : ℕ) (x y : S)
    (q : Fin m → S) :
    openChainProduct k m x y q = openChainDensity k m x y q := by
  induction m generalizing x y with
  | zero =>
      simp [openChainProduct, openChainDensity, openChainVertices, Fin.snoc, Fin.cons]
  | succ m ih =>
      rw [openChainProduct, Fin.prod_univ_castSucc]
      have hprod :
          (∏ i : Fin (m + 1),
              k (openChainVertices (m + 1) x y q i.castSucc.castSucc)
                (openChainVertices (m + 1) x y q i.castSucc.succ))
            = openChainProduct k m x (q (Fin.last m)) (Fin.init q) := by
        rw [openChainProduct]
        apply Finset.prod_congr rfl
        intro i _
        rw [openChainVertices_prefix_current, openChainVertices_prefix_next]
      have hlast :
          k (openChainVertices (m + 1) x y q (Fin.last (m + 1)).castSucc)
            (openChainVertices (m + 1) x y q (Fin.last (m + 1)).succ)
            = k (q (Fin.last m)) y := by
        simp [openChainVertices, Fin.snoc]
      rw [hprod, hlast, ih]
      rfl

set_option linter.flexible false in
omit [MeasurableSpace S] in
lemma cyclicProduct_cons_eq_openChainProduct (k : S → S → ℝ) (m : ℕ) (x : S)
    (q : Fin m → S) :
    (∏ i : Fin (m + 1), k ((@Fin.cons m (fun _ => S) x q) i)
      ((@Fin.cons m (fun _ => S) x q) (i + 1))) =
      openChainProduct k m x x q := by
  rw [openChainProduct]
  apply Finset.prod_congr rfl
  intro i _
  cases i using Fin.lastCases with
  | last =>
      simp [openChainVertices, Fin.snoc, Fin.cons]
  | cast i =>
      simp [openChainVertices, Fin.snoc, Fin.cons]
      rw [show (i.castSucc.succ.castLT i.succ.isLt : Fin (m + 1)) = i.succ by rfl]
      simp

/-- The path density on `ZMod n → S`: `∏_t k(ψ_t, ψ_{t+1})`. -/
noncomputable def pathDensity (Ts : TransferSystem S) (n : ℕ) [NeZero n]
    (ψ : ZMod n → S) : ℝ :=
  periodicPathDensity Ts.k n ψ

/-- The partition function `Z_n = ∫ ∏_t k(ψ_t,ψ_{t+1}) dν^{⊗n} = Tr(Tⁿ)`. -/
noncomputable def partition (Ts : TransferSystem S) (n : ℕ) [NeZero n] : ℝ :=
  ∫ ψ, Ts.pathDensity n ψ ∂(Measure.pi (fun _ : ZMod n => Ts.ν))

/-- The normalized periodic path (Gibbs) measure on `ZMod n → S`. -/
noncomputable def pathMeasure (Ts : TransferSystem S) (n : ℕ) [NeZero n] :
    Measure (ZMod n → S) :=
  (ENNReal.ofReal (Ts.partition n))⁻¹ •
    (Measure.pi (fun _ : ZMod n => Ts.ν)).withDensity
      (fun ψ => ENNReal.ofReal (Ts.pathDensity n ψ))

lemma pathDensity_nonneg (Ts : TransferSystem S) (n : ℕ) [NeZero n] (ψ : ZMod n → S) :
    0 ≤ Ts.pathDensity n ψ := by
  unfold pathDensity periodicPathDensity
  exact Finset.prod_nonneg fun i _ => Ts.k_nonneg _ _

/-- **Partition = trace.** `Z_n = ∫ x, kPow (n−1) x x dν` — integrating the closed periodic
chain of `n` kernels down to the diagonal of the `n`-step kernel. -/
theorem partition_eq_trace (Ts : TransferSystem S) (n : ℕ) [NeZero n] :
    Ts.partition n = ∫ x, Ts.kPow (n - 1) x x ∂Ts.ν := by
  letI := Ts.ν_sigmaFinite
  cases n with
  | zero =>
      cases NeZero.ne 0 rfl
  | succ m =>
      rw [partition]
      simp only [Nat.add_one_sub_one]
      let e := (ZMod.finEquiv (m + 1)).toEquiv
      rw [← (measurePreserving_piCongrLeft (fun _ : ZMod (m + 1) => Ts.ν) e).integral_comp']
      dsimp [e]
      change (∫ ψ : Fin (m + 1) → S,
          ∏ i : Fin (m + 1), Ts.k (ψ i) (ψ (i + 1))
          ∂Measure.pi (fun _ : Fin (m + 1) => Ts.ν)) =
        ∫ x, Ts.kPow m x x ∂Ts.ν
      rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => Ts.ν)
        0).symm).integral_comp']
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      simp_rw [Fin.insertNthEquiv_zero]
      simp only [Fin.consEquiv_apply]
      simp_rw [cyclicProduct_cons_eq_openChainProduct]
      rw [integral_prod _ (Ts.partition_integrable m)]
      simp_rw [openChainProduct_eq_density]
      simp_rw [openChain_fold Ts]

lemma partition_nonneg (Ts : TransferSystem S) (n : ℕ) [NeZero n] :
    0 ≤ Ts.partition n := by
  rw [partition_eq_trace]
  exact integral_nonneg fun x => Ts.kPow_nonneg (n - 1) x x

/-- **The two-point Feynman–Kac dictionary.** For `0 < t < n` and bounded observables
`A B : S → ℝ`, the time-`(0,t)` correlation of the path measure is the kernel-composition
("trace") ratio
`∫ A(ψ₀)·B(ψ_t) dμ_n = Z_n⁻¹ · ∫∫ A(x)·kPow_{t−1}(x,y)·B(y)·kPow_{n−t−1}(y,x) dν dν`,
i.e. `Tr(M_A Tᵗ M_B T^{n−t})/Tr(Tⁿ)`. Proved by integrating out the `n−2` intermediate
slices (iterated Fubini), composing the bonds `0→t` into `T^t`'s kernel and `t→0` (around
the circle) into `T^{n−t}`'s kernel. -/
theorem twoPoint_dictionary (Ts : TransferSystem S) (n : ℕ) [NeZero n]
    {t : ℕ} (ht0 : 0 < t) (htn : t < n) (A B : S → ℝ)
    (_hA : Measurable A) (_hB : Measurable B) :
    ∫ ψ, A (ψ 0) * B (ψ (t : ZMod n)) ∂(Ts.pathMeasure n)
      = (Ts.partition n)⁻¹ *
        ∫ x, ∫ y, A x * Ts.kPow (t - 1) x y * (B y * Ts.kPow (n - t - 1) y x)
          ∂Ts.ν ∂Ts.ν := by
  rw [pathMeasure]
  rw [integral_smul_measure]
  change ((ENNReal.ofReal (Ts.partition n))⁻¹).toReal •
      (∫ x, A (x 0) * B (x (t : ZMod n))
        ∂(Measure.pi (fun _ : ZMod n => Ts.ν)).withDensity
          (ENNReal.ofReal ∘ Ts.pathDensity n)) =
    (Ts.partition n)⁻¹ *
      ∫ x, ∫ y, A x * Ts.kPow (t - 1) x y * (B y * Ts.kPow (n - t - 1) y x)
        ∂Ts.ν ∂Ts.ν
  have hdensity_meas : Measurable (ENNReal.ofReal ∘ Ts.pathDensity n) := by
    change Measurable (ENNReal.ofReal ∘ periodicPathDensity Ts.k n)
    exact ENNReal.measurable_ofReal.comp (Ts.pathDensity_measurable n)
  rw [integral_withDensity_eq_integral_toReal_smul hdensity_meas ?_]
  · simp_rw [Function.comp_apply]
    simp_rw [show ∀ ψ : ZMod n → S,
        (ENNReal.ofReal (Ts.pathDensity n ψ)).toReal = Ts.pathDensity n ψ
      from fun ψ => ENNReal.toReal_ofReal (Ts.pathDensity_nonneg n ψ)]
    simp_rw [smul_eq_mul]
    change ((ENNReal.ofReal (Ts.partition n))⁻¹).toReal *
        (∫ x : ZMod n → S, Ts.pathDensity n x * (A (x 0) * B (x (t : ZMod n)))
          ∂Measure.pi (fun _ : ZMod n => Ts.ν)) =
      (Ts.partition n)⁻¹ *
        ∫ x, ∫ y, A x * kernelPower Ts.ν Ts.k (t - 1) x y *
          (B y * kernelPower Ts.ν Ts.k (n - t - 1) y x) ∂Ts.ν ∂Ts.ν
    rw [← Ts.twoPoint_fubini n ht0 htn A B]
    congr 1
    rw [ENNReal.toReal_inv]
    rw [ENNReal.toReal_ofReal]
    exact Ts.partition_nonneg n
  · exact Filter.Eventually.of_forall fun ψ => ENNReal.ofReal_lt_top

end TransferSystem

end ReflectionPositivity
