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
* `twoPoint_dictionary` — `∫ A(ψ₀)·B(ψ_t) dμ_n = Z_n⁻¹ · ∫∫ A·kPow_{t−1}·B·kPow_{n−t−1}`
  (with `kPow m` the kernel of `Tᵐ⁺¹`, so `kPow_{t−1}`/`kPow_{n−t−1}` are `Tᵗ`/`T^{n−t}`).
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

noncomputable def twoPointSplitDensity (k : S → S → ℝ) (a b : ℕ) (A B : S → ℝ)
    (p : S × (S × ((Fin a → S) × (Fin b → S)))) : ℝ :=
  openChainProduct k a p.1 p.2.1 p.2.2.1 *
    openChainProduct k b p.2.1 p.1 p.2.2.2 * A p.1 * B p.2.1

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

set_option linter.flexible false in
omit [MeasurableSpace S] in
lemma append_left_cyclicProduct_eq_openChainProduct (k : S → S → ℝ) (a b : ℕ)
    (x y : S) (q : Fin a → S) (r : Fin b → S) :
    (∏ i : Fin (a + 1),
        k (Fin.append (@Fin.cons a (fun _ => S) x q) (@Fin.cons b (fun _ => S) y r)
            (Fin.castAdd (b + 1) i))
          (Fin.append (@Fin.cons a (fun _ => S) x q) (@Fin.cons b (fun _ => S) y r)
            (Fin.castAdd (b + 1) i + 1))) =
      openChainProduct k a x y q := by
  rw [openChainProduct]
  apply Finset.prod_congr rfl
  intro i _
  cases i using Fin.lastCases with
  | last =>
      have hnext :
          Fin.castAdd (b + 1) (Fin.last a) + 1 =
            Fin.natAdd (a + 1) (0 : Fin (b + 1)) := by
        have hone : (1 : Fin ((a + 1) + (b + 1))).val = 1 := by
          change 1 % ((a + 1) + (b + 1)) = 1
          exact Nat.mod_eq_of_lt (by omega)
        ext
        simp only [Fin.val_add, hone, Fin.val_castAdd, Fin.val_last, Fin.val_natAdd,
          Fin.val_zero]
        rw [Nat.mod_eq_of_lt]
        · simp
      rw [hnext]
      rw [Fin.append_right]
      simp [openChainVertices, Fin.snoc, Fin.cons]
  | cast i =>
      have hnext :
          Fin.castAdd (b + 1) i.castSucc + 1 = Fin.castAdd (b + 1) i.succ := by
        have hone : (1 : Fin ((a + 1) + (b + 1))).val = 1 := by
          change 1 % ((a + 1) + (b + 1)) = 1
          exact Nat.mod_eq_of_lt (by omega)
        ext
        simp only [Fin.val_add, hone, Fin.val_castAdd, Fin.val_succ]
        rw [Nat.mod_eq_of_lt]
        · simp
        · omega
      rw [hnext]
      simp [openChainVertices, Fin.snoc, Fin.cons]
      rw [show (i.castSucc.succ.castLT i.succ.isLt : Fin (a + 1)) = i.succ by rfl]
      simp

set_option linter.flexible false in
set_option linter.unnecessarySimpa false in
omit [MeasurableSpace S] in
lemma append_right_cyclicProduct_eq_openChainProduct (k : S → S → ℝ) (a b : ℕ)
    (x y : S) (q : Fin a → S) (r : Fin b → S) :
    (∏ i : Fin (b + 1),
        k (Fin.append (@Fin.cons a (fun _ => S) x q) (@Fin.cons b (fun _ => S) y r)
            (Fin.natAdd (a + 1) i))
          (Fin.append (@Fin.cons a (fun _ => S) x q) (@Fin.cons b (fun _ => S) y r)
            (Fin.natAdd (a + 1) i + 1))) =
      openChainProduct k b y x r := by
  rw [openChainProduct]
  apply Finset.prod_congr rfl
  intro i _
  cases i using Fin.lastCases with
  | last =>
      have hcur :
          Fin.natAdd (a + 1) (Fin.last b) = Fin.last (a + 1 + b) := by
        ext
        simp
      have hnext :
          Fin.natAdd (a + 1) (Fin.last b) + 1 =
            (0 : Fin ((a + 1) + (b + 1))) := by
        ext
        simp
      rw [hnext]
      rw [Fin.append_right]
      rw [show (0 : Fin ((a + 1) + (b + 1))) =
          Fin.castAdd (b + 1) (0 : Fin (a + 1)) by rfl]
      rw [Fin.append_left]
      simp [openChainVertices, Fin.snoc, Fin.cons]
  | cast i =>
      have hnext :
          (Fin.natAdd (a + 1) i.castSucc + 1 : Fin ((a + 1) + (b + 1))) =
            Fin.natAdd (a + 1) i.succ := by
        have hone : (1 : Fin ((a + 1) + (b + 1))).val = 1 := by
          change 1 % ((a + 1) + (b + 1)) = 1
          exact Nat.mod_eq_of_lt (by omega)
        ext
        simp only [Fin.val_add, hone, Fin.val_natAdd, Fin.val_succ]
        rw [Nat.mod_eq_of_lt]
        · simp [Nat.add_assoc]
        · have hi : ↑i.castSucc + 1 < b + 1 := by
            simpa using Nat.succ_lt_succ i.isLt
          simpa [Nat.add_assoc] using Nat.add_lt_add_left hi (a + 1)
      rw [hnext]
      simp [openChainVertices, Fin.snoc, Fin.cons]
      rw [show (i.castSucc.succ.castLT i.succ.isLt : Fin (b + 1)) = i.succ by rfl]
      simp

omit [MeasurableSpace S] in
lemma cyclicProduct_append_cons_eq_openChainProducts (k : S → S → ℝ) (a b : ℕ)
    (x y : S) (q : Fin a → S) (r : Fin b → S) :
    (∏ i : Fin ((a + 1) + (b + 1)),
        k (Fin.append (@Fin.cons a (fun _ => S) x q) (@Fin.cons b (fun _ => S) y r) i)
          (Fin.append (@Fin.cons a (fun _ => S) x q) (@Fin.cons b (fun _ => S) y r)
            (i + 1))) =
      openChainProduct k a x y q * openChainProduct k b y x r := by
  rw [Fin.prod_univ_add]
  rw [append_left_cyclicProduct_eq_openChainProduct,
    append_right_cyclicProduct_eq_openChainProduct]

omit [MeasurableSpace S] in
lemma cyclicProduct_append_cons_eq_openChainProducts_assoc (k : S → S → ℝ) (a b : ℕ)
    (x y : S) (q : Fin a → S) (r : Fin b → S) :
    (∏ i : Fin (((a + 1) + b) + 1),
        k (Fin.append (@Fin.cons a (fun _ => S) x q) (@Fin.cons b (fun _ => S) y r) i)
          (Fin.append (@Fin.cons a (fun _ => S) x q) (@Fin.cons b (fun _ => S) y r)
            (i + 1))) =
      openChainProduct k a x y q * openChainProduct k b y x r := by
  simpa using cyclicProduct_append_cons_eq_openChainProducts k a b x y q r

omit [MeasurableSpace S] in
lemma piCongrLeft_finSumFinEquiv_sumPi_symm_eq_append (a b : ℕ)
    (q : Fin a → S) (r : Fin b → S) :
    (Equiv.piCongrLeft (fun _ : Fin (a + b) => S) finSumFinEquiv)
        ((Equiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => S)).symm (q, r)) =
      Fin.append q r := by
  ext i
  cases i using Fin.addCases with
  | left i =>
      simpa [finSumFinEquiv_apply_left, Fin.append_left] using
        (@Equiv.piCongrLeft_apply_apply (Fin a ⊕ Fin b) (Fin (a + b))
          (fun _ : Fin (a + b) => S) finSumFinEquiv
          ((Equiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => S)).symm (q, r))
          (Sum.inl i))
  | right i =>
      simpa [finSumFinEquiv_apply_right, Fin.append_right] using
        (@Equiv.piCongrLeft_apply_apply (Fin a ⊕ Fin b) (Fin (a + b))
          (fun _ : Fin (a + b) => S) finSumFinEquiv
          ((Equiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => S)).symm (q, r))
          (Sum.inr i))

set_option linter.unnecessarySimpa false in
omit [MeasurableSpace S] in
lemma insertNth_natAdd_zero_append_eq_append_cons (a b : ℕ) (y : S)
    (q : Fin a → S) (r : Fin b → S) :
    (@Fin.insertNth (a + b) (fun _ : Fin (a + b + 1) => S)
      (Fin.natAdd a (0 : Fin (b + 1))) y (Fin.append q r)) =
      Fin.append q (@Fin.cons b (fun _ => S) y r) := by
  funext i
  refine @Fin.addCases a (b + 1) (fun i =>
    (@Fin.insertNth (a + b) (fun _ : Fin (a + b + 1) => S)
      (Fin.natAdd a (0 : Fin (b + 1))) y (Fin.append q r)) i =
      Fin.append q (@Fin.cons b (fun _ => S) y r) i) ?_ ?_ i
  · intro i
    have hsucc :
        (Fin.natAdd a (0 : Fin (b + 1))).succAbove (Fin.castAdd b i) =
          Fin.castAdd (b + 1) i := by
      rw [Fin.succAbove_of_castSucc_lt]
      · rfl
      · simpa [Fin.lt_def, Fin.natAdd] using i.isLt
    rw [← hsucc, Fin.insertNth_apply_succAbove, hsucc]
    simp
  · intro i
    cases i using Fin.cases with
      | zero =>
          simp [Fin.insertNth_apply_same]
      | succ i =>
          have hsucc :
              (Fin.natAdd a (0 : Fin (b + 1))).succAbove (Fin.natAdd a i) =
                Fin.natAdd a i.succ := by
            rw [Fin.succAbove_of_le_castSucc]
            · ext
              simp [Fin.natAdd]
              omega
            · simp [Fin.le_def, Fin.natAdd]
          rw [← hsucc, Fin.insertNth_apply_succAbove, hsucc]
          simp

omit [MeasurableSpace S] in
lemma cons_piCongrLeft_finCongr_append_cons_eq_append_cons (a b : ℕ)
    (h : a + (b + 1) = (a + 1) + b) (x y : S) (q : Fin a → S) (r : Fin b → S) :
    (fun i : Fin (((a + 1) + b) + 1) =>
      @Fin.cons (((a + 1) + b)) (fun _ => S) x
        ((Equiv.piCongrLeft (fun _ : Fin ((a + 1) + b) => S) (finCongr h))
          (Fin.append q (@Fin.cons b (fun _ => S) y r))) i) =
      Fin.append (@Fin.cons a (fun _ => S) x q) (@Fin.cons b (fun _ => S) y r) := by
  rw [Fin.append_cons]
  ext i
  cases i using Fin.cases with
  | zero =>
      simp [Fin.cons]
  | succ i =>
      simp [Fin.cons, Equiv.piCongrLeft_apply_eq_cast]

/-- The path density on `ZMod n → S`: `∏_t k(ψ_t, ψ_{t+1})`. -/
noncomputable def pathDensity (Ts : TransferSystem S) (n : ℕ) [NeZero n]
    (ψ : ZMod n → S) : ℝ :=
  periodicPathDensity Ts.k n ψ

/-- The partition function `Z_n = ∫ ∏_t k(ψ_t,ψ_{t+1}) dν^{⊗n} = Tr(Tⁿ)`. -/
noncomputable def partition (Ts : TransferSystem S) (n : ℕ) [NeZero n] : ℝ :=
  ∫ ψ, Ts.pathDensity n ψ ∂(Measure.pi (fun _ : ZMod n => Ts.ν))

/-- The periodic path (Gibbs) measure on `ZMod n → S`, normalized by `Z_n = partition n`.
This is a genuine probability measure exactly when `partition n > 0` (e.g. for a
positivity-improving kernel); the dictionary theorems below carry the `Z_n⁻¹` factor
explicitly and do not require it. -/
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
      let e := ((ZMod.finEquiv (m + 1) : Fin (m + 1) ≃ ZMod (m + 1)))
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

set_option linter.flexible false in
theorem twoPoint_fubini_fin (Ts : TransferSystem S) (a b : ℕ) (A B : S → ℝ)
    (hAB : Integrable (twoPointSplitDensity Ts.k a b A B)
      (Ts.ν.prod (Ts.ν.prod
        ((Measure.pi (fun _ : Fin a => Ts.ν)).prod (Measure.pi (fun _ : Fin b => Ts.ν))))))
    (hSlice : ∀ x : S, Integrable (fun p : S × ((Fin a → S) × (Fin b → S)) =>
        twoPointSplitDensity Ts.k a b A B (x, p))
      (Ts.ν.prod ((Measure.pi (fun _ : Fin a => Ts.ν)).prod
        (Measure.pi (fun _ : Fin b => Ts.ν))))) :
    (∫ ψ : Fin ((a + 1) + (b + 1)) → S,
        (∏ i : Fin ((a + 1) + (b + 1)), Ts.k (ψ i) (ψ (i + 1))) *
          (A (ψ 0) * B (ψ (Fin.natAdd (a + 1) (0 : Fin (b + 1)))))
        ∂Measure.pi (fun _ : Fin ((a + 1) + (b + 1)) => Ts.ν)) =
      ∫ x, ∫ y, A x * Ts.kPow a x y * (B y * Ts.kPow b y x) ∂Ts.ν ∂Ts.ν := by
  letI := Ts.ν_sigmaFinite
  let μq : Measure (Fin a → S) := Measure.pi (fun _ : Fin a => Ts.ν)
  let μr : Measure (Fin b → S) := Measure.pi (fun _ : Fin b => Ts.ν)
  let eRest : Fin (a + (b + 1)) ≃ Fin ((a + 1) + b) := finCongr (by omega)
  let eRestMeas := MeasurableEquiv.piCongrLeft (fun _ : Fin ((a + 1) + b) => S) eRest
  let iY : Fin (a + (b + 1)) := Fin.natAdd a (0 : Fin (b + 1))
  let eY := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (a + (b + 1)) => S) iY).symm
  let eQR := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => S)).symm
  let eSum := MeasurableEquiv.piCongrLeft (fun _ : Fin (a + b) => S) finSumFinEquiv
  let eRestSplit := eQR.trans eSum
  let eYNorm := (MeasurableEquiv.prodCongr (MeasurableEquiv.refl S) eRestSplit).trans eY
  let eYRest := eYNorm.trans eRestMeas
  let eAfterFirst := MeasurableEquiv.prodCongr (MeasurableEquiv.refl S) eYRest
  have hRestLen : MeasurePreserving eRestMeas
      (Measure.pi (fun _ : Fin (a + (b + 1)) => Ts.ν))
      (Measure.pi (fun _ : Fin ((a + 1) + b) => Ts.ν)) :=
    measurePreserving_piCongrLeft (fun _ : Fin ((a + 1) + b) => Ts.ν) eRest
  have hY : MeasurePreserving eY
      (Ts.ν.prod (Measure.pi (fun _ : Fin (a + b) => Ts.ν)))
      (Measure.pi (fun _ : Fin (a + (b + 1)) => Ts.ν)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (a + (b + 1)) => Ts.ν) iY).symm
  have hQR : MeasurePreserving eQR (μq.prod μr)
      (Measure.pi (fun _ : Fin a ⊕ Fin b => Ts.ν)) :=
    (measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => Ts.ν)).symm
  have hSum : MeasurePreserving eSum
      (Measure.pi (fun _ : Fin a ⊕ Fin b => Ts.ν))
      (Measure.pi (fun _ : Fin (a + b) => Ts.ν)) :=
    measurePreserving_piCongrLeft (fun _ : Fin (a + b) => Ts.ν) finSumFinEquiv
  have hRestSplit : MeasurePreserving eRestSplit (μq.prod μr)
      (Measure.pi (fun _ : Fin (a + b) => Ts.ν)) :=
    hSum.comp hQR
  have hYNorm : MeasurePreserving eYNorm
      (Ts.ν.prod (μq.prod μr))
      (Measure.pi (fun _ : Fin (a + (b + 1)) => Ts.ν)) :=
    hY.comp (MeasurePreserving.prod (MeasurePreserving.id Ts.ν) hRestSplit)
  have hYRest : MeasurePreserving eYRest
      (Ts.ν.prod (μq.prod μr))
      (Measure.pi (fun _ : Fin ((a + 1) + b) => Ts.ν)) :=
    hRestLen.comp hYNorm
  have hAfterFirst : MeasurePreserving eAfterFirst
      (Ts.ν.prod (Ts.ν.prod (μq.prod μr)))
      (Ts.ν.prod (Measure.pi (fun _ : Fin ((a + 1) + b) => Ts.ν))) :=
    MeasurePreserving.prod (MeasurePreserving.id Ts.ν) hYRest
  change (∫ ψ : Fin (((a + 1) + b) + 1) → S,
      (∏ i : Fin (((a + 1) + b) + 1), Ts.k (ψ i) (ψ (i + 1))) *
        (A (ψ 0) * B (ψ (Fin.natAdd (a + 1) (0 : Fin (b + 1)))))
      ∂Measure.pi (fun _ : Fin (((a + 1) + b) + 1) => Ts.ν)) =
    ∫ x, ∫ y, A x * Ts.kPow a x y * (B y * Ts.kPow b y x) ∂Ts.ν ∂Ts.ν
  rw [← ((measurePreserving_piFinSuccAbove
    (fun _ : Fin (((a + 1) + b) + 1) => Ts.ν) 0).symm).integral_comp']
  rw [← hAfterFirst.integral_comp']
  simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  simp_rw [Fin.insertNthEquiv_zero]
  simp only [Fin.consEquiv_apply]
  simp [eAfterFirst, eYRest, eYNorm, eY, eRestMeas, eRestSplit, eQR, eSum, eRest, iY,
    MeasurableEquiv.coe_piCongrLeft, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
    Fin.insertNthEquiv, Equiv.prodCongr, MeasurableEquiv.prodCongr]
  simp_rw [piCongrLeft_finSumFinEquiv_sumPi_symm_eq_append a b]
  simp_rw [insertNth_natAdd_zero_append_eq_append_cons a b]
  simp_rw [cons_piCongrLeft_finCongr_append_cons_eq_append_cons a b]
  simp_rw [cyclicProduct_append_cons_eq_openChainProducts_assoc Ts.k a b]
  simp only [Fin.append_right, Fin.cons_zero]
  ring_nf
  change (∫ p : S × (S × ((Fin a → S) × (Fin b → S))),
      twoPointSplitDensity Ts.k a b A B p
      ∂Ts.ν.prod (Ts.ν.prod (μq.prod μr))) =
    ∫ x, ∫ y, A x * Ts.kPow a x y * B y * Ts.kPow b y x ∂Ts.ν ∂Ts.ν
  rw [integral_prod _ hAB]
  simp only [twoPointSplitDensity]
  have hinner (x : S) :
      (∫ y : S × ((Fin a → S) × (Fin b → S)),
          openChainProduct Ts.k a x y.1 y.2.1 *
              openChainProduct Ts.k b y.1 x y.2.2 * A x * B y.1
          ∂Ts.ν.prod ((Measure.pi (fun _ : Fin a => Ts.ν)).prod
            (Measure.pi (fun _ : Fin b => Ts.ν)))) =
        ∫ y, ∫ qr : (Fin a → S) × (Fin b → S),
          openChainProduct Ts.k a x y qr.1 *
              openChainProduct Ts.k b y x qr.2 * A x * B y
          ∂μq.prod μr ∂Ts.ν := by
    exact integral_prod _ (by
      simpa [twoPointSplitDensity, μq, μr] using hSlice x)
  simp_rw [hinner]
  have hqr (x y : S) :
      (∫ qr : (Fin a → S) × (Fin b → S),
          openChainProduct Ts.k a x y qr.1 *
              openChainProduct Ts.k b y x qr.2 * A x * B y
          ∂μq.prod μr) =
        A x * Ts.kPow a x y * B y * Ts.kPow b y x := by
    calc
      (∫ qr : (Fin a → S) × (Fin b → S),
          openChainProduct Ts.k a x y qr.1 *
              openChainProduct Ts.k b y x qr.2 * A x * B y
          ∂μq.prod μr)
          = ∫ qr : (Fin a → S) × (Fin b → S),
              (openChainProduct Ts.k a x y qr.1 * A x) *
                (openChainProduct Ts.k b y x qr.2 * B y) ∂μq.prod μr := by
              congr 1
              ext qr
              ring
      _ = (∫ q, openChainProduct Ts.k a x y q * A x ∂μq) *
            ∫ r, openChainProduct Ts.k b y x r * B y ∂μr := by
              exact integral_prod_mul
                (μ := μq) (ν := μr)
                (fun q => openChainProduct Ts.k a x y q * A x)
                (fun r => openChainProduct Ts.k b y x r * B y)
      _ = A x * Ts.kPow a x y * B y * Ts.kPow b y x := by
              rw [integral_mul_const, integral_mul_const]
              simp_rw [openChainProduct_eq_density]
              rw [show (∫ q : Fin a → S, openChainDensity Ts.k a x y q ∂μq) =
                  Ts.kPow a x y by
                simpa [μq] using openChain_fold Ts a x y]
              rw [show (∫ r : Fin b → S, openChainDensity Ts.k b y x r ∂μr) =
                  Ts.kPow b y x by
                simpa [μr] using openChain_fold Ts b y x]
              ring
  simp_rw [hqr]

theorem twoPoint_fubini (Ts : TransferSystem S) (n : ℕ) [NeZero n] {t : ℕ}
    (ht0 : 0 < t) (htn : t < n) (A B : S → ℝ)
    (hAB : Integrable (twoPointSplitDensity Ts.k (t - 1) (n - t - 1) A B)
      (Ts.ν.prod (Ts.ν.prod
        ((Measure.pi (fun _ : Fin (t - 1) => Ts.ν)).prod
          (Measure.pi (fun _ : Fin (n - t - 1) => Ts.ν))))))
    (hSlice : ∀ x : S, Integrable
        (fun p : S × ((Fin (t - 1) → S) × (Fin (n - t - 1) → S)) =>
          twoPointSplitDensity Ts.k (t - 1) (n - t - 1) A B (x, p))
      (Ts.ν.prod ((Measure.pi (fun _ : Fin (t - 1) => Ts.ν)).prod
        (Measure.pi (fun _ : Fin (n - t - 1) => Ts.ν))))) :
    ∫ ψ, periodicPathDensity Ts.k n ψ * (A (ψ 0) * B (ψ (t : ZMod n)))
        ∂(Measure.pi fun _ : ZMod n => Ts.ν)
      = ∫ x, ∫ y, A x * Ts.kPow (t - 1) x y *
          (B y * Ts.kPow (n - t - 1) y x) ∂Ts.ν ∂Ts.ν := by
  letI := Ts.ν_sigmaFinite
  cases n with
  | zero =>
      cases NeZero.ne 0 rfl
  | succ m =>
  let a := t - 1
  let b := (m + 1) - t - 1
  have hlen : ((a + 1) + (b + 1)) = m + 1 := by
    dsimp [a, b]
    omega
  let eLen : Fin ((a + 1) + (b + 1)) ≃ Fin (m + 1) := finCongr hlen
  let eZ := ((ZMod.finEquiv (m + 1) : Fin (m + 1) ≃ ZMod (m + 1)))
  rw [← (measurePreserving_piCongrLeft (fun _ : ZMod (m + 1) => Ts.ν) eZ).integral_comp']
  dsimp [periodicPathDensity, eZ]
  have hprod (ψ : Fin (m + 1) → S) :
      (∏ z : ZMod (m + 1),
          Ts.k ((MeasurableEquiv.piCongrLeft (fun _ : ZMod (m + 1) => S)
              ((ZMod.finEquiv (m + 1) : Fin (m + 1) ≃ ZMod (m + 1)))) ψ z)
            ((MeasurableEquiv.piCongrLeft (fun _ : ZMod (m + 1) => S)
              ((ZMod.finEquiv (m + 1) : Fin (m + 1) ≃ ZMod (m + 1)))) ψ (z + 1))) =
        ∏ i : Fin (m + 1), Ts.k (ψ i) (ψ (i + 1)) := by
    symm
    refine Fintype.prod_equiv ((ZMod.finEquiv (m + 1) : Fin (m + 1) ≃ ZMod (m + 1)))
      (fun i : Fin (m + 1) => Ts.k (ψ i) (ψ (i + 1)))
      (fun z : ZMod (m + 1) =>
        Ts.k ((MeasurableEquiv.piCongrLeft (fun _ : ZMod (m + 1) => S)
            ((ZMod.finEquiv (m + 1) : Fin (m + 1) ≃ ZMod (m + 1)))) ψ z)
          ((MeasurableEquiv.piCongrLeft (fun _ : ZMod (m + 1) => S)
            ((ZMod.finEquiv (m + 1) : Fin (m + 1) ≃ ZMod (m + 1)))) ψ (z + 1))) ?_
    intro i
    rfl
  have hzero (ψ : Fin (m + 1) → S) :
      ((MeasurableEquiv.piCongrLeft (fun _ : ZMod (m + 1) => S)
          ((ZMod.finEquiv (m + 1) : Fin (m + 1) ≃ ZMod (m + 1)))) ψ 0) = ψ 0 := by
    rfl
  have htcoord (ψ : Fin (m + 1) → S) :
      ((MeasurableEquiv.piCongrLeft (fun _ : ZMod (m + 1) => S)
          ((ZMod.finEquiv (m + 1) : Fin (m + 1) ≃ ZMod (m + 1)))) ψ (t : ZMod (m + 1))) =
        ψ ⟨t, htn⟩ := by
    change ψ (t : ZMod (m + 1)) = ψ ⟨t, htn⟩
    congr
    ext
    exact Nat.mod_eq_of_lt htn
  simp_rw [hprod, hzero, htcoord]
  change (∫ ψ : Fin (m + 1) → S,
      (∏ i : Fin (m + 1), Ts.k (ψ i) (ψ (i + 1))) *
        (A (ψ 0) * B (ψ ⟨t, htn⟩))
      ∂Measure.pi (fun _ : Fin (m + 1) => Ts.ν)) =
    ∫ x, ∫ y, A x * Ts.kPow (t - 1) x y *
      (B y * Ts.kPow ((m + 1) - t - 1) y x) ∂Ts.ν ∂Ts.ν
  rw [← (measurePreserving_piCongrLeft (fun _ : Fin (m + 1) => Ts.ν) eLen).integral_comp']
  dsimp [eLen]
  have hprodLen (ψ : Fin ((a + 1) + (b + 1)) → S) :
      (∏ i : Fin (m + 1),
          Ts.k ((MeasurableEquiv.piCongrLeft (fun _ : Fin (m + 1) => S)
              (finCongr hlen)) ψ i)
            ((MeasurableEquiv.piCongrLeft (fun _ : Fin (m + 1) => S)
              (finCongr hlen)) ψ (i + 1))) =
        ∏ i : Fin ((a + 1) + (b + 1)), Ts.k (ψ i) (ψ (i + 1)) := by
    symm
    refine Fintype.prod_equiv (finCongr hlen)
      (fun i : Fin ((a + 1) + (b + 1)) => Ts.k (ψ i) (ψ (i + 1)))
      (fun i : Fin (m + 1) =>
        Ts.k ((MeasurableEquiv.piCongrLeft (fun _ : Fin (m + 1) => S)
            (finCongr hlen)) ψ i)
          ((MeasurableEquiv.piCongrLeft (fun _ : Fin (m + 1) => S)
            (finCongr hlen)) ψ (i + 1))) ?_
    intro i
    have hsucc : (finCongr hlen) (i + 1) = (finCongr hlen i + 1 : Fin (m + 1)) := by
      ext
      simp [Fin.val_add, hlen]
    change Ts.k (ψ i) (ψ (i + 1)) =
      Ts.k ((MeasurableEquiv.piCongrLeft (fun _ : Fin (m + 1) => S)
          (finCongr hlen)) ψ ((finCongr hlen) i))
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin (m + 1) => S)
          (finCongr hlen)) ψ ((finCongr hlen i) + 1))
    rw [← hsucc]
    rw [MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (m + 1) => S) (finCongr hlen) ψ i]
    rw [MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (m + 1) => S) (finCongr hlen) ψ (i + 1)]
  have hzeroLen (ψ : Fin ((a + 1) + (b + 1)) → S) :
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin (m + 1) => S)
          (finCongr hlen)) ψ 0) = ψ 0 := by
    rw [← show (finCongr hlen) (0 : Fin ((a + 1) + (b + 1))) = (0 : Fin (m + 1)) by
      ext
      simp]
    simpa using
      (@Equiv.piCongrLeft_apply_apply (Fin ((a + 1) + (b + 1))) (Fin (m + 1))
        (fun _ : Fin (m + 1) => S) (finCongr hlen) ψ (0 : Fin ((a + 1) + (b + 1))))
  have htLen (ψ : Fin ((a + 1) + (b + 1)) → S) :
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin (m + 1) => S)
          (finCongr hlen)) ψ ⟨t, htn⟩) =
        ψ (Fin.natAdd (a + 1) (0 : Fin (b + 1))) := by
    rw [← show (finCongr hlen) (Fin.natAdd (a + 1) (0 : Fin (b + 1))) =
        (⟨t, htn⟩ : Fin (m + 1)) by
      ext
      dsimp [a, b]
      omega]
    simpa using
      (@Equiv.piCongrLeft_apply_apply (Fin ((a + 1) + (b + 1))) (Fin (m + 1))
        (fun _ : Fin (m + 1) => S) (finCongr hlen) ψ
        (Fin.natAdd (a + 1) (0 : Fin (b + 1))))
  simp_rw [hprodLen, hzeroLen, htLen]
  change (∫ ψ : Fin ((a + 1) + (b + 1)) → S,
      (∏ i : Fin ((a + 1) + (b + 1)), Ts.k (ψ i) (ψ (i + 1))) *
        (A (ψ 0) * B (ψ (Fin.natAdd (a + 1) (0 : Fin (b + 1)))))
      ∂Measure.pi (fun _ : Fin ((a + 1) + (b + 1)) => Ts.ν)) =
    ∫ x, ∫ y, A x * Ts.kPow a x y * (B y * Ts.kPow b y x) ∂Ts.ν ∂Ts.ν
  exact twoPoint_fubini_fin Ts a b A B hAB hSlice

/-- **The two-point Feynman–Kac dictionary.** For `0 < t < n` and bounded observables
`A B : S → ℝ`, the time-`(0,t)` correlation of the path measure is the kernel-composition
("trace") ratio
`∫ A(ψ₀)·B(ψ_t) dμ_n = Z_n⁻¹ · ∫∫ A(x)·kPow_{t−1}(x,y)·B(y)·kPow_{n−t−1}(y,x) dν dν`,
i.e. `Tr(M_A Tᵗ M_B T^{n−t})/Tr(Tⁿ)`. Proved by integrating out the `n−2` intermediate
slices (iterated Fubini), composing the bonds `0→t` into `T^t`'s kernel and `t→0` (around
the circle) into `T^{n−t}`'s kernel. -/
theorem twoPoint_dictionary (Ts : TransferSystem S) (n : ℕ) [NeZero n]
    {t : ℕ} (ht0 : 0 < t) (htn : t < n) (A B : S → ℝ)
    (hAB : Integrable (twoPointSplitDensity Ts.k (t - 1) (n - t - 1) A B)
      (Ts.ν.prod (Ts.ν.prod
        ((Measure.pi (fun _ : Fin (t - 1) => Ts.ν)).prod
          (Measure.pi (fun _ : Fin (n - t - 1) => Ts.ν))))))
    (hSlice : ∀ x : S, Integrable
        (fun p : S × ((Fin (t - 1) → S) × (Fin (n - t - 1) → S)) =>
          twoPointSplitDensity Ts.k (t - 1) (n - t - 1) A B (x, p))
      (Ts.ν.prod ((Measure.pi (fun _ : Fin (t - 1) => Ts.ν)).prod
        (Measure.pi (fun _ : Fin (n - t - 1) => Ts.ν))))) :
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
        ∫ x, ∫ y, A x * Ts.kPow (t - 1) x y *
          (B y * Ts.kPow (n - t - 1) y x) ∂Ts.ν ∂Ts.ν
    rw [← twoPoint_fubini Ts n ht0 htn A B hAB hSlice]
    congr 1
    rw [ENNReal.toReal_inv]
    rw [ENNReal.toReal_ofReal]
    exact Ts.partition_nonneg n
  · exact Filter.Eventually.of_forall fun ψ => ENNReal.ofReal_lt_top

end TransferSystem

end ReflectionPositivity
