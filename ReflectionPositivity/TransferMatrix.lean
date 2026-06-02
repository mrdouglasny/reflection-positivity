/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.CauchySchwarz

/-!
# Transfer matrix construction on the physical Hilbert space

For a reflection-positive measure `μ` with a time-translation symmetry
`τ : Ω → Ω` commuting appropriately with the reflection `θ`, the
pairing `(F, G) ↦ ⟨F · (G ∘ τ ∘ θ)⟩` descends to a bounded positive
self-adjoint operator `T_μ` on the physical Hilbert space `H_phys`
(constructed in `CauchySchwarz.lean`).

**The mass-gap operator-norm bound** captured here is the input that
`VarianceBound.lean` consumes to produce the Layer B2 variance bound
for pphi2's discharge. Crucially, this is an **algebraic** statement
(operator norm on the orthogonal complement of the vacuum), NOT a
spectral statement — so we do NOT depend on Mathlib's WIP bounded
self-adjoint spectral theorem.

## Main definitions (planned)

* `MeasureTheory.Measure.IsReflectionPositive.transferMatrix τ` —
  the bounded self-adjoint positive operator `T_μ` on `H_phys`,
  constructed from the time-translation `τ`.
* `MeasureTheory.Measure.IsReflectionPositive.vacuum` — the
  distinguished vacuum vector `Ω` in `H_phys` (image of the constant
  function `1` under the quotient).
* `MeasureTheory.Measure.IsReflectionPositive.vacuumOrthogonal` — the
  orthogonal complement of `ℂ Ω` in `H_phys`.

## Main theorems (planned)

* `MeasureTheory.Measure.IsReflectionPositive.transferMatrix_selfAdjoint`
* `MeasureTheory.Measure.IsReflectionPositive.transferMatrix_positive`
* `MeasureTheory.Measure.IsReflectionPositive.transferMatrix_norm_le_one`
  — `‖T_μ‖ ≤ 1` (the vacuum eigenvalue is the spectral radius).
* `MeasureTheory.Measure.IsReflectionPositive.transferMatrix_vacuum_eq`
  — `T_μ Ω = Ω` (vacuum is invariant).
* `MeasureTheory.Measure.IsReflectionPositive.MassGapBound` — a
  predicate / structure: `‖T_μ|_{H_perp}‖ ≤ exp(-m · a)` for some
  `m > 0` (where `a` is the time-step spacing). This is the
  algebraic shape of "mass gap"; it does NOT require spectral
  resolution of `T_μ`. The concrete instance (cylinder lattice)
  proves this via pphi2's `asymMassGap_pos`.

## Note: no spectral theorem needed for the critical path

The `MassGapBound` predicate captures the mass gap as an operator-norm
restriction on the orthogonal complement of the vacuum — a pure
operator-theoretic statement that requires only the algebraic
orthogonal decomposition `H_phys = ℂ Ω ⊕ H_perp` and the bounded
operator restriction lemma. Both are in Mathlib's current
functional-analysis layer. The "spectral" interpretation
(`λ₁ ≤ e^{-ma}`) is recovered when needed but not required for
`VarianceBound.lean`.

## This file: the abstract operator core

We first develop the **operator-theoretic core** that the Layer B2
variance bound rests on, independent of the measure-theoretic
construction: a `GappedTransfer` — a self-adjoint contraction `T` on a
real inner product space fixing a vacuum vector, with an operator-norm
gap `‖T v‖ ≤ γ ‖v‖` (`γ < 1`) on the orthogonal complement of the
vacuum. From the gap we derive that `T` preserves the vacuum-orthogonal
complement and that `‖T ^ n v‖ ≤ γ ^ n ‖v‖` there — the input
`VarianceBound.lean` turns into a uniform susceptibility bound.

The construction of such a `T` from a reflection-positive measure on
`H_phys` (the analytic RP contraction estimate + extension to the
completion) is the remaining concrete bridge, deferred to a later step.
A pickup-ready, ordered implementation plan (with the self-adjointness
lemma `reflectionInnerProduct_comp_left` already in place, and the one
genuine difficulty — the a-priori contraction bound — isolated as a
hypothesis) is recorded in `RECON.md` → "Deferred implementation plan
(option 3)".

## References

* Glimm-Jaffe Ch. 6 (lattice transfer matrix from RP).
* Reed-Simon Vol. II §X.4 (positive operators).
-/

namespace ReflectionPositivity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- A **gapped transfer operator** on a real inner product space `H`:
a continuous self-adjoint operator `T` fixing a distinguished `vacuum`
vector, together with a spectral-gap bound `‖T v‖ ≤ gap · ‖v‖` with
`gap < 1` on the orthogonal complement of the vacuum.

This is the operator-theoretic packaging of "transfer matrix with a
mass gap": `gap = e^{-m·a}` where `m > 0` is the mass and `a` the time
step. The `norm_le_of_orthogonal` field is the `MassGapBound`. -/
structure GappedTransfer (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- The transfer operator. -/
  T : H →L[ℝ] H
  /-- The vacuum vector (top eigenvector, eigenvalue `1`). -/
  vacuum : H
  /-- `T` is symmetric. -/
  selfAdjoint : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫
  /-- The vacuum is `T`-invariant. -/
  vacuum_eq : T vacuum = vacuum
  /-- The spectral gap parameter `gap = e^{-m·a}`. -/
  gap : ℝ
  /-- The gap is nonnegative. -/
  gap_nonneg : 0 ≤ gap
  /-- The gap is a strict contraction factor. -/
  gap_lt_one : gap < 1
  /-- **Mass-gap bound**: `T` contracts by `gap` on the vacuum-orthogonal
  complement. -/
  norm_le_of_orthogonal : ∀ v, ⟪vacuum, v⟫ = 0 → ‖T v‖ ≤ gap * ‖v‖

namespace GappedTransfer

variable (G : GappedTransfer H)

/-- `T` preserves the orthogonal complement of the vacuum. -/
theorem inner_vacuum_T_eq_zero {v : H} (hv : ⟪G.vacuum, v⟫ = 0) :
    ⟪G.vacuum, G.T v⟫ = 0 := by
  have h := G.selfAdjoint G.vacuum v
  rw [G.vacuum_eq] at h
  rw [← h]; exact hv

/-- Iterates of `T` stay in the vacuum-orthogonal complement. -/
theorem inner_vacuum_T_pow_eq_zero {v : H} (hv : ⟪G.vacuum, v⟫ = 0) (n : ℕ) :
    ⟪G.vacuum, (G.T ^ n) v⟫ = 0 := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ']
    exact G.inner_vacuum_T_eq_zero ih

/-- **Iterated contraction bound**: on the vacuum-orthogonal complement,
`‖T ^ n v‖ ≤ gap ^ n · ‖v‖`. -/
theorem norm_T_pow_le {v : H} (hv : ⟪G.vacuum, v⟫ = 0) (n : ℕ) :
    ‖(G.T ^ n) v‖ ≤ G.gap ^ n * ‖v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    calc ‖G.T ((G.T ^ n) v)‖
        ≤ G.gap * ‖(G.T ^ n) v‖ :=
          G.norm_le_of_orthogonal _ (G.inner_vacuum_T_pow_eq_zero hv n)
      _ ≤ G.gap * (G.gap ^ n * ‖v‖) := by
          exact mul_le_mul_of_nonneg_left ih G.gap_nonneg
      _ = G.gap ^ (n + 1) * ‖v‖ := by rw [pow_succ]; ring

/-- The `n`-step two-point function on the vacuum-orthogonal complement
decays geometrically: `|⟪v, T ^ n v⟫| ≤ gap ^ n · ‖v‖²`. -/
theorem abs_inner_T_pow_le {v : H} (hv : ⟪G.vacuum, v⟫ = 0) (n : ℕ) :
    |⟪v, (G.T ^ n) v⟫| ≤ G.gap ^ n * ‖v‖ ^ 2 := by
  calc |⟪v, (G.T ^ n) v⟫|
      ≤ ‖v‖ * ‖(G.T ^ n) v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (G.gap ^ n * ‖v‖) := by
        exact mul_le_mul_of_nonneg_left (G.norm_T_pow_le hv n) (norm_nonneg _)
    _ = G.gap ^ n * ‖v‖ ^ 2 := by ring

end GappedTransfer

end ReflectionPositivity
