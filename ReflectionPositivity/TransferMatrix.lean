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

## References

* Glimm-Jaffe Ch. 6 (lattice transfer matrix from RP).
* Reed-Simon Vol. II §X.4 (positive operators).

## Status

**Stub.**
-/

namespace MeasureTheory.Measure

-- (definitions to be added)

end MeasureTheory.Measure
