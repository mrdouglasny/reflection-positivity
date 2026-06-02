/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reflection-positive measures: definition and basic API

The abstract setup: a measure `μ` on `(Ω, Σ)` with a measurable
involution `θ : Ω → Ω` preserving `μ`, and a sub-σ-algebra `A₊ ⊂ Σ`
("positive-time" observables). The reflection bilinear form is

  `⟨F, G⟩_θ := ∫ F · (G ∘ θ) dμ`,

and `μ` is **reflection-positive** when this form is positive
semi-definite on bounded `A₊`-measurable functions.

## Main definitions (planned)

* `MeasureTheory.Measure.reflectionInnerProduct μ θ F G` — the
  bilinear form `∫ F · (G ∘ θ) dμ`.
* `MeasureTheory.Measure.IsReflectionPositive μ θ A₊` — the form
  is positive semi-definite on `L²(A₊)`-measurable functions.

## Main theorems (planned)

* Symmetry of the form: `⟨F, G⟩_θ = ⟨G, F⟩_θ` (uses `θ ∘ θ = id` +
  `μ ∘ θ⁻¹ = μ`).
* Bilinearity in each argument (standard).
* Basic algebraic API for the predicate.

## References

* Glimm-Jaffe Ch. 6 §6.2 (lattice transfer matrix and RP).
* Osterwalder-Schrader (1973, 1975) — OS3 axiom.
* Simon, *P(φ)₂*, §III.

## Status

**Stub.**
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace MeasureTheory.Measure

-- (definitions to be added)

end MeasureTheory.Measure
