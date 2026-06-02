/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reflection Cauchy-Schwarz and the physical Hilbert space

For any reflection-positive measure, the bilinear form
`⟨F, G⟩_θ := ∫ F · (G ∘ θ) dμ` satisfies the Cauchy-Schwarz inequality

  `|⟨F, G⟩_θ|² ≤ ⟨F, F⟩_θ · ⟨G, G⟩_θ`,

and the quotient of `L²(A₊)` by the kernel of `⟨·, ·⟩_θ` carries a
genuine inner product. Its Hilbert completion is the **physical
Hilbert space** of the OS reconstruction direction.

## Main theorems (planned)

* `MeasureTheory.Measure.IsReflectionPositive.cauchySchwarz` — the
  basic reflection CS inequality.
* `MeasureTheory.Measure.IsReflectionPositive.kernel` — the nullspace
  `{F : ⟨F, F⟩_θ = 0}` is a closed subspace.
* `MeasureTheory.Measure.IsReflectionPositive.physicalHilbertSpace` —
  the quotient `L²(A₊) / kernel` carries a genuine inner product;
  completion is the physical Hilbert space `H_phys`.
* API for the canonical quotient map and how `θ`-compatible bounded
  operators on `L²(A₊)` descend to `H_phys`.

## References

* Osterwalder-Schrader (1973, 1975).
* Glimm-Jaffe Ch. 6 (the construction in the lattice setting).
* Simon, *P(φ)₂*, §III.5 (OS reconstruction).

## Status

**Stub.**
-/

import ReflectionPositivity.Abstract

namespace MeasureTheory.Measure

-- (definitions to be added)

end MeasureTheory.Measure
