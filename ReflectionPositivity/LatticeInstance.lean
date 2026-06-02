/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Concrete RP instances for product lattice measures

Product Gibbs measures with even ferromagnetic nearest-neighbour
interactions are reflection-positive for the half-space sub-σ-algebra
under any lattice reflection that preserves the bond structure.

## Main theorems (planned)

* `MeasureTheory.Measure.isReflectionPositive_of_evenNearestNeighbour` —
  for any finite lattice `Λ` with a measurable reflection `θ : Λ → Λ`
  preserving the edge set, the ferromagnetic Gibbs measure

    `μ ∝ exp(-½ ∑_⟨x,y⟩ J_{x,y} (φ_x - φ_y)² - ∑_x V(φ_x)) ∏_x dφ_x`

  with `J_{x,y} ≥ 0` and `V : ℝ → ℝ` (single-site potential, no parity
  constraint required) is reflection-positive for the half-space
  sub-σ-algebra defined by `θ`. (Glimm-Jaffe Ch. 6 Thm 6.2.2.)

* Specialization to: cylinder `Z_{Nt} × Z_{Ns}` (the asym lattice
  shape for pphi2's cylinder construction), with `θ` = time reflection
  across a time hyperplane and `J_{xy} = 1/a²` for nearest-neighbour
  `⟨xy⟩`. The **`Nt` even** requirement (so the reflection plane sits
  between sites) is reflected here.

* `MeasureTheory.Measure.IsReflectionPositive.weak_limit` — RP is
  closed under characteristic-function-convergent weak limits.
  Generalizes pphi2's existing
  `OSProofs/OS3_RP_Inheritance.rp_closed_under_weak_limit`.

## Interop with pphi2

pphi2 already has the action-decomposition lemma
`OSProofs/OS3_RP_Lattice.action_decomposition` (the `S = S_+ + S_- ∘ θ`
factorization on the asym lattice). After this file lands, the pphi2
RP infrastructure becomes an adapter that proves the asym lattice's
nearest-neighbour interaction satisfies the hypotheses of the
abstract theorem here, and inherits all consequences (CS, chessboard,
transfer-matrix construction) for free.

## References

* Glimm-Jaffe Ch. 6 §6.2 Thm 6.2.2.
* Osterwalder-Seiler (1978) — RP for lattice gauge fields.
* Simon, *P(φ)₂*, §III.

## Status

**Stub.**
-/

import ReflectionPositivity.Abstract

namespace MeasureTheory.Measure

-- (definitions to be added)

end MeasureTheory.Measure
