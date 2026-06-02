/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Variance bound from transfer-matrix mass gap — Layer B2 deliverable

For an RP measure with a positive transfer-matrix mass-gap operator-
norm bound (from `TransferMatrix.lean`), the susceptibility / variance
is bounded uniformly in the time-direction lattice volume.

**This is the pphi2 Layer B2 deliverable.**

## The geometric-series argument (deep-think-vetted 2026-06-02)

The torus 2-point function is, schematically,
`S_2(t₁, t₂) = ⟨A T^t A T^{L_t - t}⟩ / ⟨T^{L_t}⟩`. As `L_t → ∞`,
`T^{L_t}` strongly projects onto the vacuum. The finite-`L_t` trace
is bounded using:

* The isolated highest eigenvalue (`1` on `Ω`).
* The operator-norm bound `‖T|_{H_perp}‖ ≤ e^{-ma}` from
  `TransferMatrix.lean`.

The series `∑_t e^{-m·a·t} = 1/(1 - e^{-ma}) < ∞` gives a uniform
susceptibility bound, independent of `L_t`. This avoids the bounded
self-adjoint spectral theorem (Mathlib WIP) and the chessboard
combinatorics — neither is required for Lt-uniformity at fixed `Ls`.

## Main theorems (planned)

* `MeasureTheory.Measure.IsReflectionPositive.variance_le_freeVariance_of_massGap`
  — **the Layer B2 deliverable**: for any RP measure with a
  `MassGapBound m a` (from `TransferMatrix.lean`) and any test
  function `f`,
  `Var_μ(f) ≤ const(m, a) · Var_free(f)`,
  uniformly in the time-direction volume `L_t`.
* `MeasureTheory.Measure.IsReflectionPositive.susceptibility_le_geometric`
  — the explicit susceptibility bound
  `const(m, a) = 1/(1 - e^{-m·a})` (up to schematic constants).

## Pphi2 adapter (in pphi2, not here)

`Pphi2/AsymTorus/AsymExpMomentDischarge.lean` defines an axiom
`asymInteractingVariance_le_freeVariance_Lt_uniform` that this file
will discharge once Phase 1 lands. The pphi2-side adapter
(~100-200 lines):

1. Instantiate `LatticeInstance.isReflectionPositive_of_evenNearestNeighbour`
   with the asym lattice's ferromagnetic structure.
2. Construct the `MassGapBound` (from `TransferMatrix.lean`) using
   pphi2's already-proved `asymMassGap_pos` (from
   `Pphi2/AsymTorus/AsymPositivity.lean`).
3. Apply `variance_le_freeVariance_of_massGap` to discharge the
   Layer B2 axiom.

## References

* Glimm-Jaffe Ch. 19 §3 (mass gap to susceptibility, where they use
  chessboard + spectral theorem; we use the geometric-series shortcut).
* Reed-Simon Vol. IV §XIII.12 (Schrödinger operators, mass gap →
  exponential decay).

## Status

**Stub.**
-/

import ReflectionPositivity.TransferMatrix

namespace MeasureTheory.Measure

-- (definitions to be added)

end MeasureTheory.Measure
