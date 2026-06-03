# The transfer-operator construction (OS reconstruction → Feynman–Kac bridge)

This document explains the construction in
[`ReflectionPositivity/TransferConstruction.lean`](../ReflectionPositivity/TransferConstruction.lean):
how, from a reflection-positive measure with a Euclidean time translation, one builds
the **transfer operator** on the physical Hilbert space and proves the
**Euclidean-correlation ↔ operator-correlation dictionary** (the abstract Feynman–Kac /
Källén–Lehmann identity) and an **`Lt`-uniform variance bound**.

It is the abstract, reusable core behind the "transfer-matrix gap ⟹ variance bound"
deliverable: square torus, asymmetric torus, and the continuum all instantiate the same
construction. For the design rationale (why this abstract route, and the alternatives
ruled out) see [`transfer-bridge-spec.md`](transfer-bridge-spec.md).

## The idea in one line

In the Osterwalder–Schrader / GNS framework the transfer operator is *time translation*
`T : [f] ↦ [f∘τ]` on the physical Hilbert space, and the Euclidean correlation of two
observables separated by `n` time steps **is, essentially by definition**, the physical
inner product `⟪[f], Tⁿ[g]⟫`. So the "Feynman–Kac dictionary" needs no Gaussian
time-slice computation — it falls out of the GNS construction plus the reflection
self-adjointness `θτθ = τ⁻¹` that is already proved in `Abstract.lean`.

## What is built

Starting data: a `ReflectionSystem` (a measure `μ` with reflection `θ`, positive-time
sub-σ-algebra `mPos`, and reflection positivity `rp`), whose physical Hilbert space
`H_phys = Completion PosObs` is constructed in `PhysicalHilbertSpace.lean`.

### D0 — `TimeTranslatedSystem`

Extends `ReflectionSystem` with a **Euclidean time translation** `τ : Ω → Ω`:

| field | meaning |
|---|---|
| `τ` | the time shift (one lattice step in Euclidean time) |
| `τmp` | `τ` preserves `μ` |
| `τθ : ∀ x, τ (θ (τ x)) = θ x` | reflection inverts translation (`θτθ = τ⁻¹`) — gives self-adjointness |
| `τPos` | `τ` preserves positive-time observables (so it acts on the carrier) |
| `contraction` | the a-priori reflection-seminorm bound `‖[f∘τ]‖ ≤ ‖[f]‖`, taken **as a field** (free in any concrete bounded/Gaussian instance — this is the only non-mechanical input, and it is supplied, not derived) |

### D1 — the transfer operator

* `transferOperatorPre : PosObs →L[ℝ] PosObs` — the map `f ↦ f∘τ` on the dense
  pre-Hilbert space; linear (via `Lp.compMeasurePreservingₗ`), and a contraction
  (`‖·‖ ≤ 1`) from the `contraction` field.
* `transferOperator : H_phys →L[ℝ] H_phys` — its continuous-linear extension to the
  completion (`ContinuousLinearMap.completion`), pinned by
  `transferOperator_coe : T (↑f) = ↑(transferOperatorPre f)` on the dense image.
* `transferOperator_selfAdjoint : ⟪T x, y⟫ = ⟪x, T y⟫` — by density (`induction_on₂`)
  from `reflectionInnerProduct_comp_left` (the `θτθ = τ⁻¹` identity).
* `vacuum := [1]` with `transferOperator_vacuum : T vacuum = vacuum` (since `1∘τ = 1`),
  under `[IsProbabilityMeasure μ]`.

These supply **four of the six `GappedTransfer` fields** (`T`, `vacuum`, `selfAdjoint`,
`vacuum_eq`). The remaining `gap` / `norm_le_of_orthogonal` are **not abstract**: a
spectral gap is a property of the concrete operator, supplied at instantiation (e.g. for
a lattice, via Perron–Frobenius on the compact transfer matrix).

### D2 — the bridge: `reflectionCorrelation_eq_inner_T_pow`

```
⟪[f], Tⁿ[g]⟫  =  ∫ f · (g ∘ τ^[n] ∘ θ) dμ        (= reflectionInnerProduct μ θ f (g∘τ^[n]))
```

The physical inner product of transfer-operator powers equals the Euclidean
(reflection) `n`-step correlation of the measure. Proved by a short induction on
`transferOperator_coe`. **This is the abstract Feynman–Kac / Källén–Lehmann dictionary**
— the step that, on a lattice, would otherwise be a Gaussian time-slice factorization.

### D3 — `Lt`-uniform variance bound: `reflectionCorrelation_susceptibility_le`

Given **any** spectral gap on `transferOperator` (a `GappedTransfer G` with
`G.T = transferOperator`) and a vacuum-orthogonal observable `v` (`⟪G.vacuum, [v]⟫ = 0`):

```
∑_{n < N} | ∫ v · (v ∘ τ^[n] ∘ θ) dμ |  ≤  ‖[v]‖² / (1 − gap)
```

uniformly in the truncation `N` — hence uniformly in the time extent. It is D2 composed
with `GappedTransfer.susceptibility_le` (the geometric-series bound in
[`VarianceBound.lean`](../ReflectionPositivity/VarianceBound.lean)).

## How to instantiate (e.g. a lattice φ⁴ cylinder)

1. Build a `TimeTranslatedSystem` for the lattice measure: `rp` from the proved lattice
   reflection positivity, `τ` = the time shift, `contraction` from Gaussian/finite
   boundedness.
2. **Operator-coincidence:** identify `H_phys` / `transferOperator` with the concrete
   spatial `L²` / transfer matrix, and package the proved spectral gap as the
   `GappedTransfer` with `G.T = transferOperator`.
3. Apply D3; identify `‖[v]‖²/(1−gap)` with `const · Var_free` (in QFT applications,
   watching the lattice-spacing normalization).

## Status

Complete: `TransferConstruction.lean` builds sorry/axiom-free; `#print axioms` of
`transferOperator`, `transferOperator_selfAdjoint`, `reflectionCorrelation_eq_inner_T_pow`,
and `reflectionCorrelation_susceptibility_le` is `[propext, Classical.choice, Quot.sound]`
only. The remaining work for any concrete consumer is the instantiation above (the gap and
the operator-coincidence), which lives in the consumer project, not here.

## References

* K. Osterwalder, R. Schrader, *Axioms for Euclidean Green's functions I, II* (1973, 1975).
* J. Glimm, A. Jaffe, *Quantum Physics*, 2nd ed., Ch. 6 (lattice transfer matrix).
* B. Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory* (1974), Ch. III.
