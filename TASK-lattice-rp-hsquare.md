# TASK: close `h_square` — finish `isReflectionPositive_of_evenNearestNeighbour`

Repo: this one. File: `ReflectionPositivity/LatticeInstance.lean` (already has the HS core +
`isReflectionPositive_of_evenNearestNeighbour` proved MODULO the `h_square` hypothesis — read the
file + `docs/lattice-rp-design.md` §VET OUTCOME). GOAL: prove `h_square` for the concrete data,
turning `isReflectionPositive_of_evenNearestNeighbour` into an UNCONDITIONAL theorem (drop the
`h_square` arg). This is the measure-theoretic assembly the previous pass flagged as the blocker;
it is the bulk of the real GJ 6.2.2 proof. Elementary in math, fiddly in `Measure.pi` API.

## What must be shown

For `d : EvenFerroReflectionData ι` and `F : EvenConfig ι → ℝ` with `Measurable[d.mPos] F` and
`Integrable (fun φ => F φ * F (d.θ φ)) d.μ`:
  `reflectionInnerProduct d.μ d.θ F F = ∫ z : ι → ℝ, (I z) ^ 2 ∂(stdGaussianPi ι)`
for a suitable `I : (ι → ℝ) → ℝ`. Recall (defs in file):
- `EvenConfig ι = Sum ι ι → ℝ`; `positivePart φ = φ ∘ inl`, `negativePart φ = φ ∘ inr`;
  `evenTheta φ = φ ∘ Equiv.sumComm` (swaps blocks), so `positivePart (θ φ) = negativePart φ`.
- `d.μ = d.baseMeasure.withDensity (ENNReal.ofReal ∘ d.density)`,
  `d.baseMeasure = Measure.pi (fun _ : Sum ι ι => volume)`, `d.density ≥ 0` (it's `Real.exp _`).
- `density_hs_factor`: `d.density φ = ∫ z, posPartIntegrand (positivePart φ) z * posPartIntegrand (negativePart φ) z ∂(stdGaussianPi ι)`.

## Proof route (pinned; the three fiddly steps + the Mathlib API to try)

1. **Unfold reflectionInnerProduct + withDensity:**
   `reflectionInnerProduct d.μ d.θ F F = ∫ φ, F φ * F (θ φ) ∂d.μ`
   `= ∫ φ, F φ * F (θ φ) * d.density φ ∂d.baseMeasure`  (via
   `MeasureTheory.integral_withDensity_eq_integral_smul`/`integral_withDensity_eq_integral_mul` —
   density is `ENNReal.ofReal (d.density φ)` with `d.density ≥ 0`; use `Real.coe_toNNReal` /
   `ENNReal.toReal_ofReal`. Handle the `smul`/`mul` real-valued form.)

2. **Block split of `baseMeasure` (the fiddliest — Doob-Dynkin + Measure.pi over a sum):**
   Use the measurable equiv `e : (Sum ι ι → ℝ) ≃ᵐ ((ι → ℝ) × (ι → ℝ))`,
   `e φ = (positivePart φ, negativePart φ)` — build from `MeasurableEquiv.piSumEquivProd`-style
   API, i.e. `MeasurableEquiv.piSum`/`MeasurableEquiv.sumPiEquivProdPi` or
   `(MeasurableEquiv.piCongrLeft ...).trans (MeasurableEquiv.sumPiEquivProdPi ...)`; grep Mathlib
   for `sumPiEquivProdPi` / `piSum`. It should be measure-preserving from
   `Measure.pi (Sum ι ι)` to `Measure.pi ι ×ₘ Measure.pi ι` (Mathlib:
   `MeasureTheory.measurePreserving_piSum` / `Measure.pi_map_piSumEquiv` or similar — find it).
   Push the integral through `e` (`MeasurePreserving.integral_comp` / `integral_map`), turning
   `∫ φ … ∂(pi Sum)` into `∫ (a,b), … ∂(pi ι ×ₘ pi ι)`. Under `e`: `positivePart φ ↦ a`,
   `negativePart φ ↦ b`, and `θ` ↦ `Prod.swap` (so `F (θ φ) ↦ (F ∘ e.symm) (b, a)`).
   **Doob-Dynkin:** `Measurable[d.mPos] F` with `d.mPos = comap positivePart _` gives
   `∃ G : (ι → ℝ) → ℝ, Measurable G ∧ F = G ∘ positivePart` — Mathlib
   `MeasurableSpace.measurable_comap`-family / `Measurable.factorsThrough` /
   `comap_measurable`; if the exact Doob-Dynkin lemma is hard to locate, an acceptable alternative
   is to ADD `(G : (ι → ℝ) → ℝ) (hG : Measurable G) (hFG : F = G ∘ positivePart)` to the theorem's
   hypotheses (the pphi2 adapter supplies `G` directly, since its observables are built on the
   positive half) — REPORT if you take this route. Then `F φ = G a`, `F (θ φ) = G b`.

3. **Fubini + square:** the integrand is `G a * G b * (∫ z, posInt(a,z) posInt(b,z) dg)`. Pull the
   `∫ z` out (`integral_const_mul` / `MeasureTheory.integral_integral_swap` — Fubini/Tonelli;
   integrability from the hypotheses — you may need to ADD the integrability side-conditions the
   swap requires as theorem hyps; state them minimally and REPORT). Get
   `∫ z, (∫ a, G a posInt(a,z) d(pi ι)) * (∫ b, G b posInt(b,z) d(pi ι)) dg`. The two inner
   integrals are the SAME (rename `b→a`, same `G`, same `posInt`), `=: I z`. So the integrand is
   `(I z)^2 = (I z)*(I z)`. Conclude with `I := fun z => ∫ a, G a * d.posPartIntegrand a z ∂(Measure.pi (fun _:ι => volume))`.

Then `isReflectionPositive_of_evenNearestNeighbour` becomes unconditional (remove `h_square`;
its consumers use `∫ (I z)^2 ≥ 0` via `integral_nonneg`+`sq_nonneg`, already in the file).

## Constraints
NO axioms, NO sorries in committed code. It is ACCEPTABLE to add explicit hypotheses to
`isReflectionPositive_of_evenNearestNeighbour` for (i) the Doob-Dynkin `G` factorization and
(ii) the Fubini integrability side-conditions, IF the fully-general versions are hard to source —
but MINIMIZE them and REPORT exactly what you added (these become the pphi2 adapter's obligations).
`#print axioms` on the final theorem (bare trio). `lake build` green. If a specific `Measure.pi`
sum-split lemma is genuinely absent from this Mathlib and can't be built in ~1h, STOP and report
the exact missing lemma + goal state. Commit "LatticeInstance: close h_square — unconditional (or
adapter-hypothesis) even-ferromagnetic lattice RP" and push. Report: unconditional vs which added
hyps, footprint, any blocker.
