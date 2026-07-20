# TASK: `isReflectionPositive_of_evenNearestNeighbour` (GJ 6.2.2) — implement `LatticeInstance.lean`

Repo: this one (`reflection-positivity`), Lean 4 + Mathlib. Design + full proof skeleton (READ
FIRST): `docs/lattice-rp-design.md` (Gemini-vetted, Route A, axiom-free via Hubbard–Stratonovich).
File: `ReflectionPositivity/LatticeInstance.lean` (currently a stub). Consumes
`ReflectionPositivity/Abstract.lean` (`IsReflectionPositive`, `reflectionInnerProduct`).
Build: `lake build`; iterate `lake env lean ReflectionPositivity/LatticeInstance.lean`.

## Clean formulation (no plane sites — `Nt` even ⟹ reflection has NO fixed sites)

Work with a **two-block** decomposition (this is simpler than the design doc's plane-integration
sketch, which is for the reflect-through-sites case; we do reflect-through-bonds):

- Index by `ι` (`[Fintype ι] [DecidableEq ι]`) = the **positive-half sites**. The full lattice is
  `Λ := ι ⊕ ι` (`Sum ι ι`), with `inl` = positive half `Λ₊`, `inr` = negative half `Λ₋`.
- Reflection `r : Λ ≃ Λ := Equiv.sumComm ι ι` (swaps the two blocks), involutive, no fixed points.
- Configs `Ω := Λ → ℝ` with `MeasurableSpace` = `MeasurableSpace.pi`; `θ : Ω → Ω := (· ∘ r)`.
- Base measure `μ₀ := Measure.pi (fun _ : Λ => (volume : Measure ℝ))`.
- Data: within-block symmetric potentials/couplings encoded so the density factors as below;
  concretely take as INPUT a function `E₊ : (ι → ℝ) → ℝ` (the "half action": within-Λ₊ kinetic
  bonds + `Σ_{x} V(φ_x)` + the crossing self-terms `½ Σ_e J_e φ_{x_e}²`) and a finite family of
  **crossing edges** `edges : Finset ι` with couplings `J : ι → ℝ`, `hJ : ∀ i, 0 ≤ J i`, so that
  the density is
    `ρ(φ) := exp(-E₊(φ ∘ inl) - E₊(φ ∘ inr) + ∑_{i ∈ edges} J i * (φ (inl i)) * (φ (inr i)))`.
  (The `E₊(φ∘inl) + E₊(φ∘inr)` form BAKES IN both the θ-invariance of the within-block action and
  the potential's no-parity split — deliverable "action_split" reduces to this shape and is by
  construction; the crossing edges couple `inl i` to `inr i = r (inl i)`.)
  `μ := μ₀.withDensity (fun φ => ENNReal.ofReal (ρ φ))` (assume the normalization/finiteness
  hypotheses needed for integrability — carry `E₊` bounded-below + the needed `Integrable`
  hypotheses as fields/args; do NOT get bogged in proving Z < ∞ from scratch — take it as a hyp).
- `mPos : MeasurableSpace Ω` := `MeasurableSpace.comap (fun φ => φ ∘ inl) inferInstance`
  (the σ-algebra of the positive half).

## Deliverables

1. **Bundle** `EvenFerroReflectionData ι` carrying `E₊`, `edges`, `J`, `hJ`, and the integrability
   hypotheses the proof needs (state them minimally — e.g. that `φ ↦ ρ φ` and the HS-tilted
   integrands are integrable; add hyps as the proof reveals them). Define `μ`, `θ`, `mPos` from it.

2. **`hs_edge`** (the Hubbard–Stratonovich per-edge identity, elementary):
   for `J ≥ 0`, `a b : ℝ`,
   `Real.exp (J * a * b) = ∫ z, Real.exp (Real.sqrt J * z * a) * Real.exp (Real.sqrt J * z * b) ∂(gaussianReal 0 1)`  — CHECK the exact normalization; derive from the 1D Gaussian MGF
   `∫ exp(s z) d N(0,1) = exp(s²/2)` (Mathlib: `ProbabilityTheory.gaussianReal` + its MGF, or
   `integral_gaussian`/`mgf`; find the right lemma) applied to `s = √J (a+b)`, then
   `(a+b)² = a² + b² + 2ab` moves the `a²,b²` — WAIT: to match the target `exp(Jab)` exactly the
   self-terms `exp(½J a²) exp(½J b²)` appear; either (i) put them on the LEFT
   (`exp(½Ja²)exp(½Jb²)exp(Jab) = ∫ exp(√J z a)exp(√J z b) dN`) and cancel them against `E₊`'s
   crossing self-terms, or (ii) absorb differently — pick the formulation that makes deliverable 4
   clean and STATE it precisely. The product over `edges` gives an integral over `ℝ^edges` (use
   `Measure.pi` of `gaussianReal 0 1`, or fold the finite product).

3. **`density_hs_factor`**: rewrite `ρ φ` (times the cancellation self-terms per the choice in 2)
   as `∫ z, (posPart-integrand φ∘inl z) * (posPart-integrand φ∘inr z) d(gaussian^edges)`, where
   `posPart-integrand a z := exp(-E₊(a) + ∑_i √(J i) z_i a_i)`. Pure algebra + `hs_edge` +
   `Finset.prod`/Fubini.

4. **The theorem** `isReflectionPositive_of_evenNearestNeighbour`
   `(d : EvenFerroReflectionData ι) : IsReflectionPositive d.μ d.θ d.mPos`.
   Proof (Route A, per design doc §VET OUTCOME): unfold `IsReflectionPositive`; for `mPos`-meas `F`,
   `F` factors through `φ ∘ inl` so `F φ = F̂ (φ ∘ inl)` and `F (θ φ) = F̂ (φ ∘ inr)` (θ swaps
   blocks; use the `mPos` comap structure — `MeasurableSpace.comap`-measurable ⟹ factors). Then
   `∫ F φ * F (θφ) dμ = ∫ F̂(φ∘inl) F̂(φ∘inr) ρ(φ) dμ₀`; push `μ₀ = pi` as a product over the two
   blocks (`Measure.pi` on `ι ⊕ ι` ≅ product of `pi ι` × `pi ι` — use
   `MeasurableEquiv.sumPiEquivProdPi`/`Measure.pi`-`sumComm` API, find the right one); apply
   deliverable 3 + Fubini to get `∫ z, I(z) * I(z) d(gaussian^edges)` with
   `I(z) := ∫ a, F̂(a) * posPart-integrand a z d(pi ι volume)` (the two block-integrals are EQUAL
   by the `inl`/`inr` symmetry of `ρ` and `θ`); conclude `∫ z, (I z)² ≥ 0` via
   `integral_nonneg` + `sq_nonneg`.

5. **`IsReflectionPositive.weak_limit`** (independent; can be a separate lemma): if `μₙ` are RP for
   `(θ, mPos)` and `μₙ → μ` in the sense that `∫ F·(F∘θ) dμₙ → ∫ F·(F∘θ) dμ` for the relevant `F`
   (state the convergence hypothesis so it matches how pphi2's
   `rp_closed_under_weak_limit` / characteristic-functional convergence is phrased — read that
   pphi2 lemma's statement if accessible, else use bounded-continuous test-function convergence),
   then `μ` is RP. Proof: `le_of_tendsto` on `0 ≤ ∫ F·(F∘θ) dμₙ`.

## Staging & partial-commit (IMPORTANT — this is a large measure-theory build)

Build in order 2 → 1 → 3 → 4, then 5. **Deliverable 2 (`hs_edge`) is the elementary crux — land it
first and solidly.** If the full assembly (4) fights the `Measure.pi` block-splitting API for more
than ~2 hours, **commit everything that compiles** (bundle + `hs_edge` + `density_hs_factor` + any
partial 4/5) with NO sorries in the committed code, and report EXACTLY which step blocked and the
goal state. A partial landing (the HS core + factorization) is valuable. Do NOT introduce axioms or
sorries to force a full landing.

NO axioms, NO sorries in committed code. `#print axioms` on whatever top-level results you land
(expect bare trio). `lake build` green. Commit "LatticeInstance: generic even-ferromagnetic lattice
reflection positivity (GJ 6.2.2) via Hubbard–Stratonovich [+ weak_limit]" (adjust if partial),
push to origin. Report: deliverables landed, footprints, exact blocker if any, and the precise
statement of `isReflectionPositive_of_evenNearestNeighbour` as committed.

---

## OUTCOME (2026-07-20) — GJ 6.2.2 RP PROVED, bare trio (modulo one integrability adapter hyp)

Commits `6e80db8` (HS core + structure) + `19a0fb7` (h_square closed). `#print axioms
isReflectionPositive_of_evenNearestNeighbour = [propext, Classical.choice, Quot.sound]`.

- HS perfect-square core (`hs_edge`, `hs_edges`, `density_hs_factor`): axiom-free (the vet's crux).
- Doob–Dynkin factorization through `positivePart`: proved internally (not a hypothesis).
- `Measure.pi`-over-`Sum` block split: proved via `measurePreserving_sumPiEquivProdPi`.
- `IsReflectionPositive.weak_limit`: landed.
- Remaining hypothesis: **one `hFubini` integrability side-condition** (the HS-square integrand is
  integrable on the product measure) — a genuine side-condition, NOT the RP content. Added
  `measurable_EPos` to the bundle.

**pphi2 adapter (next, lands in pphi2):** instantiate `EvenFerroReflectionData` for
`interactingLatticeMeasureAsym` (ι = spatial×half-time sites, `EPos` = half-action, `edges/J` =
the crossing NN bonds `1/a²`, ferromagnetic ✓), discharge `hFubini` from pphi2's Nelson/exp-moment
integrability, and feed `weak_limit` over the `Lt→∞` pullback to discharge
`CylinderMeasureSequenceEventuallyReflectionPositive` (`hRP` in `cylinderIso_OS_of_RP_OS2`). Bonus:
retires pphi2's `gaussian_rp_cov_perfect_square` axiom.
