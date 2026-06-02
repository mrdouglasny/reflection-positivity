# reflection-positivity — Implementation Plan

*2026-06-02. Initial scoping. Subject to revision as the file structure
firms up against actual Mathlib API.*

**Revised post deep-think vet (2026-06-02)** — gemini caught a
structural bug in the original plan: chessboard estimates are **NOT
needed** for the pphi2 Layer B2 deliverable. The Lt-uniform variance
bound follows directly from the cylinder transfer-matrix mass gap via
an operator-norm geometric-series argument on the orthogonal
complement of the vacuum, with no need for Mathlib's WIP spectral
theorem or chessboard combinatorics. Five recalibrations applied
below:

1. **Split `TransferMatrixGap.lean`** into `TransferMatrix.lean`
   (construction of the transfer matrix on the physical Hilbert
   space) + `VarianceBound.lean` (Layer B2 deliverable, just the
   geometric-series step).
2. **Demote `Chessboard.lean`** to parallel / lower-priority. It is
   still wanted for broader downstream applications (FSS infrared
   bounds, phase transitions) but is **NOT on the critical path** to
   Layer B2.
3. **Use the FILS 1978 abstract operator formulation** for chessboard
   when we get to it — keeps it at the level of unitary involutions
   on Hilbert spaces, divorced from lattice grid geometry. Vastly
   smaller and more Mathlib-upstreamable than the naive
   multinomial-combinatorics-on-the-torus approach.
4. **Keep `Abstract.lean` purely algebraic** as long as possible.
   Avoid topology / completion / quotient-of-topological-vector-space
   friction until `CauchySchwarz.lean`.
5. **Pphi2 RP coexistence** (option b in §"Adoption plan"): the new
   repo coexists with pphi2's existing `OSProofs/OS3_RP_*` infrastructure
   initially. Pphi2 gets an adapter file that maps its existing
   `S_+ + S_- ∘ θ` factorization into the new typeclass; refactoring
   the pphi2 OS3 code is technical-debt cleanup for later.

**Critical-path Phase 1 (revised)**: ~1550-2500 lines, ~3-5 weeks
(was 2100-3200 / 4-7 weeks). The chessboard file is
parallel / deferred.

**Scope extension 2026-06-02**: include the **graph-theoretic
reflection positivity** of Freedman-Lovász-Schrijver
(JAMS 2007) — `M(f, k)` PSD for every `k`, where `M(f, k)` is the
connection matrix of a graph parameter `f` indexed by `k`-labeled
graphs. Same abstract shape as OS RP (PSD form on a semigroup with
involution; GNS-style construction via commutative finite-dim
C*-algebras), different domain. **Parallel deliverable, NOT on
critical path for pphi2.** Added as `Graph/` subdirectory analogous
to `Chessboard/`. See "Graph reflection positivity (FLS)" section
below.

## Goals

Provide the **foundational + chessboard layer** of the
Osterwalder-Schrader reflection-positivity program, sufficient for:

1. **Layer B2 of pphi2's `asymInteracting_expMoment_volume_uniform`
   discharge** — Lt-uniform interacting variance bound on the cylinder,
   via cylinder transfer-matrix mass gap + chessboard. This is the
   primary motivating consumer.
2. A standalone Mathlib-quality RP API, suitable for downstream OS
   reconstruction / phase-transition / cluster-expansion work.

Out of scope for the **initial release**:

* Continuum-limit OS reconstruction (would be Phase 2).
* Specific spin-system applications (Heisenberg, Ising in `d ≥ 3`,
  long-range models — Phase 3+).
* Gauge-theory RP (Wilson, BFM, ... — Phase 3+).
* Stahl's theorem / matrix-analysis applications (separate).

## File structure (revised post-vet)

```
ReflectionPositivity.lean                         -- root, re-exports

ReflectionPositivity/
  Abstract.lean                                   -- IsReflectionPositive predicate, basic algebraic API
  CauchySchwarz.lean                              -- Reflection CS + pre-Hilbert quotient (physical Hilbert space)
  TransferMatrix.lean                             -- transfer-matrix construction on H_phys (self-adjoint, positive, bounded)
  VarianceBound.lean                              -- Layer B2 deliverable: mass-gap ⟹ Lt-uniform variance bound (geometric series)
  LatticeInstance.lean                            -- Concrete RP for ferromagnetic Gibbs measures

ReflectionPositivity/Chessboard/                  -- parallel, lower-priority (NOT on critical path)
  Chessboard.lean                                 -- FILS 1978 abstract operator chessboard estimates

ReflectionPositivity/Graph/                       -- parallel, parallel-priority (NOT on critical path)
  ConnectionMatrix.lean                           -- M(f, k) connection-matrix structure, rank, PSD
  HomomorphismFunction.lean                       -- f = hom(·, H) for weighted graphs H
  FreedmanLovaszSchrijver.lean                    -- main theorem: RP + finite rank growth ⟹ f is a hom function
```

The critical path for pphi2 Layer B2 is the OS continuous track
(everything in `ReflectionPositivity/` directly, outside the
subdirectories). `Chessboard/` and `Graph/` are parallel deliverables
for broader downstream consumers, NOT required for Layer B2.

## Phase 1 — minimum viable foundation (target ~2000-3000 lines)

### `ReflectionPositivity/Abstract.lean` (~300-500 lines)

The core definition and basic algebraic API.

* `MeasureTheory.Measure.IsReflectionPositive μ θ A₊` — for `μ` a
  measure on `(Ω, Σ)`, `θ : Ω → Ω` a measurable involution preserving
  `μ`, and `A₊ : MeasurableSpace Ω` a sub-σ-algebra: the bilinear form
  `(F, G) ↦ ∫ F · (G ∘ θ) dμ` is positive semi-definite on
  bounded `A₊`-measurable functions.
* Equivalent formulations: `∫ F · (F ∘ θ) dμ ≥ 0` for `F ∈ L²(A₊)`;
  the integral defines a positive semi-definite form on `L²(A₊)`.
* `θ` is a measure-preserving involution: closure under composition,
  inversion (= itself).
* Conjugate-pairing API: `⟨F, G⟩_θ := ∫ F · (G ∘ θ) dμ`, basic linearity,
  symmetry (`⟨F, G⟩_θ = ⟨G, F⟩_θ` from `θ ∘ θ = id` + `μ ∘ θ⁻¹ = μ`).

### `ReflectionPositivity/CauchySchwarz.lean` (~400-700 lines)

The reflection Cauchy-Schwarz inequality and pre-Hilbert quotient.

* `MeasureTheory.Measure.IsReflectionPositive.cauchySchwarz` — for
  `μ` RP and `F, G ∈ L²(A₊)`,
  `|⟨F, G⟩_θ|² ≤ ⟨F, F⟩_θ · ⟨G, G⟩_θ`.
* `MeasureTheory.Measure.IsReflectionPositive.kernel` — the nullspace
  `N := {F : ⟨F, F⟩_θ = 0}` is a closed subspace (kernel of the form).
* `MeasureTheory.Measure.IsReflectionPositive.physicalHilbertSpace` —
  the quotient `L²(A₊) / N` carries a genuine inner product
  `⟨F, G⟩_θ`; completion is the **physical Hilbert space** `H_phys`
  (the OS reconstruction object).
* Useful API: the canonical quotient map `q : L²(A₊) → H_phys`; how
  bounded operators on `L²(A₊)` that commute with `θ`-pairing descend
  to `H_phys`.

### `ReflectionPositivity/TransferMatrix.lean` (~300-500 lines)

Construction of the transfer matrix on the physical Hilbert space.
For an RP measure `μ` on `Ω = Ω_S × ℤ` (time-translation invariant),
the pairing `(F, G) ↦ ⟨F · (G ∘ τ ∘ θ)⟩` (where `τ` is one-step time
translation) descends to a bounded self-adjoint positive operator
`T_μ` on `H_phys`.

* `MeasureTheory.Measure.IsReflectionPositive.transferMatrix` — the
  operator construction. Self-adjointness from `θ`-symmetry of the
  pairing; positivity from RP itself; boundedness from the
  reflection Cauchy-Schwarz.
* For the **abstract mass-gap bound** consumed in `VarianceBound.lean`:
  decompose `H_phys = ℂ Ω ⊕ H_perp` (vacuum + orthogonal complement),
  and capture the mass gap as an operator-norm bound
  `‖T_μ|_{H_perp}‖ ≤ e^{-ma}` where `m > 0` is the spectral gap.
* **No Mathlib spectral theorem required** for this critical-path
  shape — gemini-vetted 2026-06-02. We need only the algebraic
  orthogonal decomposition + the operator-norm restriction lemma,
  both of which are in Mathlib's current functional-analysis layer.

### `ReflectionPositivity/VarianceBound.lean` (~150-300 lines) — Layer B2 deliverable

The **pphi2 Layer B2 output**: for any RP measure with positive
mass-gap operator-norm bound (from `TransferMatrix.lean`), the
susceptibility / variance is bounded uniformly in the time-direction
volume.

* `MeasureTheory.Measure.IsReflectionPositive.variance_le_freeVariance_of_massGap` —
  for any RP measure with `‖T_μ|_{H_perp}‖ ≤ e^{-ma}` and any
  `f : Ω → ℝ`,
  `Var_μ(f) ≤ const(m) · Var_free(f)`
  uniformly in lattice volume (specifically, uniform in `L_t` for
  pphi2's cylinder application).

* **Proof** (vetted 2026-06-02 — does NOT require chessboard):
  Express the torus 2-point function as a transfer-matrix trace
  `⟨A T^t A T^{L_t-t}⟩ / ⟨T^{L_t}⟩`. As `L_t → ∞`, `T^{L_t}` projects
  onto the vacuum. The finite-`L_t` trace is bounded using the
  isolated highest eigenvalue (`1` on `Ω`) and the operator-norm
  bound on `H_perp` (`≤ e^{-ma}`). The series `∑_t e^{-mat} < ∞`
  gives the uniform susceptibility.

* **Critical-path-shortest variant**: state the susceptibility bound
  directly in terms of the operator-norm bound, leaving the
  Källén-Lehmann spectral decomposition to a Phase 2 refinement.

### `ReflectionPositivity/LatticeInstance.lean` (~400-500 lines)

Concrete RP instance for product lattice measures with an even
nearest-neighbour interaction.

* `MeasureTheory.Measure.isReflectionPositive_of_evenNearestNeighbour` —
  for any finite lattice `Λ` with a reflection symmetry `θ`, the
  ferromagnetic Gibbs measure
  `μ ∝ exp(-½ ∑_{x,y} J_{xy} φ_x φ_y - ∑_x V(φ_x)) ∏ dφ_x` with
  `J_{xy} ≥ 0` even and `V` arbitrary single-site is RP for the
  half-space sub-σ-algebra. (Glimm-Jaffe Ch. 6 Thm 6.2.2.)
* Specialization to: cylinder `Z_{Nt} × Z_{Ns}` (the asym lattice for
  pphi2's cylinder construction), with `θ` = time reflection.
* RP closed under weak limits — this generalizes pphi2's existing
  `rp_closed_under_weak_limit` (`OSProofs/OS3_RP_Inheritance.lean`).

### `ReflectionPositivity/TransferMatrixGap.lean` (~400-500 lines)

The **Layer B2 deliverable**: for an RP measure with a positive
transfer-matrix mass gap, the susceptibility / variance is bounded.

(See `TransferMatrix.lean` and `VarianceBound.lean` files above — the
old `TransferMatrixGap.lean` was split into these two per the
2026-06-02 deep-think vet.)

## Graph reflection positivity (FLS, parallel deliverable)

The Freedman-Lovász-Schrijver framework (JAMS 20, 2007) gives a
graph-theoretic analogue of RP that fits the same abstract template
(PSD form on a semigroup with involution) but operates on graph
parameters rather than measure-theoretic observables. **NOT on the
critical path for pphi2**; included here for repo breadth and
Mathlib-upstream value.

### `ReflectionPositivity/Graph/ConnectionMatrix.lean` (~300-500 lines)

The connection-matrix structure on graph parameters.

* `Graph.connectionMatrix f k` — for a graph parameter `f` and
  `k ≥ 0`, the (infinite) matrix `M(f, k)` with rows/columns indexed
  by isomorphism classes of `k`-labeled graphs, entry at `(G₁, G₂)`
  given by `f(G₁ G₂)` (where `G₁ G₂` is the product: glue along
  labels).
* `Graph.IsReflectionPositive f` — `M(f, k)` is positive semi-definite
  for every `k`.
* `Graph.rankConnectivity f k` — `r(f, k) := rk M(f, k)`. Bounded growth
  `r(f, k) ≤ q^k` is the rank-connectivity hypothesis of FLS Thm 2.4.

### `ReflectionPositivity/Graph/HomomorphismFunction.lean` (~200-400 lines)

The homomorphism-function class `f_H(G) := hom(G, H)` for `H` a
weighted graph.

* `Graph.homomorphismFunction H` — for `H = (a, B)` (positive node
  weights + symmetric real edge-weight matrix), the function
  `f_H(G) := ∑_φ ∏_u α_H(φ u) ∏_{uv ∈ E(G)} β_H(φu, φv)`.
* `Graph.homomorphismFunction.isReflectionPositive` — every `f_H` is
  reflection-positive, with `r(f_H, k) ≤ |V(H)|^k`.

### `ReflectionPositivity/Graph/FreedmanLovaszSchrijver.lean` (~500-800 lines)

The FLS main theorem (converse).

* `Graph.FLS.main` — **the main theorem (Thm 2.4 of FLS 2007)**: a
  reflection-positive multiplicative graph parameter `f` with
  `r(f, k) ≤ q^k` for some `q` is a homomorphism function: there
  exists a weighted graph `H` with `|V(H)| ≤ q` such that `f = f_H`.
* Proof via the commutative finite-dim C*-algebra construction
  (FLS §4): the connection-matrix structure makes the `k`-labeled
  partial graphs into a *-semigroup; PSD-ness lets us complete to a
  Hilbert space; rank bound forces the algebra finite-dim; structure
  theorem for commutative C*-algebras gives the realization `H`.

### Reusability of the abstract layer

`ReflectionPositivity/Abstract.lean` is intentionally **algebraic
only** (per gemini vet) — it can be specialized to both the OS
(measure-theoretic) and FLS (graph-theoretic) settings. The "abstract
RP" notion is: a `*-semigroup S` with a function `f : S → ℝ` such
that the kernel `(s, t) ↦ f(s* · t)` is positive semi-definite. OS RP
specializes to `S = L²(A₊)` and FLS RP specializes to
`S = ℝ[k-labeled graphs]`.

If the shared algebraic layer pays off, a future refactor can move
common content (e.g., the GNS-style quotient construction) into
`Abstract.lean`; for the initial release, OS and Graph live in
parallel without forced sharing.

## Adoption plan (revised post-vet)

Per gemini-2026-06-02 (Q4), **option (b) coexist**, not subsume. Once
Phase 1 lands and the import surface is stable:

1. Bump pphi2 to require `reflection-positivity`. Add a single
   pphi2-side adapter file that maps the existing
   `OSProofs/OS3_RP_Lattice.action_decomposition` (the `S = S_+ + S_- ∘ θ`
   factorization for the asym lattice) into the new `IsReflectionPositive`
   typeclass.
2. Discharge the Layer B2 axiom in pphi2 using
   `variance_le_freeVariance_of_massGap` (from `VarianceBound.lean`) with
   the proved `asymMassGap_pos` (from
   `Pphi2/AsymTorus/AsymPositivity.lean`) as input.
3. **Leave pphi2's existing `OS3_RP_*` and `IRLimit/CylinderOS` code
   in place initially.** Refactoring those into adapter / instance
   layers is technical-debt cleanup for a later session, AFTER Layer
   B2 is fully discharged and tests pass.
4. Open issues / draft adoption for Phi4 / OSforGFF / OSreconstruction
   / combinatorics-of-graph-parameters consumers as their maintainers
   want.

## Phase-1 total scope (revised post-vet 2026-06-02)

**Critical path** (OS continuous track, discharges pphi2 Layer B2):

| File | Lines |
|---|---|
| `Abstract.lean` | 300-500 |
| `CauchySchwarz.lean` | 400-700 |
| `TransferMatrix.lean` | 300-500 |
| `VarianceBound.lean` | 150-300 |
| `LatticeInstance.lean` | 400-500 |
| **Critical-path subtotal** | **~1550-2500** |

**Parallel deliverables** (NOT on Layer B2 critical path):

| File | Lines |
|---|---|
| `Chessboard/Chessboard.lean` (FILS 1978 operator approach) | 800-1500 |
| `Graph/ConnectionMatrix.lean` | 300-500 |
| `Graph/HomomorphismFunction.lean` | 200-400 |
| `Graph/FreedmanLovaszSchrijver.lean` | 500-800 |
| **Parallel subtotal** | **~1800-3200** |

**Full Phase 1 if all parallel deliverables included**:
~3350-5700 lines, ~6-12 weeks.
**Layer B2 critical path only**: ~1550-2500 lines, ~3-5 weeks.

Wall-clock estimate per the project's calibrated formalization
heuristic. Deeper than lee-yang Phase 1 because the transfer-matrix
construction interacts with Mathlib's WIP
spectral theorem.

## Risks / unknowns

* **Mathlib coverage check**: does Mathlib have any reflection-
  positivity content? Existing pphi2 / gaussian-field / OSreconstruction
  have RP fragments but no unified abstract treatment. Best guess: no
  pre-existing Mathlib API; we build everything from
  `MeasureTheory.Integral` and `MeasureTheory.Measure`.
* **Pre-Hilbert quotient infrastructure**: Mathlib has `Submodule` and
  `Quotient`, but the specific "quotient by kernel of a positive
  semi-definite bilinear form yields a genuine Hilbert space"
  construction may need bespoke setup. Worth a recon pass before
  `CauchySchwarz.lean`.
* **Chessboard combinatorics**: the iterated-reflection bookkeeping
  in `Chessboard.lean` is notoriously fiddly in informal math (every
  textbook treats it with hand-waving). Formalization will require
  careful definitions of "disjoint reflected regions" on a lattice.
  Expect this to dominate `Chessboard.lean`'s line count.
* **Transfer matrix construction and Mathlib spectral theorem state**:
  the abstract `transferMatrix` operator construction needs the
  bounded self-adjoint spectral theorem. Lean's spectral theorem is WIP
  (gemini flagged this in the 2026-05-31 vet); the Layer B2 deliverable
  may need a Fourier-route / explicit-modes shortcut for finite
  lattices (analogous to pphi2's plan in `AsymKallenLehmann.lean`,
  which became `AsymVarianceBound.lean` because the existing density-
  transfer route was found to suffice for Layer B1). For Layer B2
  (uniformity), the abstract spectral-theorem route may not have a
  similar shortcut.
* **Integration with pphi2's existing OS3 work**: pphi2 has
  `OSProofs/OS3_RP_Lattice.lean` (`action_decomposition`) and
  `OS3_RP_Inheritance.lean` (`rp_closed_under_weak_limit`) already
  proved. The new abstract framework must subsume these without
  invalidating downstream pphi2 consumers — or pphi2's existing files
  become adapter / instance layers on top of the new abstract one.

## Initial milestone (if approved)

1. Verify Mathlib coverage of reflection / involution / measure-
   preserving setups — issue a recon report.
2. Run `lake update` to fetch Mathlib and confirm the toolchain builds.
3. Stub `Abstract.lean` with the `IsReflectionPositive` definition
   + basic API only; verify it type-checks.
4. Fill in the reflection Cauchy-Schwarz in `CauchySchwarz.lean` as a
   smoke-test of the framework (it's the simplest nontrivial
   consequence of the definition).
5. Decision point: continue, adjust scope, or rethink.
