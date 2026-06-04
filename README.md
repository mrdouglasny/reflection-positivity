# reflection-positivity

A Lean 4 / Mathlib formalization of **reflection positivity** (RP) in
its two main guises:

* **Osterwalder-Schrader RP** (OS3) for measure-theoretic / continuous
  settings — the reflection Cauchy-Schwarz inequality, multiple-
  reflection / chessboard estimates (Fröhlich-Israel-Lieb-Simon), the
  pre-Hilbert space construction (the OS reconstruction direction),
  and the **transfer-matrix-gap → variance bound** connection.

* **Freedman-Lovász-Schrijver RP** (JAMS 2007) for discrete / graph-
  theoretic settings — the PSD-ness of connection matrices `M(f, k)`
  of graph parameters, the rank-connectivity hypothesis, and the
  **main theorem**: a multiplicative RP graph parameter with bounded
  rank growth is a homomorphism function `f_H` for some weighted
  graph `H`.

Both share the same abstract template (PSD form on a *-semigroup with
an involution, GNS-style construction); the two specializations are
parallel deliverables in this repo.

Mathlib-only dependencies. Designed to be Mathlib-upstreamable: the
files here are deliberately scoped so each could be lifted into
`Mathlib.MeasureTheory.ReflectionPositivity.*` without refactoring.

## What "reflection positivity" means here

### Two related but distinct programs

| | OS (continuous) | FLS (discrete) |
|---|---|---|
| **Setting** | Measure `μ` on `(Ω, Σ)` with involution `θ` | Graph parameter `f : Graph → ℝ` |
| **Form** | `(F, G) ↦ ∫ F · (G ∘ θ) dμ` | Connection matrix `M(f, k)_{G₁, G₂} = f(G₁ G₂)` |
| **RP condition** | Bilinear form PSD on `L²(A₊)` | `M(f, k)` PSD for every `k` |
| **Reconstruction** | Physical Hilbert space → quantum theory (Wightman) | Weighted graph `H` with `f = hom(·, H)` |
| **Reference** | Osterwalder-Schrader (1973, 1975) | Freedman-Lovász-Schrijver (JAMS 2007) |

### OS reflection positivity (continuous)

Reflection positivity (RP) is the third Osterwalder-Schrader axiom
(OS3) for Euclidean field theories. Abstractly: a measure `μ` on a
measurable space `(Ω, Σ)` with a measurable involution
`θ : Ω → Ω` (the "reflection"), preserving `μ`, satisfies RP with
respect to a sub-σ-algebra `A₊ ⊂ Σ` (the "positive-time" observables)
when

  `∀ F ∈ L²(A₊),  ∫ F · (F ∘ θ) dμ ≥ 0`.

Equivalently: the bilinear form `(F, G) ↦ ∫ F · (G ∘ θ) dμ` is positive
semi-definite on `L²(A₊)`. Taking the quotient by its kernel yields the
**physical Hilbert space**, and the reflection through this construction
is the bridge from a Euclidean theory back to a quantum theory in
Minkowski signature — this is the OS reconstruction direction.

Modern usage of "reflection positivity" covers a richer program:

* **Reflection Cauchy-Schwarz** — for `F, G ∈ L²(A₊)`,
  `|⟨F · θG⟩|² ≤ ⟨F · θF⟩ · ⟨G · θG⟩`. The basic inequality of the
  RP framework.
* **Chessboard estimates** (Fröhlich-Simon-Spencer, 1976) — iterated
  reflections in multiple directions reduce L¹ bounds on products of
  fields at separated sites to single-site / product-state bounds. The
  key tool for proving phase transitions in lattice spin systems
  (Glimm-Jaffe Ch. 10) and for variance / susceptibility bounds in
  constructive QFT (Glimm-Jaffe Ch. 19).
* **Transfer-matrix construction** — RP on a periodic time direction
  gives a self-adjoint (in fact, positive-definite) transfer matrix
  on the physical Hilbert space, with a strictly isolated top
  eigenvalue (Perron-Frobenius). This is the operator-theoretic
  packaging of OS reconstruction in lattice QFT.
* **Transfer-matrix gap ⟹ variance bound** — for any RP measure
  with positive transfer-matrix mass gap, the susceptibility is
  bounded by `1/m²` (in suitable units); for any observable `f`,
  `Var_μ(f) ≤ const · ‖f‖²`. This is **the Layer B2 deliverable**
  for pphi2's `asymInteracting_expMoment_volume_uniform` discharge.

The framework has broader downstream uses, formalized or not:

* OS reconstruction theorem (Euclidean → Wightman), including
  applications in OSforGFF and OSreconstruction projects.
* Phase transitions for lattice spin systems
  (Fröhlich-Simon-Spencer 1976; Glimm-Jaffe Ch. 10).
* Bounded susceptibility / cluster decay for P(φ)₂ / gauge theories
  (Glimm-Jaffe Ch. 19).
* Lieb concavity / log-Sobolev inequalities via Stahl's theorem in
  matrix analysis (modern applications of the multivariate
  Lee-Yang and RP programs).

### The transfer-operator construction (built)

`ReflectionPositivity/TransferConstruction.lean` builds the OS transfer
operator abstractly and proves the Feynman–Kac / Källén–Lehmann
dictionary. The key observation: in the GNS framework the transfer
operator is simply *time translation* `T : [f] ↦ [f∘τ]` on the physical
Hilbert space, and the Euclidean correlation across `n` time steps **is,
by construction**, the operator correlation `⟪[f], Tⁿ[g]⟫` — so no
Gaussian time-slice computation is needed. Four declarations:

* `TimeTranslatedSystem` — a `ReflectionSystem` plus a measure-preserving
  time translation `τ` with `θτθ = τ⁻¹` (and the contraction
  `‖[f∘τ]‖ ≤ ‖[f]‖` as a supplied field — the only non-mechanical input,
  free in any concrete instance).
* `transferOperator : H_phys →L[ℝ] H_phys` — the extension of `f ↦ f∘τ`
  to the completion, with `selfAdjoint` (from `θτθ=τ⁻¹`) and a fixed
  `vacuum = [1]`. (Supplies four of the six `GappedTransfer` fields; the
  spectral `gap` is supplied at instantiation, e.g. via Perron–Frobenius.)
* `reflectionCorrelation_eq_inner_T_pow` (the bridge):
  `⟪[f], Tⁿ[g]⟫ = ∫ f · (g ∘ τ^[n] ∘ θ) dμ`.
* `reflectionCorrelation_susceptibility_le` (the deliverable): with any
  gap, `∑_{n<N} |∫ v·(v∘τ^[n]∘θ) dμ| ≤ ‖[v]‖²/(1−gap)`, **uniform in the
  time extent**.

The construction is abstract — square torus, asymmetric torus, and the
continuum all instantiate it; a concrete consumer supplies only the
spectral gap and the operator-coincidence identifying `H_phys` with its
own transfer matrix. **Full details and an instantiation guide:
[`docs/transfer-construction.md`](docs/transfer-construction.md)**
(design rationale and ruled-out alternatives:
[`docs/transfer-bridge-spec.md`](docs/transfer-bridge-spec.md)).

### The Feynman–Kac trace dictionary (built, general)

`ReflectionPositivity/TransferSystem.lean` proves the transfer-matrix /
Feynman–Kac correspondence at its **natural generality and in the
kernel-iterate (Fubini) form** — no abstract trace-class operator API
needed, just iterated integrals of kernel products. A `TransferSystem S`
is a single-time-slice space `(ν, k)` with a symmetric nonnegative
transfer kernel `k` (plus σ-finiteness / integrability side-conditions);
it induces the periodic path (Gibbs) measure on `ZMod n → S` with density
`∏_t k(ψ_t, ψ_{t+1})`. Two theorems, **genuinely proved** (axioms
`propext, Classical.choice, Quot.sound`; no correlation identity assumed
as a hypothesis):

* `partition_eq_trace` — `Z_n = ∫ x, kPow (n−1) x x dν`, where `kPow m` is
  the `(m+1)`-fold kernel composition (the kernel of `Tᵐ⁺¹`). This is
  `Z_n = Tr(Tⁿ)`.
* `twoPoint_dictionary` —
  `∫ A(ψ₀)·B(ψ_t) dμ_n = Z_n⁻¹ · ∫∫ A(x)·kPow_{t−1}(x,y)·B(y)·kPow_{n−t−1}(y,x) dν dν`,
  i.e. `Tr(M_A Tᵗ M_B T^{n−t}) / Tr(Tⁿ)`.

Proved by reindexing `ZMod n → Fin n` and peeling slices via
`measurePreserving_piFinSuccAbove` + `integral_prod`, folding the open
arcs into `kPow`. Fully generic over `(S, ν, k)`.

**Which route to use.** These are two complementary builds:

* The **`TransferConstruction`** (GNS) route above is OS reconstruction —
  it works whenever the time translation `τ` preserves positive-time
  observables, i.e. on the **half-infinite / `Nt→∞` cylinder** and the
  continuum. (On a *finite periodic* torus `τ` does **not** preserve a
  strict positive-time half-region, so the GNS transfer operator there is
  ill-defined — established by vetting.)
* The **`TransferSystem`** (kernel-iterate) route here is the one a
  **finite periodic lattice** (e.g. pphi2's φ⁴₂ cylinder) instantiates:
  set `k(x,y) = w(x)·G(x−y)·w(y)`, identify the lattice Gibbs measure with
  the path measure, and read off the `Tⁿ`-trace correlations directly.

**Full design + the maximal-generality discussion:**
[`docs/transfer-construction.md`](docs/transfer-construction.md).

### Graph reflection positivity (FLS)

The Freedman-Lovász-Schrijver framework (JAMS 2007) gives a
**combinatorial reformulation** of RP for graph-theoretic and
statistical-mechanical settings:

* A graph parameter `f` is **multiplicative** if
  `f(G₁ ⊔ G₂) = f(G₁) · f(G₂)`.
* For `k ≥ 0` the **connection matrix** `M(f, k)` has rows / columns
  indexed by isomorphism classes of `k`-labeled graphs, with entry
  `M(f, k)_{G₁, G₂} = f(G₁ G₂)` (the product glues along labels).
* `f` is **reflection-positive** when `M(f, k)` is PSD for every `k`.
* **Rank connectivity** `r(f, k) := rk(M(f, k))` measures the
  "effective dimensionality" of `f` at label-count `k`.
* **Main theorem (FLS 2007 Thm 2.4)**: A multiplicative
  reflection-positive `f` with `r(f, k) ≤ q^k` for some `q` is a
  weighted graph homomorphism function `f = f_H`, with
  `|V(H)| ≤ q`. Proof via the commutative finite-dim C*-algebra
  structure of the GNS quotient.

Downstream uses:

* Characterizing graph parameters expressible as partition functions
  of statistical-mechanical models (vertex-coloring models, Ising,
  Potts, ...).
* Lovász's graph limits theory (Borgs-Chayes-Lovász-Szegedy
  graphons).
* Tensor-network / quantum-information applications (matrix product
  states, PEPS, classical simulability conditions).
* Extremal graph theory / spectral graph theory questions on
  homomorphism counts.

The two programs (OS continuous and FLS discrete) share the same
abstract template — a PSD form on a `*`-semigroup — and the same
GNS-style construction. Whether the shared abstraction pays off in
formalization will be revisited after both Phase-1 deliverables
mature.

## Status

**OS abstract stack complete** (2026-06-03), sorry/axiom-free:

* `Abstract.lean` — the reflection inner product `∫ F·(G∘θ) dμ`, its
  symmetry, additivity, and translation self-adjointness (`θτθ=τ⁻¹`).
* `CauchySchwarz.lean` — reflection Cauchy–Schwarz, the `L²` bridge
  (`reflectionLp`, `inner_reflectionLp`), positivity of the form.
* `PhysicalHilbertSpace.lean` — `ReflectionSystem`, the pre-inner-product
  core, and `physicalHilbertSpace = Completion PosObs`.
* `TransferMatrix.lean` / `VarianceBound.lean` — the `GappedTransfer`
  structure and the geometric-series susceptibility bound
  `∑ |⟪v, Tⁿ v⟫| ≤ ‖v‖²/(1−gap)`.
* `TransferConstruction.lean` — the OS (GNS) transfer operator + Feynman–Kac
  bridge + `Lt`-uniform variance bound (see the section above and
  [`docs/transfer-construction.md`](docs/transfer-construction.md)).
* `TransferSystem.lean` — the general kernel-iterate Feynman–Kac trace
  dictionary (`partition_eq_trace`, `twoPoint_dictionary`) for a finite
  periodic lattice; the route a concrete finite lattice instantiates.

Each headline declaration's `#print axioms` is
`[propext, Classical.choice, Quot.sound]` only. The graph / FLS
(`Graph/`) and chessboard (`Chessboard/`) tracks follow the discharge
order in [PLAN.md](PLAN.md).

## Why a standalone repo

The reflection-positivity material is **mathematically generic** — it
depends only on Mathlib's measure theory + functional analysis + bounded
self-adjoint spectral material, and has clear consumers across several
otherwise-unrelated formalization projects:

| Downstream project | Use case |
|---|---|
| [`pphi2`](https://github.com/mrdouglasny/pphi2) | Layer B2 of `asymInteracting_expMoment_volume_uniform`: cylinder mass gap ⟹ Lt-uniform interacting variance bound (via the geometric-series argument in `VarianceBound.lean`; chessboard NOT needed for this case). Also: cylinder OS3 (`hRP`) discharge via abstract RP + weak-limit inheritance. |
| [`Phi4`](https://github.com/mrdouglasny/pphi2/tree/main/Pphi2) | RP for the square `Z_N^d` lattice + transfer-matrix construction. |
| [`OSforGFF`](https://github.com/mrdouglasny/OSforGFF) | OS reconstruction for the Gaussian free field. |
| [`OSreconstruction`](https://github.com/mrdouglasny/OSreconstruction) | Generic OS reconstruction theorem (Euclidean → Wightman). |
| Future stat-mech / gauge work | RP for spin systems, lattice gauge theories. |
| Future combinatorics / graph-limits work | FLS graph reflection positivity for partition-function characterization. |

The existing pphi2 modules `OSProofs/OS3_RP_Lattice.lean` and
`OS3_RP_Inheritance.lean` provide *concrete* RP for the asym /
square lattice instances; this repo houses the **abstract framework**
they would instantiate, plus the deeper consequences (chessboard,
transfer-matrix construction, variance bounds) that pphi2 and other
downstream projects can then consume off-the-shelf.

## License

Apache 2.0. See `LICENSE` (TODO).

## References

* K. Osterwalder and R. Schrader, *Axioms for Euclidean Green's
  functions, I, II*, Comm. Math. Phys. 31 (1973), 83–112; 42 (1975),
  281–305.
* J. Fröhlich, B. Simon, T. Spencer, *Infrared bounds, phase
  transitions and continuous symmetry breaking*, Comm. Math. Phys.
  50 (1976), 79–95.
* J. Fröhlich, R. Israel, E. H. Lieb, B. Simon, *Phase transitions
  and reflection positivity. I. General theory and long range lattice
  models*, Comm. Math. Phys. 62 (1978), 1–34.
* J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point
  of View*, 2nd ed., Springer (1987), Ch. 6 (lattice transfer matrix),
  Ch. 10 (chessboard estimates), Ch. 19 (constructive applications).
* B. Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Princeton
  (1974), Ch. III (OS axioms + lattice RP).
* J. Glimm, A. Jaffe, T. Spencer, *The Wightman axioms and particle
  structure in the P(φ)₂ quantum field model*, Ann. of Math. 100
  (1974), 585–632 (cluster expansion + RP for the continuum limit).
* M. Freedman, L. Lovász, A. Schrijver, *Reflection positivity, rank
  connectivity, and homomorphism of graphs*, J. Amer. Math. Soc. 20
  (2007), 37–51 (the graph-theoretic reformulation).
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium
  Publications 60 (2012), Ch. 6 (textbook treatment of FLS RP and
  the graph-parameter / graph-limit connection).
