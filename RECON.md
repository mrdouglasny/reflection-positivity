# Recon report — Mathlib + catalogs coverage for RP

*2026-06-01. Initial-milestone step 1 (per PLAN.md). Informs the
`Abstract.lean` / `CauchySchwarz.lean` design before any code lands.*

## Verdict

No abstract, measure-theoretic reflection-positivity API exists in
Mathlib. Our own catalogs contain substantial *domain-specific* RP
(free covariance, GFF, lattice instances) and one *exploratory
abstract* treatment (`graphops-qft`), but nothing reusable off the
shelf for the clean `μ + θ + A₊` form the plan targets. The repo is
effectively greenfield for `Abstract.lean`; we build on Mathlib
measure theory + the quadratic-discriminant lemma.

## Mathlib coverage

* **Reflection positivity**: none. No `ReflectionPositive`,
  `reflectionInnerProduct`, or OS-axiom content.
* **Measure-preserving involutions**: `MeasureTheory.MeasurePreserving`
  exists and is the right primitive. An "involution" is just
  `θ ∘ θ = id` (`Function.Involutive`); `MeasurePreserving θ μ μ`
  packages the measure invariance. The change-of-variables we need for
  form symmetry is `MeasurePreserving.integral_comp` /
  `MeasurePreserving.lintegral_comp` (composition with a measurable
  bijection leaves the integral unchanged).
* **Cauchy-Schwarz engine**: `inner_mul_le_norm_mul_norm` is for genuine
  inner-product spaces (too strong — we have only a PSD form). The right
  tool for a merely-PSD symmetric bilinear form is the discriminant
  lemma `discrim_le_zero` (`Mathlib.Algebra.QuadraticDiscriminant`):
  `(∀ x, 0 ≤ a*x^2 + b*x + c) → discrim a b c ≤ 0`. Feed it the
  nonneg quadratic `t ↦ B(F - t·G, F - t·G)`.
* **Pre-Hilbert quotient** (for `CauchySchwarz.lean`'s
  `physicalHilbertSpace`): Mathlib has `Submodule.Quotient` and
  `InnerProductSpace.Core`, but "quotient by the kernel of a PSD form
  → genuine inner product → completion" is not packaged. Expect bespoke
  setup. NOT needed for the CS smoke test itself (CS is purely the
  discriminant argument on the form), so it does not gate the milestone.

## Catalog coverage (our own projects)

RP hits by project: `aqft2` 63, `OSforGFF(in3D)` ~76, `pphi2` 14,
`Phi4` 11, `graphops-qft` 7, others few. Almost all are
**domain-specific**: `freeCovariance_reflection_positive*`,
`covarianceReflectionPositive_gaussianFreeField*`,
`rpInnerProduct` for the GFF. Useful as *instances* / test cases later,
not as the abstract layer.

### `graphops-qft` — closest prior art (exploratory, mostly `sorry`)

`GraphopsQFT/Basic/ReflectionPositivity.lean` has the design we are
generalizing:

* `HasReflection (Ω) (μ)` — bundles involution `Θ`, `MeasurePreserving Θ μ μ`,
  and a half-space `upper : Set Ω` with `reflection_maps`. **Good design
  reference** for how to package the reflection data. (We will use a
  sub-σ-algebra `A₊` rather than a `Set`, per PLAN, since that is the OS
  formulation and composes better with conditional expectation.)
* `Graphop.IsReflectionPositive` — `0 ≤ ∫ f·(A(f∘Θ)) dμ` for `f`
  supported on `upper`. Tied to a `Graphop` operator `A`; our form drops
  `A` (it is the identity / pure pairing `∫ F·(G∘θ)`).
* `ConnectionMatrix`, `reflectionPositive_iff_connectionMatrix_psd`
  (`sorry`), `reflectionPositive_of_limit` (`sorry`) — directly relevant
  to `Graph/` and `LatticeInstance.weak_limit`; reuse the *statements* as
  templates.

Takeaway: `graphops-qft` proves the abstraction is viable but left the
hard lemmas open. We are not blocked by it and should not depend on it
(different repo, `Graphop`-specific, unproved); we lift design ideas
only.

### `pphi2` — the consumer interface (exact names)

| Name | Status | Location |
|---|---|---|
| `asymInteracting_expMoment_volume_uniform` | **axiom** (Layer B2 target) | `Pphi2/AsymTorus/AsymContinuumLimit.lean:601` |
| `asymMassGap_pos` | proved | `Pphi2/AsymTorus/AsymPositivity.lean:136` |
| `asymInteractingVariance_le_freeVariance_lattice` | proved | `Pphi2/AsymTorus/AsymVarianceBound.lean:101` |
| `asymInteractingVariance_le_freeVariance_torus` | proved | `Pphi2/AsymTorus/AsymVarianceBound.lean:208` |
| `rp_closed_under_weak_limit` | proved | `Pphi2/OSProofs/OS3_RP_Inheritance.lean:87` |
| `action_decomposition` (`S = S₊ + S₋∘θ`) | proved | `Pphi2/OSProofs/OS3_RP_Lattice.lean:151` |

These confirm the adoption-plan adapter targets in PLAN.md §"Adoption
plan" are real and proved. `asymMassGap_pos` is the input to
`VarianceBound.lean`'s deliverable; `action_decomposition` is what
`LatticeInstance.lean` must subsume.

## Design decisions taken from recon

1. **Reflection data**: define `reflectionInnerProduct μ θ F G := ∫ x, F x * G (θ x) ∂μ`
   for `F G : Ω → ℝ`. Keep `θ : Ω → Ω` + `Function.Involutive θ` +
   `MeasurePreserving θ μ μ` as separate hypotheses on the lemmas (not yet
   bundled into a structure — bundle later if it pays off, à la
   `HasReflection`).
2. **`A₊` as a sub-σ-algebra** `m₊ : MeasurableSpace Ω` with `m₊ ≤ ` the
   ambient. `IsReflectionPositive` quantifies over `F` that are
   `m₊`-`Measurable` (and integrable as needed for the form).
3. **CS smoke test is algebra, not analysis**: prove
   `reflectionInnerProduct` is symmetric (change of variables via
   `MeasurePreserving` + involution) and bilinear (needs integrability
   hyps), then CS via `discrim_le_zero`. No Hilbert-space machinery, no
   spectral theorem — consistent with PLAN recalibration #4.
4. **No dependency on `graphops-qft`**; lift design only.

## Design note — `physicalHilbertSpace` (next phase, recon 2026-06-01)

The Lp-level construction has a clean shape once the right Mathlib
pieces are identified:

* **Reflection operator on L²**: `R := Lp.compMeasurePreserving θ hθ`
  (`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`). It is an
  `Lp ℝ 2 μ →+ Lp ℝ 2 μ`, norm-preserving (`isometry_compMeasurePreserving`),
  with `coeFn_compMeasurePreserving : R g =ᵐ[μ] g ∘ θ`. (Bundled only as
  `→+`; ℝ-linearity in the scalar holds and is provable from `coeFn`.)
* **Reflection form as a twisted L² inner product**: on `Lp ℝ 2 μ`,
  `B(f, g) := ⟪f, R g⟫_{L²}` where `⟪·,·⟫` is the genuine L² inner
  product (`L2Space.inner_def : ⟪f,g⟫ = ∫ a, f a * g a`, real case).
  Then `B(f, g) = ∫ f · (g ∘ θ) = reflectionInnerProduct` (a.e. via
  `coeFn_compMeasurePreserving`). Bilinearity/continuity come for free
  from the L² inner product + `R` — *no* manual integrability juggling.
* **Positive-time subspace**: `lpMeas ℝ ℝ mPos 2 μ : Submodule ℝ (Lp ℝ 2 μ)`
  (`ConditionalExpectation/AEMeasurable.lean`) — already a submodule,
  `mem ↔ AEStronglyMeasurable[mPos]`. RP ⟹ `0 ≤ B(f,f)` on it.
* **Kernel + quotient**: `N := {f ∈ lpMeas : B(f,f) = 0}` is a submodule
  (radical lemma `inner_eq_zero_of_self_eq_zero` ⟹ `B`-orthogonal to all,
  so closed under `+`/`•`). The quotient `lpMeas ⧸ N` carries the
  definite form `B`, i.e. an `InnerProductSpace.Core`; its completion
  (`Analysis/InnerProductSpace/Completion.lean`) is `H_phys`.

**RESOLVED route (recon 2026-06-01; Codex-corroborated).**
Mathlib has the *entire* PSD-form → Hilbert-space pipeline prebuilt — no
bespoke quotient/completion API needed:

1. `PreInnerProductSpace.Core ℝ ·` (`InnerProductSpace/Defs.lean:136`) is
   a PSD, **possibly degenerate** inner-product core: fields
   `conj_inner_symm` (= our symmetry), `re_inner_nonneg` (= RP positivity),
   `add_left`, `smul_left` (= bilinearity). Build it from `B(f,g)=⟪f,Rg⟫`.
   (`InnerProductSpace.Core` *adds* `definite`; we do **not** have/need that.)
2. `InnerProductSpace.ofCore` (`Defs.lean:568`) takes a
   `PreInnerProductSpace.Core` and yields a *seminormed* inner product
   space (`SeminormedAddCommGroup` + `InnerProductSpace`) — degeneracy ⇒
   seminorm, exactly our case.
3. `SeparationQuotient` (`InnerProductSpace/Completion.lean:43`):
   `instance : InnerProductSpace 𝕜 (SeparationQuotient E)`. The separation
   quotient is the quotient by `nullSubmodule` = `{x : ‖x‖ = 0}`
   (`Normed/Group/NullSubmodule.lean`) = our radical `N`. This produces the
   genuine *definite* inner product on `V/N`.
4. `UniformSpace.Completion.innerProductSpace`
   (`InnerProductSpace/Completion.lean:89`): `InnerProductSpace 𝕜 (Completion E)`.

So `H_phys := UniformSpace.Completion V_B`, where `V_B` is a `Module ℝ`
carrier for the positive-time observables with the `ofCore` structure
from `B`. **`Completion` separates *and* completes in one step**
(`Completion := SeparationQuotient (CauchyFilter ·)`), so no explicit
`SeparationQuotient V_B` stage is required (use `SeparationQuotient V_B`
on its own only if the *uncompleted* definite quotient is independently
wanted).

**Copy-paste template**: `Analysis/InnerProductSpace/Reproducing.lean`
(~line 218, the RKHS `H₀ K` / `OfKernel` construction) is the exact
pattern —
```
instance : PreInnerProductSpace.Core 𝕜 (H₀ K) where ...
instance : InnerProductSpace 𝕜 (H₀ K) := .ofCore _
abbrev OfKernel := UniformSpace.Completion (H₀ K)
```
Follow it: define a `Module`-only carrier type for the positive-time
observables, install the `PreInnerProductSpace.Core` from `B`, `.ofCore`,
then `Completion`. This sidesteps the competing-norm clash (the carrier
is fresh, not `lpMeas` with its L² norm) and reuses all prebuilt API.

**Completion IS needed** (corrects the Q1 conjecture above): the relevant
topology is the `B`-seminorm, which is *strictly weaker* than the ambient
L²-norm (`B(f,f)=∫f·(f∘θ)` can be ≪ `‖f‖²`). `N` is L²-closed but `V` need
not be complete in the `B`-seminorm, so the abstract completion is real.

## The measure→operator bridge (analysis, 2026-06-02)

Constructing a concrete `GappedTransfer` on `H_phys` from a
reflection-positive measure needs a time translation `τ` with
`τ ∘ θ ∘ τ = θ` (`θτθ = τ⁻¹`; done: `reflectionInnerProduct_comp_left`
gives self-adjointness `⟨F∘τ,G⟩_θ = ⟨F,G∘τ⟩_θ`). The transfer operator is
`[f] ↦ [f∘τ]`. The crux is the **contraction estimate** `‖T‖ ≤ 1`:

- self-adjointness gives `‖Tf‖² = ⟨f, T²f⟩`, and reflection CS gives
  log-convexity `sₙ² ≤ s_{n-1} s_{n+1}` where `sₙ = ‖Tⁿf‖`;
- BUT closing the bootstrap to `s₁ ≤ s₀` requires an **a-priori bound**
  that `T` is bounded (`sₙ ≤ C Rⁿ`). This is the step textbooks hand-wave;
  it is the real formalization difficulty.

**Reframing for the pphi2 critical path.** The Layer B2 *deliverable* —
`GappedTransfer.susceptibility_le` (uniform-in-`L_t` variance bound) — is
DONE and is abstract over any inner product space. For pphi2's cylinder
(a finite/nice lattice) the transfer matrix is manifestly bounded, so the
a-priori-boundedness subtlety does not arise: pphi2 can construct its
concrete `T` and supply it as a `GappedTransfer`, then apply
`susceptibility_le`. The fully general measure→`T` construction (with the
a-priori bound) is a library-completeness enhancement, **not strictly on
pphi2's critical path**. If pursued, the clean Lean route is likely to
take boundedness (or the contraction `⟨f∘τ,f∘τ⟩_θ ≤ ⟨f,f⟩_θ`) as a
hypothesis matching what the concrete setting provides, rather than
deriving it via the convexity bootstrap.

## One formalization wrinkle (`physicalHilbertSpace`)

**One formalization wrinkle**: `ofCore` installs a `SeminormedAddCommGroup`
on the carrier, but `lpMeas` already carries the L² `NormedAddCommGroup`.
To avoid the competing-instance clash, build the core on a type *synonym*
(or plain module wrapper) of `V` that carries only the `Module ℝ`
structure — the standard Mathlib `ofCore` usage pattern (`letI`/local
instances). This is the main subtlety; the rest is assembling prebuilt API.
