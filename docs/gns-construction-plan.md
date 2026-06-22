# GNS construction — scoping plan

**Goal.** Bridge `TransferSystem` (kernel + measure form) and `GappedTransfer`
(operator form) via the Gelfand-Naimark-Segal (GNS) construction. The bridge
lets us pass `Lt`-uniform bounds proved in operator form
(`connected_two_point_le`) back to path-measure two-point functions
(`twoPoint_dictionary`), which is the missing piece for the pphi2
Layer-B2 wiring (Piece 2 of the Route-A blueprint —
`asymInteractingVariance_le_freeVariance_Lt_uniform` discharge).

## Why this lives in `reflection-positivity`

* The construction is purely abstract — it depends only on the
  `TransferSystem` structure + positivity-improving assumption.
* Multiple downstream consumers: pphi2 Layer B2 (item 3), plus the OS4
  clustering items 14 + 15 which need the same trace-form ↔ operator-form
  bridge (`planning/INDEX.md`'s "square trace dictionary" gap).
* Keeps the abstract machinery out of pphi2; reflection-positivity is the
  natural home (sits next to `connected_two_point_le`,
  `averaged_susceptibility_bound`).

## What we want

Given a `TransferSystem S` with kernel `k`, reference measure `ν`, and
a positive top eigenvector `Ω : S → ℝ` with eigenvalue `λ₀ > 0` and
L²-normalization `∫ Ω² dν = 1`:

### The GNS Hilbert space

* **State space**: `μ_Ω := Ω² · dν` — a probability measure on `S` (the
  "ground state distribution").
* **Hilbert space**: `H_GNS := L²(S, μ_Ω; ℝ)`.
* **Cyclic vector**: `Ω_GNS := 1` (constant function), with `‖1‖_{L²(μ_Ω)} = 1`.
* **Multiplication operator**: for `A : S → ℝ` bounded, `M_A f := A · f`
  is a bounded self-adjoint operator on `H_GNS`.
* **Markov semigroup**: `U_t f := (1/λ₀^t) · (T^t (f · Ω)) / Ω`. This is
  the **ground-state transformation** of `T`, and `U_t : H_GNS → H_GNS` is
  a contraction (in fact, a Markov operator with `U_t 1 = 1`).

### The dictionary bridge

```lean
theorem pathMeasure_two_point_GNS_form
    (Ts : TransferSystem S) (Ω : S → ℝ) (λ₀ : ℝ) (hΩ_eigen, hΩ_norm, hΩ_pos)
    (A B : S → ℝ) (hA_bdd : ∃ K, ∀ x, |A x| ≤ K) (hB_bdd : ...)
    (Nt : ℕ) [NeZero Nt] (t : ZMod Nt) (ht : 0 < t.val) (htn : t.val < Nt) :
    |∫ A(ψ 0) * B(ψ t) ∂(Ts.pathMeasure Nt)
        - ⟨(1 : L²(μ_Ω)), (M_A ∘ U_{t.val} ∘ M_B) (1 : L²(μ_Ω))⟩|
      ≤ correctionTerm Nt
```

where `correctionTerm Nt = O(γ^Nt)` (where `γ` is the spectral gap of the
normalized `T̂ = T/λ₀` on the `Ω`-orthogonal complement in L²(ν)).

The bound is **Nt-uniform** (the correction is bounded by `γ` for all `Nt ≥ 1`),
which is what pphi2 Layer B2 needs.

### Composition with `connected_two_point_le`

Once the bridge is in place, the pphi2 use looks like:

```
|path-measure connected 2pt| ≤ |GNS connected 2pt| + correctionTerm
                              ≤ γ^t · ‖P₁ M_A 1‖_{GNS} · ‖P₁ M_B 1‖_{GNS}
                                                            + correctionTerm
```

and the GNS-side ground-perpendicular norm `‖P₁ M_A 1‖_{GNS}` is exactly
`‖M_A Ω - ⟨Ω, M_A Ω⟩ Ω‖_{L²(ν)} / ‖Ω‖`, which is what Piece 1's
a-cancellation lemma bounds.

## Pieces

### Piece A — `μ_Ω` and `L²(μ_Ω)` setup (~50-100 lines)

* Define `Ts.groundMeasure (Ω : S → ℝ)` := `Ω² · dν`.
* Prove `IsProbabilityMeasure (groundMeasure Ω)` under `‖Ω‖_{L²(ν)} = 1`.
* `L²(μ_Ω)` is just `Lp ℝ 2 μ_Ω` — no special wrapping needed; downstream
  consumers can construct CLMs there directly.

### Piece B — Multiplication-operator API contract (~20-50 lines)

* **Design decision (2026-06-22):** keep `mulCLM` in pphi2. The GNS bridge
  in reflection-positivity is stated abstractly — it accepts a
  multiplication CLM as an input parameter, and pphi2 supplies its
  existing `mulCLM` instance when consuming the bridge.
* What goes in `reflection-positivity`: a `def` or `structure` for the
  multiplication-CLM contract — basically just `M_A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`
  together with the a.e. specification `⇑(M_A f) =ᵐ A · f` and the
  self-adjointness `IsSelfAdjoint M_A` (for real-valued `A`).
* Avoids cross-repo code moves; pphi2's `mulCLM` continues to be the
  concrete witness without duplication.

### Piece C — Markov semigroup `U_t` (~100-200 lines)

* Define `U_t : L²(μ_Ω) → L²(μ_Ω)` via `U_t f := (1/λ₀^t) · (T^t (f · Ω)) / Ω`.
  Bounded linear; proof of well-definedness uses `Ω > 0` and the L²-bound
  of `T^t` (already proved).
* Prove `U_t 1 = 1` (Markov; uses `T^t Ω = λ₀^t Ω`).
* Prove `‖U_t‖_op ≤ 1` (contraction; needs Cauchy-Schwarz + the L²-Ω
  weighting).
* (Optional) Prove `U_t · U_s = U_{t+s}` (semigroup).

### Piece D — Spectral gap of `U_t` on `1`-orthogonal complement (~100-150 lines)

* Establish: `‖U_t f‖_{L²(μ_Ω)} ≤ γ^t · ‖f‖_{L²(μ_Ω)}` for `f ⊥ 1` in
  `L²(μ_Ω)`, where `γ` is the spectral gap of the normalized `T̂` from
  `GappedTransfer`.
* Proof: `⟨f, 1⟩_{L²(μ_Ω)} = 0` iff `⟨f Ω, Ω⟩_{L²(ν)} = 0`. The map
  `f ↦ f · Ω` is an isometric embedding `L²(μ_Ω) ↪ L²(ν)` (with image
  `Ω · L²(μ_Ω)`); the perpendicular-Ω in L²(ν) lifts cleanly.
* Then apply the L²(ν)-gap.

### Piece E — Path-measure two-point in GNS form (~150-250 lines)

* The **main bridge theorem**: `pathMeasure_two_point_GNS_form` above.
* Proof: Two parts.
  1. Express `∫ A(ψ 0) B(ψ t) ∂pathMeasure` via `twoPoint_dictionary`,
     then expand `kPow` via the rank-1 split `kPow_{m} = λ₀^{m+1} Ω⊗Ω + R_m`.
     The `Ω⊗Ω` term gives the GNS form (after dividing by `Z_n`).
  2. The `R_m` term contributes the `O(γ^Nt)` correction. Use the L²(ν)
     op-norm decay of `T'^m` to bound it.
* The `Z_n ≥ λ₀^n` inequality is needed (from `T'` positive). May need a
  separate lemma `partition_ge_groundEigenvalue_pow`.

### Piece F — Connected two-point bound via GNS + `connected_two_point_le` (~50-100 lines)

* Combine Piece E with the existing `connected_two_point_le` (instantiated
  on the GNS `GappedTransfer`).
* Output: `Nt`-uniform bound on the path-measure connected two-point of
  bounded observables, which is exactly the pphi2 Layer B2 input.

## Aggregate scope

| Piece | Lines | Difficulty |
|---|---|---|
| A (groundMeasure setup) | 50-100 | ★ |
| B (mulCLM) | 50-100 (or 0 if reusing pphi2's) | ★ |
| C (Markov semigroup) | 100-200 | ★★ |
| D (gap on `1`-perp) | 100-150 | ★★ |
| E (main bridge) | 150-250 | ★★★ |
| F (connected two-point) | 50-100 | ★ |
| **Total** | **500-900** | ★★ |

**Wall-clock**: ~1-2 active weeks per the project's calibrated heuristic.
Unblocks pphi2 Layer B2 (item 3) and OS4 clustering items 14 + 15 (which
share the same bridge need on the square lattice).

## First PR target

**Pieces A + B** (setup + mulCLM port). Together ~100-200 lines,
self-contained. Demonstrates the structure works and gives downstream
consumers the basic types without committing to the semigroup yet.

## Risks / unknowns

* **Integrability of `T^t (f · Ω)` in L²(μ_Ω)** for `f ∈ L²(μ_Ω)`. Needs
  `f · Ω ∈ L²(ν)` (true: `‖f · Ω‖_{L²(ν)} = ‖f‖_{L²(μ_Ω)}`), so `T^t (f · Ω)
  ∈ L²(ν)`, but we need it to be in `Ω · L²(μ_Ω)` (so division by Ω makes
  sense). Use positivity-improving + the eigenvector property.
* **Vet the bound's correction-term form** before formalizing — same
  discipline as crux-2. The `O(γ^Nt)` bound is the heuristic; the precise
  constant depends on `Tr(T'^n)/Tr(T^n)`.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics II:
  Fourier Analysis, Self-Adjointness* — GNS construction (XII.1).
* J. Glimm, A. Jaffe, *Quantum Physics* §6.1, §19.4 — transfer matrix
  GNS in lattice QFT.
* O. Bratteli, D. Robinson, *Operator Algebras and Quantum Statistical
  Mechanics I* §2.3.3 — GNS, cyclic vectors, KMS states.
