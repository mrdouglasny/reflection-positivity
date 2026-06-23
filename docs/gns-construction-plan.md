# GNS / ground-state transform — scoping plan

**Goal.** Bridge `TransferSystem` (kernel + measure form) and `GappedTransfer`
(operator form) via the **ground-state transform** (Doob `h`-transform; this
is the GNS construction for the transfer system, but the ground-state-transform
name makes the `U_t = (1/λ₀^t) · T^t(· Ω)/Ω` formula easier to recognize).
The bridge lets us pass `Lt`-uniform bounds proved in operator form
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

### The ground-state-transform Hilbert space

* **State space**: `μ_Ω := Ω² · dν` — a probability measure on `S` when
  `∫ Ω² dν = 1` (the "ground state distribution").
* **Hilbert space**: `H_GS := L²(S, μ_Ω; ℝ)`.
* **Cyclic vector**: `Ω_GS := 1` (constant function), with `‖1‖_{L²(μ_Ω)} = 1`.
* **Isometry to `L²(ν)`**: `W : L²(μ_Ω) → L²(ν)`, `W f := f · Ω`. When
  `Ω > 0` ν-a.e., `W` is **unitary** onto `L²(ν)`, not merely an embedding
  into a proper subspace — this removes the "division-by-Ω" anxiety
  noted in the original risk list.
* **Multiplication operator**: for `A : S → ℝ` bounded, `M_A f := A · f`
  is a bounded self-adjoint operator on `H_GS`.
* **Ground-state-transform semigroup**: `U_t f := (1/λ₀^t) · (T^t (f · Ω)) / Ω`.
  Always satisfies `U_t 1 = 1` (Markov property; from `T^t Ω = λ₀^t Ω`).
  **Contraction `‖U_t‖_op ≤ 1` requires an additional hypothesis** —
  positive eigenvector alone is not enough. The right hypothesis is
  either `‖(T/λ₀) f‖_{L²(ν)} ≤ ‖f‖_{L²(ν)}` (normalized-transfer
  contraction), or full `GappedTransfer` packaging on `T̂ = T/λ₀`. In
  either case, the contraction follows from `W` being an isometry:
  `W U_t W⁻¹ = (T/λ₀)^t` on `L²(ν)`, so `‖U_t f‖_{L²(μ_Ω)} = ‖(T/λ₀)^t (Wf)‖_{L²(ν)}`.

### Required additional hypotheses

The abstract `TransferSystem` structure provides only a nonneg symmetric
kernel + Fubini/integrability fields, NOT a bounded `L²(ν)` operator or
spectral bounds. The bridge needs:

* A bounded self-adjoint `T : L²(ν) →L[ℝ] L²(ν)` with `(T f)(x) =ᵐ ∫ k(x,y) f(y) dν`
  (the canonical integral operator built from the kernel).
* `T Ω = λ₀ • Ω` with `λ₀ > 0` and `Ω : S → ℝ`, `Ω > 0` ν-a.e.,
  `∫ Ω² dν = 1`.
* Normalized-transfer contraction `‖T̂‖_op ≤ 1` (where `T̂ = T/λ₀`), or
  equivalently a `GappedTransfer` packaging with `vacuum = Ω` and gap `γ`.
* For the partition-function lower bound `Z_n ≥ λ₀^n` (used in the
  finite-volume correction): `T` positive (not just kernel nonneg) — a
  nonneg symmetric kernel need not define a positive-semidef operator.
  In the pphi2 instance this is proved (transfer = `M_w ∘ Conv_G ∘ M_w`
  with `M_w` self-adjoint and `Conv_G` positive); the abstract bridge
  must take it as a hypothesis.

### The exact GNS / ground-state identity

The identity that powers the bridge — `connected_two_point_le` applied
to the GNS Hilbert space with cyclic vector `1` is **definitionally
equivalent** to it applied to `L²(ν)` with vacuum `Ω` and normalized
transfer `T̂ = T/λ₀`:

```
⟨1, M_A U_t M_B 1⟩_{L²(μ_Ω)}
  = (1 / λ₀^t) · ⟨Ω, M_A T^t M_B Ω⟩_{L²(ν)}
  = ⟨Ω, M_A T̂^t M_B Ω⟩_{L²(ν)}.
```

Proof: pure substitution + `W` unitary (no further gap hypothesis
needed for this identity itself).

### The dictionary bridge — finite-periodic form

**Correct finite-volume comparison** (per codex review 2026-06-22): the
path-measure two-point at separation `t ∈ ZMod Nt` differs from the
ground-state-transform vacuum form by a **wrap-around** term, not a
single `O(γ^Nt)` correction. The trace ratio
`Tr(M_A T̂^t M_B T̂^{Nt-t}) / Tr(T̂^Nt)` carries TWO geometric legs (the
forward arc `T̂^t` and the periodic return arc `T̂^{Nt-t}`).

The cleanest statement is in **connected** form:

```lean
theorem pathMeasure_connected_two_point_finite_periodic_bound
    (Ts : TransferSystem S) (Ω : S → ℝ) (λ₀ γ : ℝ)
    (hΩ_eigen) (hΩ_norm) (hΩ_pos)
    (hT_bdd) (hT_normContract) (hT_positive)
    (hΩ_topGap : ∀ v, ⟪Ω,v⟫_{L²(ν)} = 0 → ‖T̂ v‖ ≤ γ · ‖v‖) (hγ : γ ∈ [0,1))
    (A B : MultiplicationCLMContract Ts.ν)
    (Nt : ℕ) [NeZero Nt] (t : ZMod Nt) (ht : 0 < t.val) (htn : t.val < Nt) :
    |∫ A.A(ψ 0) * B.A(ψ t) ∂(Ts.pathMeasure Nt)
        - (∫ A.A(ψ 0) ∂(Ts.pathMeasure Nt)) * (∫ B.A(ψ t) ∂(Ts.pathMeasure Nt))|
      ≤ C_perp(A, B) · (γ^t.val + γ^(Nt - t.val))     -- the two one-perp-leg
        + C_rem(A, B) · γ^Nt                          -- R·R + denominator + one-point corrections
```

where:

* **`C_perp(A, B) := ‖P₁_{L²(ν)} (A · Ω)‖ · ‖P₁_{L²(ν)} (B · Ω)‖`** controls
  the two **one-perp-leg** terms `P₀·R` and `R·P₀` (from the rank-1
  expansion `T̂^t = P₀ + R^t`, `T̂^{Nt-t} = P₀ + R^{Nt-t}`). This is the
  ground-perp norm `connected_two_point_le` directly supplies.

* **`C_rem(A, B)`** controls the **R·R** doubly-perp term plus the
  **denominator + finite-volume one-point corrections** that don't cancel
  cleanly under the `Z_n = λ₀^n + Tr(T'^n)` split. **Per codex review
  2026-06-23**, this is NOT bounded by `C_perp` alone — the R·R term has
  geometric size `γ^Nt` with a constant involving excited-subspace /
  trace / HS quantities (e.g., `‖P₁ M_A P₁‖_{HS}`, NOT just `‖P₁ M_A Ω‖`),
  and the partition-function denominator correction `Tr(T'^Nt)/λ₀^Nt`
  contributes another `O(γ^Nt)` term that doesn't decompose through
  `connected_two_point_le`. **The bridge takes `C_rem` as a hypothesis**
  (or, in the concrete pphi2 instance, derives it from the explicit
  Gaussian kernel's HS norm).

The decomposition into two explicit terms makes the trace/HS proof
obligation honest rather than hidden in an abstract `C_AB`.

**Why this is `Nt`-uniform after summing**: both decay terms are
summable.
- `Σ_{t=0..Nt-1} (γ^t + γ^{Nt - t}) = 2·(1 - γ^Nt)/(1 - γ) ≤ 2/(1 - γ)`,
  handled by `geom_wrap_sum_le`.
- `Σ_{t=0..Nt-1} γ^Nt = Nt · γ^Nt → 0` as `Nt → ∞`, bounded uniformly
  by `sup_{Nt ≥ 1} Nt · γ^Nt = 1/(e · log(1/γ))` (or whatever the
  exact bound; the point is it's `Nt`-bounded).

The pre-connected raw-comparison form (without the one-point subtraction)
would be `≤ C · (γ^(Nt - t) + γ^Nt)` for the trace-ratio comparison
to the vacuum form; the connected form above is strictly cleaner for
the B2 use because the one-point subtractions cancel the dominant
`λ₀^Nt · P₀·P₀ / λ₀^Nt = ⟨Ω,M_A Ω⟩·⟨Ω,M_B Ω⟩` term explicitly, leaving
only the geometric-decay residuals tracked by `C_perp` and `C_rem`.

### Composition with `connected_two_point_le`

Once the bridge is in place, the pphi2 Layer-B2 use looks like:

```
|path-measure connected 2pt at separation t|
    ≤ C_perp · (γ^t + γ^(Nt - t)) + C_rem · γ^Nt          (finite-periodic bridge)
    ≤ ‖P₁ (A · Ω)‖ · ‖P₁ (B · Ω)‖ · (γ^t + γ^(Nt - t))   (via connected_two_point_le)
                                  + C_rem · γ^Nt
```

Then `Σ_{t<Nt}` uses `geom_wrap_sum_le` (proved) on the dominant term,
and `Σ γ^Nt` on the remainder. Each `‖P₁ (A · Ω)‖_{L²(ν)}` gets bounded
by Piece 1's a-cancellation lemma (`norm_sq_proj_obsTrunc_omega_le`)
for the bounded-cutoff variant `A = A_{K,t}` in pphi2. The `C_rem`
constant in pphi2's concrete instance comes from the Gaussian transfer
kernel's HS norm (`asymTransferKernel` is L² as a kernel on `ℝ^Ns × ℝ^Ns`).

## Pieces

### Piece A — `μ_Ω` and `L²(μ_Ω)` setup (~50-100 lines)

* Define `Ts.groundMeasure (Ω : S → ℝ)` := `Ω² · dν`.
* Prove `IsProbabilityMeasure (groundMeasure Ω)` under `‖Ω‖_{L²(ν)} = 1`.
* `L²(μ_Ω)` is just `Lp ℝ 2 μ_Ω` — no special wrapping needed; downstream
  consumers can construct CLMs there directly.

### Piece B — Multiplication-operator API contract (~30-80 lines)

* **Design decision (2026-06-22):** keep `mulCLM` in pphi2. The GNS bridge
  in reflection-positivity is stated abstractly — it accepts a
  multiplication CLM as an input parameter, and pphi2 supplies its
  existing `mulCLM` instance when consuming the bridge.
* What goes in `reflection-positivity` — the contract structure carries
  both the observable AND the CLM witness with its a.e. spec, NOT just an
  opaque CLM (per codex review 2026-06-22; the theorem statement needs
  to know which observable appears in the path integral):

  ```lean
  structure MultiplicationCLMContract {α : Type*} [MeasurableSpace α]
      (μ : Measure α) where
    A : α → ℝ
    A_meas : Measurable A
    A_bound : ∃ K : ℝ, 0 < K ∧ ∀ᵐ x ∂μ, |A x| ≤ K
    M : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ
    spec : ∀ f, ⇑(M f) =ᵐ[μ] fun x => A x * f x
    selfAdjoint : IsSelfAdjoint M
  ```

* Avoids cross-repo code moves; pphi2's `mulCLM`, `mulCLM_spec`, and
  `mulCLM_isSelfAdjoint` are exactly the fields needed to construct a
  `MultiplicationCLMContract` from a bounded `A`. (If RP later wants to
  build multiplication CLMs internally from a bounded `A`, pphi2's
  `mulCLM` is generic enough to port — not needed for this scope.)

### Piece C — Markov semigroup `U_t` (~100-200 lines)

* Define `U_t : L²(μ_Ω) → L²(μ_Ω)` via `U_t f := (1/λ₀^t) · (T^t (f · Ω)) / Ω`.
  Bounded linear; proof of well-definedness uses `Ω > 0` and the L²-bound
  of `T^t` (already proved).
* Prove `U_t 1 = 1` (Markov; uses `T^t Ω = λ₀^t Ω`).
* Prove `‖U_t‖_op ≤ 1` (contraction; by `W`-unitary transport from
  `hT_normContract` / `GappedTransfer`. The eigenvector / weighting
  alone is NOT enough — see "Required additional hypotheses" above).
* (Optional) Prove `U_t · U_s = U_{t+s}` (semigroup).

### Piece D — Spectral gap of `U_t` on `1`-orthogonal complement (~100-150 lines)

* Establish: `‖U_t f‖_{L²(μ_Ω)} ≤ γ^t · ‖f‖_{L²(μ_Ω)}` for `f ⊥ 1` in
  `L²(μ_Ω)`, where `γ` is the spectral gap of the normalized `T̂` from
  `GappedTransfer`.
* Proof: `⟨f, 1⟩_{L²(μ_Ω)} = 0` iff `⟨f Ω, Ω⟩_{L²(ν)} = 0`. The map
  `f ↦ f · Ω` is an isometric embedding `L²(μ_Ω) ↪ L²(ν)` (with image
  `Ω · L²(μ_Ω)`); the perpendicular-Ω in L²(ν) lifts cleanly.
* Then apply the L²(ν)-gap.

### Piece E0 — Exact GNS / ground-state identity (~100-150 lines)

The standalone identity `⟨1, M_A U_t M_B 1⟩_{L²(μ_Ω)} = (1/λ₀^t) · ⟨Ω, M_A T^t M_B Ω⟩_{L²(ν)}`.
Pure substitution + `W` unitary. **No gap hypothesis required.**

Can be done BEFORE Piece D (the gap inheritance on `1⊥`) — only uses A, B, C.

### Piece E1 — Finite-periodic dictionary bridge (~300-700 lines, the main bridge)

The **main bridge theorem** (corrected statement, per codex review 2026-06-22):

```lean
theorem pathMeasure_connected_two_point_finite_periodic_bound
    (Ts : TransferSystem S)
    (Ω : S → ℝ) (λ₀ γ : ℝ) (hyps_per_required_additional_hypotheses_above)
    (A B : MultiplicationCLMContract Ts.ν)
    (hRem : RemainderHypothesis A B Ts Ω λ₀ γ)  -- bounds C_rem; see below
    (Nt : ℕ) [NeZero Nt] (t : ZMod Nt) (ht : 0 < t.val) (htn : t.val < Nt) :
    |∫ A.A(ψ 0) * B.A(ψ t) ∂(Ts.pathMeasure Nt)
        - (∫ A.A(ψ 0) ∂(Ts.pathMeasure Nt)) * (∫ B.A(ψ t) ∂(Ts.pathMeasure Nt))|
      ≤ ‖vacuumPerp_{L²(ν)} (A.A · Ω)‖ * ‖vacuumPerp_{L²(ν)} (B.A · Ω)‖
          * (γ ^ t.val + γ ^ (Nt - t.val))         -- one-perp-leg terms (P₀R + RP₀)
        + hRem.C_rem * γ ^ Nt                       -- doubly-perp R·R + denominator + 1pt corrections
```

* **Proof structure (corrected per codex re-review 2026-06-23):**
  1. `twoPoint_dictionary` → trace-ratio form `(1/Z_n) · ∫∫ A·kPow_{t-1}·B·kPow_{Nt-t-1}`.
  2. Rank-1 split on **both** kPow factors: `kPow_{m} = λ₀^{m+1} · Ω(x)Ω(y) + R_m(x,y)`, where `R_m` is the (signed) kernel of `T'^{m+1}` with `T' := T - λ₀·P₀`.
  3. Expand the four product terms in the trace integral: **P₀·P₀** (disconnected), **P₀·R** (one perp leg, `γ^(Nt-t)` decay), **R·P₀** (other perp leg, `γ^t` decay), **R·R** (doubly perp, `γ^Nt` decay).
  4. Normalize by `Z_n = λ₀^n + Tr(T'^n) ≥ λ₀^n` (positive operator hypothesis). The denominator's `Tr(T'^n)` correction contributes an additional `O(γ^Nt)` term.
  5. **One-point subtraction**: the finite-volume one-point `(∫ A dpathMeasure_n)` differs from the GNS one-point `⟨Ω, M_A Ω⟩` by another `O(γ^Nt)` term (the denominator/numerator finite-volume corrections). The connected subtraction cancels the **dominant** `λ₀^Nt · ⟨Ω, M_A Ω⟩ · ⟨Ω, M_B Ω⟩` term but leaves the cross-corrections as part of `C_rem`.
  6. **The two perp-leg terms** P₀·R and R·P₀ are bounded by op-norm decay of T' on the ground-perp via `connected_two_point_le`-style algebra: each gives `‖P₁ (A · Ω)‖ · ‖P₁ (B · Ω)‖ · γ^{t-or-(Nt-t)}`.
  7. **The R·R term and the finite-volume one-point corrections** are bundled into `hRem.C_rem`. The doubly-perp R·R term needs trace-class / HS norm control such as `‖P₁ M_A P₁‖_HS · ‖P₁ M_B P₁‖_HS`, NOT just the ground-perp norms `‖P₁ M_A Ω‖`. The bridge takes `C_rem` as a hypothesis; pphi2's concrete instance derives it from the explicit Gaussian-kernel HS norm.
  8. Bridge `vacuumPerp_{L²(μ_Ω)} ↔ vacuumPerp_{L²(ν)}` via `W` unitary.

The `RemainderHypothesis` abstraction (`C_rem` + the integrability/HS-bound
proof obligation) is what an abstract `TransferSystem` user must supply.
Field sketch:

```lean
structure RemainderHypothesis (A B : MultiplicationCLMContract Ts.ν)
    (Ts : TransferSystem S) (Ω : S → ℝ) (λ₀ γ : ℝ) where
  C_rem : ℝ
  C_rem_nonneg : 0 ≤ C_rem
  remainder_bound : ∀ (Nt : ℕ) [NeZero Nt],
    (the R·R + denominator + finite-volume one-point trace estimate)
      ≤ C_rem * γ ^ Nt
```

Bundling the bound itself (not just the constant) keeps the contract
honest — any consumer must demonstrate the combined finite-periodic
remainder estimate, not just guess a constant. In pphi2's instance,
the Gaussian transfer kernel's explicit HS norm closes
`remainder_bound` directly.

* **Concretely needs**: a kernel-level analog of the rank-1 split (signed-kernel `R_m := kPow_m - λ₀^{m+1} · Ω(x)Ω(y)`) with op-norm decay tracked through L²(ν) integration. The pphi2-side `asymKernelPerp_*` lemmas (still to be written) would be the concrete witness; in RP it's stated abstractly via the `MultiplicationCLMContract` + op-norm-gap inputs.

### Piece F — Composition with `connected_two_point_le` (~50-100 lines)

* Combine Piece E1 with the existing `connected_two_point_le` (instantiated
  on the GNS Hilbert space `L²(μ_Ω)` with `vacuum = 1` and the transferred
  gap from Piece D).
* Output: `Nt`-uniform bound on the path-measure connected two-point of
  bounded observables, summable via `geom_wrap_sum_le` — this is exactly
  the pphi2 Layer B2 input.

## Piece dependencies

Per codex review 2026-06-22, the original linear chain can be loosened:

```
A (groundMeasure + groundIsometry) ──┐
                    ├──► E0 (exact identity) ──► E1 (finite-periodic bridge) ──► F (connected) 
B (CLM contract) ──┐│                                          │
                   ┘└──► C (semigroup) ──► D (gap on 1⊥) ──────┘
```

- E0 only needs A+B+C+isometry — no gap.
- D is needed for F, not for E0 or E1 (the L²(ν) gap pulls through the
  isometry directly).

## Aggregate scope (provisional; codex flagged the original as optimistic)

| Piece | Lines | Difficulty |
|---|---|---|
| A (groundMeasure + isometry W setup) | 80-150 | ★ |
| B (`MultiplicationCLMContract` structure) | 30-80 | ★ |
| C (`U_t` Markov semigroup + Markov property) | 150-300 | ★★ |
| D (gap on `1⊥`) | 100-200 | ★★ |
| E0 (exact GNS identity, no gap) | 100-150 | ★ |
| E1 (finite-periodic bridge with rank-1 kernel split) | 300-700 | ★★★ |
| F (connected two-point composition) | 50-100 | ★ |
| **Total** | **810-1680** | ★★ |

**Wall-clock**: ~2-4 active weeks (widened from the original ~1-2 weeks
after codex's correction-term and trace-algebra findings — the
finite-periodic bridge is the dominant work and was underestimated).

Unblocks pphi2 Layer B2 (item 3) and OS4 clustering items 14 + 15 (which
share the same bridge need on the square lattice).

## First PR target

**Pieces A + B + E0** (setup + CLM contract + exact GNS identity). E0
is the cleanest standalone deliverable — no gap hypothesis, just pure
algebra of the unitary `W`. Together ~210-380 lines, self-contained.
Demonstrates the structure works and gives downstream consumers the
basic types AND the headline identity without committing to the full
finite-periodic bridge yet.

## Alternatives considered

* **Direct kernel-only route** (stay in `TransferSystem`; rank-1 split
  on kernels; periodic bound on traces; never build `L²(μ_Ω)` or `U_t`).
  Viable in principle but duplicates the operator gap machinery
  `GappedTransfer` already provides, and still needs the same
  signed-kernel / trace-positivity infrastructure. Saves Pieces A+C+D+E0
  but adds equivalent work inline.
* **`TransferConstruction` route** (use the existing CTI machinery to
  build the Hilbert space more definitionally). Possible, but for finite
  periodic `pathMeasure Nt` it still has to handle the periodic
  wrap-around — doesn't make the `γ^t + γ^(Nt-t)` correction structure
  go away.

**Decision**: the ground-state-transform / GNS route is preferred because
(a) the unitary `W : L²(μ_Ω) → L²(ν)` makes the gap inheritance clean,
(b) the abstract bridge is reusable for OS4 clustering, and (c) the
trace-algebra core (rank-1 split + signed remainder) is needed by any
route anyway.

## Risks / unknowns (expanded per codex review 2026-06-22)

* **Division by Ω in `L²(μ_Ω)`** is **harmless** when `Ω > 0` ν-a.e.
  The `W : f ↦ f·Ω` is a **unitary** `L²(μ_Ω) → L²(ν)` (not just an
  embedding), so `‖T^t(f·Ω)/Ω‖_{L²(μ_Ω)} = ‖T^t(f·Ω)‖_{L²(ν)}`. The
  earlier risk text about positivity-improving was wrong-pointed.
* **Quantitative gap on `1⊥` in `L²(μ_Ω)`** does NOT follow from
  positivity-improving alone. It must be transported through the
  isometry `W` from a hypothesized L²(ν) gap on `Ω⊥`. Either bundle
  `T̂ = T/λ₀` as a `GappedTransfer` with `vacuum = Ω` (then the gap is
  given), or take the gap on `Ω⊥` as an explicit hypothesis.
* **`Z_n ≥ λ₀^n`** is NOT a consequence of nonneg kernel entries alone
  — a symmetric nonneg kernel need not define a positive-semidef
  operator (negative spectrum can contribute to odd traces). Needs
  explicit `T` positive-operator hypothesis. In the pphi2 instance
  this is proved (transfer = `M_w ∘ Conv_G ∘ M_w` with `M_w` self-adjoint
  and `Conv_G` positive); the abstract bridge must take it as a
  hypothesis or prove it from an even-power HS bound.
* **Trace algebra under bare `TransferSystem`** is not safe.
  `TransferSystem` intentionally avoids abstract trace-class API; the
  rank-1 trace split (`Tr(T'^n)`, `T'` positive, etc.) needs either
  (a) a finite-dim / trace-class / HS kernel layer with signed-kernel
  integrability for the remainder, or (b) a purely kernel-integral
  version of the rank-1 split + bounds. Plan: (b), stated in terms of
  the signed kernel `R_m := kPow_m - λ₀^{m+1}·Ω(x)Ω(y)` with op-norm
  decay verified via L²(ν) integration.
* **Finite-volume one-point corrections.** The finite-volume connected
  covariance subtracts finite-volume means, NOT GNS/vacuum means; these
  agree only up to a corresponding finite-volume correction. The Piece
  E1 statement above subtracts the path-measure one-points correctly;
  the correction is absorbed into `hRem.C_rem · γ^Nt` (it does not fit
  inside the `C_perp` wrap-around term).
* **Correction constants depend on observable norms** and on whatever
  trace/HS class controls the return leg — not just functions of `γ`.
  The Piece E1 statement tracks the one-perp constants via the
  vacuum-perp norms `‖vacuumPerp_{L²(ν)} (A · Ω)‖` and the trace/HS
  remainder via `hRem.C_rem`.
* **Unbounded pphi2 slice observables** (linear `⟨g,·⟩` are unbounded
  on `L²(ν)`) are handled by Piece 1's truncation + Piece 3's `K → ∞`
  DCT limit **downstream** of this bridge. The abstract bridge here is
  for bounded observables only — the truncation/limit is pphi2's job.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics II:
  Fourier Analysis, Self-Adjointness* — GNS construction (XII.1).
* J. Glimm, A. Jaffe, *Quantum Physics* §6.1, §19.4 — transfer matrix
  GNS in lattice QFT.
* O. Bratteli, D. Robinson, *Operator Algebras and Quantum Statistical
  Mechanics I* §2.3.3 — GNS, cyclic vectors, KMS states.
