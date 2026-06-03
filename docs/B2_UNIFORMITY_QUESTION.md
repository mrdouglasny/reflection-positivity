# Vetting brief: does pphi2 Layer B2 require a uniform-in-`a` mass gap?

*Drafted 2026-06-02 for expert vetting. Self-contained. The question is
whether the `Lt`-uniform interacting variance bound (pphi2's Layer B2)
can be obtained from the **per-`a`** cylinder transfer-matrix mass gap via
a geometric series, or whether it secretly requires the **uniform-in-`a`**
(continuum) mass gap — the Fröhlich–Simon–Spencer / Glimm–Jaffe–Spencer
chessboard input.*

## RESOLUTION (expert vetting, 2026-06-02)

**Position P is correct, *because* `Ls` is fixed.** The proposed
reconciliation (§4) is confirmed: P and G analyze different thermodynamic
regimes. FSS/GJS chessboard is required only for the **thermodynamic**
limit (`Ls→∞`), where φ⁴₂ can undergo symmetry breaking and the gap can
vanish. On a **fixed** spatial cylinder, the continuum Hamiltonian
`H(Ls)` has a finite spatial cutoff, hence (compact resolvent difference
vs the free Hamiltonian on a finite interval) **purely discrete bottom
spectrum and a strictly positive gap `m > 0`**. By norm-resolvent
convergence `T_a → e^{−a H(Ls)}` as `a→0`, the lattice gap `m_a → m > 0`,
so `inf_a m_a > 0` for small `a` — **no chessboard needed**. Literature
precedent: **Simon, "The P(φ)₂ Euclidean (Quantum) Field Theory" (1974),
Ch. VI** (finite-volume / cylinder), with lattice→continuum gap
convergence via Nelson hypercontractivity + resolvent convergence
(Thm V.15, Ch. VI.V). GRS correlation inequalities control the `a→0`
bounds at fixed volume; the spectral-gap literature bifurcates only at the
`Lt, Ls→∞` step (fixed-`Ls` → easy compact-resolvent path; full 2D plane →
FSS chessboard path).

**The `1/a` cancellation trap (decisive for the formalization).** The
abstract `susceptibility_le` yields `Σ_{t<Nt} γ^t ≤ 1/(1−γ)` with
`γ = e^{−m_a a}`, so `1/(1−γ) ≈ 1/(m_a a)` **diverges as `1/a`**. This
divergence is physically correct (a discrete sum over `Nt` time slices);
it is the lattice time-measure `a` times the sum that gives the continuum
`a·Σ ≈ 1/m_a`. Since the **target is a ratio** `Var_int ≤ C·Var_free`, and
`Var_free` carries the *same* `1/a` lattice-sum divergence
(`1/(1−e^{−m_free a})`), the `1/a` factors **cancel in the ratio**, leaving
`C ≈ m_free/m_a`, finite and `a`-uniform (since `m_a → m > 0`). Finiteness
does **not** require FSS, but it **does** require that B2 forms the
interacting/free ratio (dividing the two geometric series) **before**
taking any `sup` over `a` — never evaluating `1/(1−γ)` as a standalone
magnitude.

**Formalization consequence.** `susceptibility_le` (interacting upper
bound) is necessary but not sufficient: the discharge must (a) keep
everything in dimensionless ratio form with the shared `a²` spacetime
measure as an uninstantiated common factor, and (b) supply a free-side
*lower* bound `Var_free ≳ 1/(1−γ_free)` — which is free-Gaussian-specific
(explicit covariance `⟨f,(−Δ_a+m²)⁻¹f⟩`), hence pphi2-side, not abstract.
The constant is then `C → m_free/m_int` with `m_int` the fixed-`Ls`
continuum gap. Gap inputs needed: `m_a → m(Ls) > 0` (fixed-`Ls`, via
compact resolvent), NOT a thermodynamic uniform gap.

## 1. The precise statement to be discharged

pphi2's Layer-B2 axiom
(`Pphi2/AsymTorus/AsymExpMomentDischarge.lean:190`,
`asymInteractingVariance_le_freeVariance_Lt_uniform`), paraphrased:

> ∃ `C > 0` (depending on `P, mass, Ls`) such that **for all** `Lt`, all
> `Nt, Ns, a` with `Nt·a = Lt` and `Ns·a = Ls`, and all test functions `f`,
> `Var_int(f) ≤ C · Var_free(f)`,
>
> where `Var_int(f) = ∫ (ω f)² dμ_int^{torus}` and
> `Var_free(f) = ∫ (ω g)² dμ_free^{lattice}`, `g = ι f`.

The single constant `C` must be uniform across **two coupled limits**:

- **IR / time:** `Lt = Nt·a → ∞` (more time slices), and
- **UV / continuum:** `a → 0`, with `Ns = Ls/a → ∞`,

at **fixed spatial extent `Ls`** and fixed `mass`.

## 2. pphi2's layer architecture (as currently built)

- **Layer B1** (`AsymVarianceBound.lean`,
  `asymInteractingVariance_le_freeVariance_torus`, **proved**): at **fixed
  `Lt`**, `∃ C(Lt, Ls)` with `Var_int ≤ C(Lt,Ls)·Var_free`, **uniform in
  `(Nt, Ns, a)`** (i.e. uniform in `a`). Proved via the density-transfer /
  Gaussian-4th-moment / Nelson exp-moment route (not via the transfer
  matrix).
- **Layer B2** (the axiom above): must upgrade B1 to a constant uniform in
  `Lt` as well — i.e. show `sup_{Lt} C(Lt, Ls) < ∞` (and the resulting
  constant is still `a`-uniform).
- **Spectral infrastructure available** (`AsymL2Operator`, `AsymJentzsch`,
  `AsymPositivity`): the spatial transfer operator `asymTransferOperatorCLM`
  is self-adjoint, compact, with a Perron–Frobenius ground state and a
  **per-`(Nt,Ns,a)` mass gap** `asymMassGap_pos`. Its docstring states the
  **uniformity of this gap as `a→0`, `Ns→∞` is NOT in scope** and "is Layer
  B2 (chessboard / FSS); the square's analogue `spectral_gap_uniform` is
  itself still an open axiom."

## 3. The two competing positions

### Position P (the PLAN's 2026-06-02 deep-think vet — "no chessboard")

`reflection-positivity/PLAN.md` records a deep-think vet asserting: the
`Lt`-uniform variance bound follows **directly from the cylinder
transfer-matrix mass gap via an operator-norm geometric-series argument**,
**without** Mathlib's WIP spectral theorem and **without chessboard
combinatorics** — because at fixed `a` the spatial transfer operator and
its gap `γ = e^{−mₐa}` are fixed, so `Σ_{t<Nt} γ^t ≤ 1/(1−γ)` is bounded
**independent of `Nt` (hence `Lt`)**. (This is exactly the abstract
`GappedTransfer.susceptibility_le` now proved in reflection-positivity.)

### Position G (Gemini 2.5-pro, literature-grounded — "chessboard required")

Asked what published P(φ)₂ constructions do, Gemini 2.5-pro answered (with
citations):

- The construction is **factored, not monolithic**: continuum (`a→0`) at
  fixed volume via **Guerra–Rosen–Simon correlation inequalities** (GRS I,
  *Ann. Math.* 1975, Thm 2.1 — they add an auxiliary `½σφ²` to restore
  ferromagneticity broken by the `−6cφ²` Wick term, giving
  `⟨φ(f)²⟩_int ≤ ⟨φ(f)²⟩_free`-type bounds uniform in `a` at fixed volume);
  time-volume (`Lt→∞`) at fixed `a` via the transfer-matrix mass gap /
  Källén–Lehmann (Glimm–Jaffe Ch. 6, 19).
- **Brascamp–Lieb** does not apply (`V'' = 12λφ² − 12λc < 0` for small `φ`,
  worsening as `c→∞`); **Nelson hypercontractivity** is for establishing
  the mass gap (Simon "P(φ)₂" Ch. VIII), not the variance bound.
- **Bottom line (G's strong claim):** combining the two steps **requires
  the mass gap uniform in `a`** (`inf_a mₐ > 0`) — the FSS chessboard /
  Glimm–Jaffe–Spencer (*Ann. Math.* 1975) result. G asserts there is **no**
  published route to the joint uniformity using only a per-`a` gap, and
  **none** monolithically from correlation inequalities. A per-`a` gap
  vanishing as `a→0` would make `C` diverge.

## 4. The proposed reconciliation (to be vetted)

P and G may both be correct because they concern **different regimes**,
and the distinguishing feature is whether `Ls` is fixed:

- G's "uniform-in-`a` gap is hard (chessboard)" is the statement for the
  **thermodynamic** limit (`Ls → ∞` as well). There, `inf_a mₐ > 0` uniform
  in both `a` and `Ls` is genuinely the FSS/GJS input.
- pphi2's cylinder **fixes `Ls`**. As `a→0` the spatial direction is a
  *fixed finite physical interval* `[0, Ls]` discretized more finely, with
  `Ns = Ls/a` sites. The spatial transfer operator's gap should then
  converge to the **continuum fixed-`Ls` gap** — a fixed positive number —
  so it is plausibly uniform in `a` **without** the thermodynamic FSS
  estimate. On this reading, the chessboard is needed only for `Ls→∞`, not
  for fixed-`Ls`, `a→0`, and Position P's "no chessboard" claim holds
  **because `Ls` is fixed**.

## 5. The sharp question(s) for the vetter

1. At **fixed `Ls`**, does the lattice spatial transfer-matrix mass gap
   `mₐ` (equivalently `γ = e^{−mₐa}` bounded away from 1) admit a lower
   bound **uniform in `a` as `a→0`** — i.e. does it converge to a positive
   continuum fixed-`Ls` gap — *without* invoking the
   Fröhlich–Simon–Spencer / Glimm–Jaffe–Spencer thermodynamic uniform-gap
   estimate? (If yes, Position P is correct and pphi2's B2 avoids
   chessboard; if the argument secretly needs `Ls→∞` control, Position G
   is correct and a uniform gap is required.)

2. Independently: in combining B1 (`C(Lt,Ls)` `a`-uniform at fixed `Lt`)
   with the `Lt→∞` control, does the mechanism bounding `sup_{Lt} C(Lt,Ls)`
   reintroduce `a`-dependence? Concretely, is `sup_{Lt} C(Lt,Ls)` finite
   **and** `a`-uniform using only the **per-`a`** gap, or does its
   finiteness require `inf_a mₐ > 0`?

3. Is there a published P(φ)₂ construction (or a clean argument) that, at
   **fixed `Ls`**, obtains the joint `(Lt, a)`-uniform variance bound from
   (i) GRS/hypercontractivity for the `a`-direction at fixed `Lt` plus
   (ii) the transfer-matrix gap for the `Lt`-direction, **without** a
   thermodynamic uniform-in-`a` gap? Or does the fixed-`Ls` continuum gap
   itself require nontrivial input?

## 6. What is already formalized (context for the vetter)

- `reflection-positivity` (Lean/Mathlib v4.30.0): the abstract operator
  core is proved sorry-free — `GappedTransfer` (self-adjoint contraction
  with vacuum and an operator-norm gap `‖T|_{Ω^⊥}‖ ≤ γ < 1`) and
  `GappedTransfer.susceptibility_le`:
  `∑_{n<N} |⟪v, Tⁿ v⟫| ≤ ‖v‖²/(1−γ)`, **uniform in `N`** (the `Lt`
  direction). This realizes Position P's geometric-series step abstractly.
- `pphi2` (`AsymGappedTransfer.lean`, commit 53499d5): packages
  `asymTransferOperatorCLM` as a `GappedTransfer`, taking the operator-norm
  gap `hnorm` as a hypothesis. Note: pphi2's `asymMassGap` is the gap to an
  **arbitrary** excited eigenvalue (`eigenval i₁ < eigenval i₀`), **not**
  the supremum of the non-ground spectrum; the operator-norm gap `hnorm`
  needs the latter (a true spectral gap), which is a separate spectral
  lemma regardless of the `a`-uniformity question above.

The crux for the whole B2 discharge is whether `γ` (per-`a`, hence the
constant `1/(1−γ)`) can be taken `a`-uniform at fixed `Ls` — question (1).
