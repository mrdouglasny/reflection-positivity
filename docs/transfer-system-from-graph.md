# Future work: `LatticeTransferData → TransferSystem` (graph + measure → transfer matrix)

A proposed general constructor turning a **time-layered lattice graph + local energy** into
the proved transfer-matrix machinery of this repo, so a concrete lattice is supplied by
filling a small *local* record, with reflection positivity **derived** rather than
re-proved per instance. **Status: future work / not built.** The concrete asymmetric-φ⁴₂
cylinder instance is being assembled by hand now (`TransferSystem.lean` consumer in
`pphi2`); this records the abstraction to lift up afterward. Corpus-wide context:
[`planning` proposal](../../planning/plans/proposals/transfer-system-from-graph.md).

## What already exists here (the abstract consumers)

- `TransferSystem` (`ReflectionPositivity/TransferSystem.lean`) — the **kernel-iterate
  Feynman–Kac dictionary**: symmetric nonnegative kernel `k` on `(S, ν)` ⟹ periodic path
  measure on `ZMod n → S`, with `partition_eq_trace` and `twoPoint_dictionary` proved
  (forward direction; pure Fubini; no RP).
- `ReflectionSystem` / `TimeTranslatedSystem` / `transferOperator`
  (`PhysicalHilbertSpace.lean`, `TransferConstruction.lean`) — the **OS/GNS reconstruction**
  (RP measure + time translation ⟹ physical Hilbert space + self-adjoint transfer operator);
  this is where RP is genuinely used. See [`transfer-construction.md`](transfer-construction.md).

The missing piece is the generic `(graph + energy) ↦ structure` constructor — currently
each lattice is instantiated by hand.

## Scope: OS / transfer matrix only

A transfer matrix needs a distinguished time direction = a **ℤ- (or ℤ_n-) action by a graph
automorphism** (the time shift `τ`) + a **reflection** automorphism `θ` with `θτθ=τ⁻¹`, and
`τ`-invariance of the measure. RP is what makes the reconstructed operator positive +
self-adjoint (`e^{−aH}`, `H≥0`, spectral gap). The FLS reconstruction (graph *parameter* +
PSD connection matrices ⟹ finite weighted graph) is a different theorem — no time direction,
no transfer matrix — and is out of scope here.

## Required input: a time-layered lattice graph + local energy

`V = (time) × V_space`: spatial vertices `V_space` (one slice), intra-slice + inter-slice
(time) edges; a time-shift automorphism `τ : (t,s)↦(t+1,s)` and a time-reflection
automorphism `θ : (t,s)↦(−t,s)` with `shift∘refl∘shift = refl`; and a local energy
(`sliceEnergy`, symmetric `timeBondEnergy`).

## Proposed record + constructors

```lean
structure LatticeTransferData where
  Vspace : Type*
  [instFintype : Fintype Vspace]
  sliceEnergy    : (Vspace → ℝ) → ℝ
  timeBondEnergy : (Vspace → ℝ) → (Vspace → ℝ) → ℝ
  timeBond_symm  : ∀ x y, timeBondEnergy x y = timeBondEnergy y x   -- ⟹ k_symm / self-adjoint
  -- RP-type hypotheses on timeBondEnergy (below) + integrability/σ-finiteness

-- k x y = exp(−timeBondEnergy x y − ½ sliceEnergy x − ½ sliceEnergy y) = w x · G x y · w y
def LatticeTransferData.toTransferSystem      : LatticeTransferData → TransferSystem (Vspace → ℝ)
def LatticeTransferData.toReflectionSystem    : … → ReflectionSystem (Configuration …)
def LatticeTransferData.toTimeTranslatedSystem : … → TimeTranslatedSystem (Configuration …)
```

`w(x) = exp(−½ sliceEnergy x) > 0` ⟹ `k_nonneg`; `G` symmetric ⟹ `k_symm`. The B2 obligation
(*global Gibbs measure = `pathMeasure` of `k`*) becomes a generic energy-factorization lemma
(`global energy = Σ_t [timeBond(ψ_t,ψ_{t+1}) + sliceEnergy ψ_t]`).

## RP as a *derived* theorem (the payoff)

The `rp` field of `ReflectionSystem` should follow from local hypotheses, not a per-instance
proof. Sufficient conditions (Glimm–Jaffe Ch. 6.1; Osterwalder–Seiler):
1. reflection cuts the graph across a time-zero hyperplane with crossing (time) bonds mapped
   symmetrically;
2. time-bond couplings are reflection-positive type (e.g. nearest-neighbour `−(φ−φ')²`);
3. the on-site/slice measure is even.
Then `V₊+V₀+V₋` factorization + Gaussian-with-boundary-weight gives `rp`. Bundling (1)–(3) as
fields ⟹ `toReflectionSystem` produces `rp` as a lemma. (pphi2's hand-proved
`OSProofs.lattice_rp` is the prototype to generalize.)

## Why later, not now

Building it now would detour the live work (discharging pphi2's
`asymInteractingVariance_le_freeVariance_Lt_uniform` via the hand-built asym-cylinder
instance). Once that lands and the square torus / general spin lattices / the continuum
limit want to reuse it, this is the abstraction to lift. Vetting (Gemini/Codex) TODO before
building.

## References

- Glimm–Jaffe, *Quantum Physics* 2nd ed., Ch. 6.1.
- K. Osterwalder, E. Seiler, *Gauge field theories on a lattice*, Ann. Phys. 110 (1978).
- M. Freedman, L. Lovász, A. Schrijver, JAMS 20 (2007) — the different (FLS) reconstruction.
