# Transfer-operator / Feynman–Kac correlation bridge — implementation spec

Maximum-generality formulation (route II, OS/GNS). Implementation-ready signatures,
grounded in the actual declarations in this repo (2026-06-03). New file:
`ReflectionPositivity/TransferConstruction.lean` (imports `PhysicalHilbertSpace`,
`TransferMatrix`, `VarianceBound`).

## Existing decls this builds on (verbatim)

```lean
-- Abstract.lean
def reflectionInnerProduct (μ : Measure Ω) (θ : Ω → Ω) (F G : Ω → ℝ) : ℝ   -- = ∫ F·(G∘θ) dμ
theorem reflectionInnerProduct_comp_left {μ θ τ}
    (hθ : MeasurePreserving θ μ μ) (hτ : MeasurePreserving τ μ μ)
    (hcomm : ∀ x, τ (θ (τ x)) = θ x) {F G} (hF …) (hG …) :
    reflectionInnerProduct μ θ (F ∘ τ) G = reflectionInnerProduct μ θ F (G ∘ τ)

-- PhysicalHilbertSpace.lean
structure ReflectionSystem (Ω) [m0 : MeasurableSpace Ω] where
  μ : Measure Ω;  θ : Ω → Ω;  mp : MeasurePreserving θ μ μ;  inv : Function.Involutive θ
  mPos : MeasurableSpace Ω;  le : mPos ≤ m0;  rp : @IsReflectionPositive Ω m0 μ θ mPos
def  S.PosObs : Type _ := ↥(lpMeas ℝ ℝ S.mPos 2 S.μ)            -- pre-Hilbert carrier
def  S.PosObs.toLp (f) : Lp ℝ 2 S.μ
instance S.instPreCore : PreInnerProductSpace.Core ℝ S.PosObs    -- inner = reflectionInnerProduct
abbrev S.physicalHilbertSpace : Type _ := UniformSpace.Completion S.PosObs  -- has IPS+Complete

-- TransferMatrix.lean
structure GappedTransfer (H) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  T : H →L[ℝ] H;  vacuum : H;  selfAdjoint : ∀ x y, ⟪T x,y⟫ = ⟪x,T y⟫
  vacuum_eq : T vacuum = vacuum;  gap : ℝ;  gap_nonneg;  gap_lt_one
  norm_le_of_orthogonal : ∀ v, ⟪vacuum,v⟫ = 0 → ‖T v‖ ≤ gap*‖v‖
-- VarianceBound.lean
theorem GappedTransfer.susceptibility_le {v} (hv : ⟪G.vacuum,v⟫=0) (N : ℕ) :
    ∑ n ∈ Finset.range N, |⟪v,(G.T^n) v⟫| ≤ ‖v‖^2/(1-G.gap)
```

## Deliverable 0 — the data: `TimeTranslatedSystem`

```lean
/-- A reflection system with a compatible Euclidean time translation `τ`. -/
structure TimeTranslatedSystem (Ω) [m0 : MeasurableSpace Ω] extends ReflectionSystem Ω where
  τ      : Ω → Ω
  τmp    : MeasurePreserving τ μ μ
  τθ     : ∀ x, τ (θ (τ x)) = θ x                         -- θτθ = τ⁻¹  (self-adjointness)
  τPos   : ∀ f, AEStronglyMeasurable[mPos] f μ → AEStronglyMeasurable[mPos] (f ∘ τ) μ
  -- a-priori contraction (FREE in concrete instances; the one non-mechanical field):
  contraction : ∀ f : PosObs toReflectionSystem,
      reflectionInnerProduct μ θ (f.toLp ∘ τ) (f.toLp ∘ τ)
        ≤ reflectionInnerProduct μ θ f.toLp f.toLp
```

## Deliverable 1 — the transfer operator (gap-free core)

```lean
/-- Pre-completion transfer map `Tpre [f] = [f ∘ τ]` on `PosObs`; 1-Lipschitz by
    `contraction`, linear by precomposition. -/
noncomputable def S.transferOperatorPre : S.PosObs →L[ℝ] S.PosObs

/-- The transfer operator on `H_phys`, = `Completion.map` of `Tpre`; `‖T‖ ≤ 1`. -/
noncomputable def S.transferOperator : S.physicalHilbertSpace →L[ℝ] S.physicalHilbertSpace

/-- `T [f] = [f ∘ τ]` on the dense subspace (the defining property). -/
theorem S.transferOperator_coe (f : S.PosObs) :
    S.transferOperator ((f : S.PosObs) : S.physicalHilbertSpace)
      = ((⟨f.toLp ∘ τ, …⟩ : S.PosObs) : S.physicalHilbertSpace)

/-- Self-adjoint (from `reflectionInnerProduct_comp_left` + density). -/
theorem S.transferOperator_selfAdjoint (x y) : ⟪S.transferOperator x, y⟫ = ⟪x, S.transferOperator y⟫

/-- The vacuum `[1]` (class of the constant `1`); `T`-invariant since `1 ∘ τ = 1`. -/
noncomputable def S.vacuum : S.physicalHilbertSpace
theorem S.transferOperator_vacuum : S.transferOperator S.vacuum = S.vacuum
```

Construction = the 6-step plan in `RECON.md` (`Tpre` → `Completion.map` → self-adjoint
by density → vacuum). **No gap proved here.**

## Deliverable 2 — the correlation identity (THE bridge; gap-free, near-definitional)

```lean
/-- Euclidean-time correlation = physical inner product of `T`-powers.
    By induction on `n` from `transferOperator_coe` + `reflectionInnerProduct_comp_left`. -/
theorem S.reflectionCorrelation_eq_inner_T_pow (f g : S.PosObs) (n : ℕ) :
    ⟪((f : S.PosObs) : S.physicalHilbertSpace),
       (S.transferOperator ^ n) ((g : S.PosObs) : S.physicalHilbertSpace)⟫
      = reflectionInnerProduct S.μ S.θ f.toLp (g.toLp ∘ S.τ^[n])
```

This is the whole content of "Feynman–Kac" in the abstract setting — no Fubini, no
trace formula. (Base case `n=0` = `instPreCore`; step = `transferOperator_coe` +
`comp_left` with `τ^[n]` measure-preserving and `τPos` for membership.)

## Deliverable 3 — the abstract B2 variance bound (adds the gap)

```lean
/-- Given a gap on `T` (a `GappedTransfer` with `.T = transferOperator`, `.vacuum =
    vacuum`), a time-smeared second moment is bounded uniformly in the time extent.
    `v : PosObs` the (vacuum-orthogonal) field-excited vector, `h̃ : ℤ → ℝ` finitely
    supported time profile. -/
theorem S.varianceTimeSum_le
    (G : GappedTransfer S.physicalHilbertSpace)
    (hGT : G.T = S.transferOperator) (hGvac : G.vacuum = S.vacuum)
    {v : S.PosObs} (hv : ⟪G.vacuum, (v : S.physicalHilbertSpace)⟫ = 0)
    (h̃ : ℤ → ℝ) (hsupp : h̃.support.Finite) :
    ∑ t ∈ hsupp.toFinset, ∑ t' ∈ hsupp.toFinset,
        h̃ t * h̃ t' * reflectionInnerProduct S.μ S.θ v.toLp (v.toLp ∘ S.τ^[|t-t'|.toNat])
      ≤ (∑ t ∈ hsupp.toFinset, |h̃ t|)^2 * ‖(v : S.physicalHilbertSpace)‖^2 / (1 - G.gap)
```

Proof: rewrite each correlation via Deliverable 2 to `⟪v, T^{|t−t'|} v⟫`, bound the
double sum by `(∑|h̃|)·∑_d |⟪v,T^d v⟫|`, then `susceptibility_le`. **Constant has no
time-extent dependence ⟹ `Lt`-uniform.**

## Dependency DAG / status

```
ReflectionSystem, PosObs, H_phys, instPreCore .......... PROVED (PhysicalHilbertSpace.lean)
reflectionInnerProduct_comp_left ....................... PROVED (Abstract.lean)
GappedTransfer, susceptibility_le ...................... PROVED (TransferMatrix/VarianceBound)
  │
  ├─ D0  TimeTranslatedSystem (structure) ............... TODO (mechanical; `contraction` a field)
  ├─ D1  transferOperator + selfAdjoint + vacuum ........ TODO (6-step plan; Completion API)
  ├─ D2  reflectionCorrelation_eq_inner_T_pow .......... TODO (induction; the "bridge")
  └─ D3  varianceTimeSum_le ............................. TODO (D2 + susceptibility_le)
```

The only non-mechanical input is `D0.contraction` (a-priori boundedness) — taken as a
structure field, discharged for free in every concrete instance.

## pphi2 instantiation interface (the only φ⁴₂-specific work)

1. `Pphi2TimeTranslatedSystem : TimeTranslatedSystem (Configuration (AsymLatticeField Nt Ns))`
   — `μ = interactingLatticeMeasureAsym`, `θ` = time reflection, `τ` = time shift, `rp`
   from the proved lattice RP, `contraction` from Gaussian/finite boundedness (free).
2. **Operator-coincidence lemma** (where the Codex lattice review's covariance work lands):
   `transferOperator` on `H_phys` ≅ `asymTransferOperatorCLM` on `L2SpatialField Ns`
   (a unitary identifying `H_phys` with the spatial `L²`, intertwining the two operators).
   Supplies a `GappedTransfer` with `.T = transferOperator` and the PROVED gap
   (`asymGappedTransfer'`), satisfying D3's `hGT`/`hGvac`.
3. Apply `varianceTimeSum_le`; identify the RHS with `C · Var_free` (free covariance,
   `1/a` cancellation per `[[pphi2-b2-adapter-plan]]`); B1 supplies `a`-uniformity.

## Open spec questions (resolve during D1/instantiation)

- `vacuum = [1]`: needs `1 ∈ PosObs` (the constant is `mPos`-measurable, `L²` on a
  probability measure). Confirm `μ` is a probability measure in the instance (it is:
  `interactingLatticeMeasureAsym_isProbability`).
- The unitary `H_phys ≅ L2SpatialField Ns` (instantiation step 2) is the substantive
  φ⁴₂ lemma — its proof is the lattice action-factorization (the route-I "step 2/3").
  This is where to point Codex's findings.
- Time-profile sign/`ℤ`-vs-`ZMod Nt` bookkeeping in D3 (cylinder periodicity).
