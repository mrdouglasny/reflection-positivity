/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.TransferMatrix
import ReflectionPositivity.VarianceBound

/-!
# Connected two-point bound from the spectral gap (rank-1 projection)

The operator core of the spectral identification (Layer-B4). For a `GappedTransfer` (normalized
transfer operator `T` with vacuum `Ω`, `TΩ=Ω`, and gap `‖Tv‖≤γ‖v‖` on `Ω^⊥`) and self-adjoint
observable operators `M_A, M_B`, the **connected** vacuum two-point at time separation `d`,
`⟪Ω, M_A Tᵈ M_B Ω⟫ − ⟪Ω,M_A Ω⟫⟪Ω,M_B Ω⟫`, decays like `γᵈ`:
```
|connected_d| ≤ γᵈ · ‖P₁ M_A Ω‖ · ‖P₁ M_B Ω‖,   P₁ = I − |Ω⟩⟨Ω|.
```
This uses only the rank-1 ground projection `P₁` and the existing iterated-contraction bound
`norm_T_pow_le` — **no eigenbasis / spectral theorem** (see `pphi2/docs/B4B5-design.md`, route
correction). It is the per-separation input that `geom_wrap_sum_le` /
`averaged_susceptibility_bound` sum into the `Nt`-uniform susceptibility bound.
-/

open scoped RealInnerProductSpace

namespace ReflectionPositivity

namespace GappedTransfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (G : GappedTransfer H)

/-- The vacuum-orthogonal projection `P₁ v = v − ⟪Ω,v⟫ Ω` (orthogonal when `‖Ω‖=1`). -/
def vacuumPerp (v : H) : H := v - ⟪G.vacuum, v⟫ • G.vacuum

/-- Iterates fix the vacuum: `Tᵈ Ω = Ω`. -/
theorem T_pow_vacuum (d : ℕ) : (G.T ^ d) G.vacuum = G.vacuum := by
  induction d with
  | zero => simp
  | succ n ih => rw [pow_succ', ContinuousLinearMap.mul_apply, ih, G.vacuum_eq]

/-- `P₁ v` is vacuum-orthogonal (needs `‖Ω‖=1`). -/
theorem inner_vacuum_vacuumPerp (hΩ : ‖G.vacuum‖ = 1) (v : H) :
    ⟪G.vacuum, G.vacuumPerp v⟫ = 0 := by
  simp only [vacuumPerp, inner_sub_right, inner_smul_right]
  have h : ⟪G.vacuum, G.vacuum⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hΩ]; norm_num
  rw [h]; ring

/-- Reconstruction `v = ⟪Ω,v⟫ Ω + P₁ v`. -/
theorem vacuum_add_vacuumPerp (v : H) :
    ⟪G.vacuum, v⟫ • G.vacuum + G.vacuumPerp v = v := by
  simp only [vacuumPerp]; abel

/-- **Two-point split.** The raw vacuum two-point splits into the disconnected product plus the
connected part `⟪P₁ M_A Ω, Tᵈ (P₁ M_B Ω)⟫` (the genuinely `d`-dependent part). -/
theorem two_point_split (hΩ : ‖G.vacuum‖ = 1)
    (MA MB : H →L[ℝ] H) (hMA : ∀ x y, ⟪MA x, y⟫ = ⟪x, MA y⟫) (d : ℕ) :
    ⟪G.vacuum, MA ((G.T ^ d) (MB G.vacuum))⟫
      = ⟪G.vacuum, MA G.vacuum⟫ * ⟪G.vacuum, MB G.vacuum⟫
        + ⟪G.vacuumPerp (MA G.vacuum), (G.T ^ d) (G.vacuumPerp (MB G.vacuum))⟫ := by
  have hwperp : ⟪G.vacuum, (G.T ^ d) (G.vacuumPerp (MB G.vacuum))⟫ = 0 :=
    G.inner_vacuum_T_pow_eq_zero (G.inner_vacuum_vacuumPerp hΩ (MB G.vacuum)) d
  have h1 : ⟪MA G.vacuum, (G.T ^ d) (G.vacuumPerp (MB G.vacuum))⟫
      = ⟪G.vacuumPerp (MA G.vacuum), (G.T ^ d) (G.vacuumPerp (MB G.vacuum))⟫ := by
    conv_lhs => rw [← G.vacuum_add_vacuumPerp (MA G.vacuum)]
    rw [inner_add_left, real_inner_smul_left, hwperp]; simp
  rw [← hMA G.vacuum ((G.T ^ d) (MB G.vacuum))]
  conv_lhs => rw [← G.vacuum_add_vacuumPerp (MB G.vacuum)]
  rw [map_add, map_smul, G.T_pow_vacuum d, inner_add_right, real_inner_smul_right, h1,
    real_inner_comm (MA G.vacuum) G.vacuum]
  ring

/-- **Connected two-point bound.** The connected vacuum two-point at separation `d` decays like
`γᵈ` times the product of the vacuum-orthogonal observable norms. -/
theorem connected_two_point_le (hΩ : ‖G.vacuum‖ = 1)
    (MA MB : H →L[ℝ] H) (hMA : ∀ x y, ⟪MA x, y⟫ = ⟪x, MA y⟫) (d : ℕ) :
    |⟪G.vacuum, MA ((G.T ^ d) (MB G.vacuum))⟫
        - ⟪G.vacuum, MA G.vacuum⟫ * ⟪G.vacuum, MB G.vacuum⟫|
      ≤ G.gap ^ d * (‖G.vacuumPerp (MA G.vacuum)‖ * ‖G.vacuumPerp (MB G.vacuum)‖) := by
  rw [G.two_point_split hΩ MA MB hMA d, add_sub_cancel_left]
  calc |⟪G.vacuumPerp (MA G.vacuum), (G.T ^ d) (G.vacuumPerp (MB G.vacuum))⟫|
      ≤ ‖G.vacuumPerp (MA G.vacuum)‖ * ‖(G.T ^ d) (G.vacuumPerp (MB G.vacuum))‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖G.vacuumPerp (MA G.vacuum)‖ * (G.gap ^ d * ‖G.vacuumPerp (MB G.vacuum)‖) :=
        mul_le_mul_of_nonneg_left
          (G.norm_T_pow_le (G.inner_vacuum_vacuumPerp hΩ (MB G.vacuum)) d) (norm_nonneg _)
    _ = G.gap ^ d * (‖G.vacuumPerp (MA G.vacuum)‖ * ‖G.vacuumPerp (MB G.vacuum)‖) := by ring

/-- **Observable susceptibility bound.** Summing the connected two-point of a self-adjoint
observable `Φ` over all separations is bounded by `‖P₁ Φ Ω‖²/(1-γ)` — the variance bound from the
gap, in observable form. (Stitches `two_point_split` with the proved `susceptibility_le`.) -/
theorem connected_susceptibility_le (hΩ : ‖G.vacuum‖ = 1)
    (Φ : H →L[ℝ] H) (hΦ : ∀ x y, ⟪Φ x, y⟫ = ⟪x, Φ y⟫) (N : ℕ) :
    ∑ d ∈ Finset.range N,
        |⟪G.vacuum, Φ ((G.T ^ d) (Φ G.vacuum))⟫ - ⟪G.vacuum, Φ G.vacuum⟫ ^ 2|
      ≤ ‖G.vacuumPerp (Φ G.vacuum)‖ ^ 2 / (1 - G.gap) := by
  have hv : ⟪G.vacuum, G.vacuumPerp (Φ G.vacuum)⟫ = 0 :=
    G.inner_vacuum_vacuumPerp hΩ (Φ G.vacuum)
  have hterm : ∀ d, ⟪G.vacuum, Φ ((G.T ^ d) (Φ G.vacuum))⟫ - ⟪G.vacuum, Φ G.vacuum⟫ ^ 2
      = ⟪G.vacuumPerp (Φ G.vacuum), (G.T ^ d) (G.vacuumPerp (Φ G.vacuum))⟫ := by
    intro d; rw [G.two_point_split hΩ Φ Φ hΦ d, sq]; ring
  calc ∑ d ∈ Finset.range N,
        |⟪G.vacuum, Φ ((G.T ^ d) (Φ G.vacuum))⟫ - ⟪G.vacuum, Φ G.vacuum⟫ ^ 2|
      = ∑ d ∈ Finset.range N,
          |⟪G.vacuumPerp (Φ G.vacuum), (G.T ^ d) (G.vacuumPerp (Φ G.vacuum))⟫| := by
        exact Finset.sum_congr rfl (fun d _ => by rw [hterm d])
    _ ≤ ‖G.vacuumPerp (Φ G.vacuum)‖ ^ 2 / (1 - G.gap) := G.susceptibility_le hv N

end GappedTransfer

end ReflectionPositivity
