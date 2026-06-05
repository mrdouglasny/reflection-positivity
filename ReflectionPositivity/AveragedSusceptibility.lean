/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Averaged-susceptibility geometric engine (Layer-B4)

The geometric-series core of the finite-volume Källén–Lehmann bound. On a periodic time torus
of extent `Nt`, the connected two-point function at separation `d` is, in the transfer-operator
eigenbasis, `Σ_k b_k (γ_k^d + γ_k^{Nt-d})` (`b_k = |⟨Ω|Φ|e_k⟩|²`, `γ_k = λ_k/λ₀`), the second
term being the periodic wrap-around. Summing over `d` and using the spectral gap `γ_k ≤ γ < 1`
gives a bound **independent of `Nt`** — the `(1+γ)/(1-γ)` constant from Gemini's design
(`pphi2/docs/B4B5-design.md`).

This file proves the pure geometric/summation content (no operator theory): the wrap-around sum
bound and its `b`-weighted (per-mode) version. The spectral identification of the trace-ratio
correlators with this form is the companion B5a step.

## Main results

* `geom_wrap_sum_le` — `Σ_{d<Nt} (r^d + r^{Nt-d}) ≤ (1+r)/(1-r)` for `0 ≤ r < 1`.
* `averaged_susceptibility_bound` — the `b`-weighted version with a uniform gap `γ`.
-/

open scoped BigOperators

namespace ReflectionPositivity

/-- A finite geometric sum is bounded by the infinite one. -/
private theorem sum_range_pow_le_inv (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ d ∈ Finset.range n, r ^ d ≤ (1 - r)⁻¹ := by
  have hsum := summable_geometric_of_lt_one hr0 hr1
  calc ∑ d ∈ Finset.range n, r ^ d
      ≤ ∑' d : ℕ, r ^ d :=
        Summable.sum_le_tsum _ (fun i _ => pow_nonneg hr0 i) hsum
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1

/-- **Periodic wrap-around geometric bound.** The `Nt`-uniform bound at the heart of the
averaged susceptibility: the forward (`r^d`) and wrap-around (`r^{Nt-d}`) geometric series
together sum to at most `(1+r)/(1-r)`. -/
theorem geom_wrap_sum_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (Nt : ℕ) :
    ∑ d ∈ Finset.range Nt, (r ^ d + r ^ (Nt - d)) ≤ (1 + r) / (1 - r) := by
  have hpos : 0 < 1 - r := by linarith
  rw [Finset.sum_add_distrib]
  -- forward series
  have h1 : ∑ d ∈ Finset.range Nt, r ^ d ≤ (1 - r)⁻¹ := sum_range_pow_le_inv r hr0 hr1 Nt
  -- wrap-around series: reindex `Nt - d = (Nt-1-d)+1`, then it is `r · Σ r^d`
  have h2 : ∑ d ∈ Finset.range Nt, r ^ (Nt - d) ≤ r * (1 - r)⁻¹ := by
    have hreflect : ∑ d ∈ Finset.range Nt, r ^ (Nt - d) =
        ∑ d ∈ Finset.range Nt, r ^ (d + 1) := by
      rw [← Finset.sum_range_reflect (fun d => r ^ (d + 1)) Nt]
      refine Finset.sum_congr rfl (fun d hd => ?_)
      have hd' : d < Nt := Finset.mem_range.mp hd
      congr 1
      omega
    rw [hreflect]
    have : ∑ d ∈ Finset.range Nt, r ^ (d + 1) = r * ∑ d ∈ Finset.range Nt, r ^ d := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun d _ => by rw [pow_succ, mul_comm])
    rw [this]
    exact mul_le_mul_of_nonneg_left (sum_range_pow_le_inv r hr0 hr1 Nt) hr0
  calc (∑ d ∈ Finset.range Nt, r ^ d) + ∑ d ∈ Finset.range Nt, r ^ (Nt - d)
      ≤ (1 - r)⁻¹ + r * (1 - r)⁻¹ := add_le_add h1 h2
    _ = (1 + r) / (1 - r) := by rw [div_eq_mul_inv]; ring

/-- `(1+x)/(1-x)` is monotone on `[0,1)`. -/
private theorem one_add_div_one_sub_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    (1 + x) / (1 - x) ≤ (1 + y) / (1 - y) := by
  have hx1 : 0 < 1 - x := by linarith
  have hy1 : 0 < 1 - y := by linarith
  have e : ∀ z : ℝ, z < 1 → (1 + z) / (1 - z) = 2 / (1 - z) - 1 := by
    intro z hz
    have hz' : (1 : ℝ) - z ≠ 0 := by linarith
    field_simp
    ring
  rw [e x (by linarith), e y hy]
  have hden : 1 - y ≤ 1 - x := by linarith
  have hmono : 2 / (1 - x) ≤ 2 / (1 - y) := by gcongr
  linarith

/-- **Averaged-susceptibility bound (B4 engine).** A nonnegative-weighted sum of per-mode
wrap-around geometric series, with all rates bounded by the gap `γ`, is bounded by
`((1+γ)/(1-γ))·Σ b` — uniformly in the time extent `Nt`. With `b_k = |⟨Ω|Φ|e_k⟩|²` and
`gam_k = λ_k/λ₀`, the left side is `Σ_d` (connected two-point at separation `d`) and the bound
is the `Nt`-uniform averaged susceptibility. -/
theorem averaged_susceptibility_bound (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (Nt : ℕ)
    {ι : Type*} (s : Finset ι) (b gam : ι → ℝ) (hb : ∀ k ∈ s, 0 ≤ b k)
    (hgam : ∀ k ∈ s, 0 ≤ gam k ∧ gam k ≤ γ) :
    ∑ d ∈ Finset.range Nt, ∑ k ∈ s, b k * (gam k ^ d + gam k ^ (Nt - d)) ≤
      (1 + γ) / (1 - γ) * ∑ k ∈ s, b k := by
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun k hk => ?_)
  obtain ⟨hgk0, hgkγ⟩ := hgam k hk
  have hgk1 : gam k < 1 := lt_of_le_of_lt hgkγ hγ1
  rw [← Finset.mul_sum, mul_comm ((1 + γ) / (1 - γ)) (b k)]
  refine mul_le_mul_of_nonneg_left ?_ (hb k hk)
  calc ∑ d ∈ Finset.range Nt, (gam k ^ d + gam k ^ (Nt - d))
      ≤ (1 + gam k) / (1 - gam k) := geom_wrap_sum_le (gam k) hgk0 hgk1 Nt
    _ ≤ (1 + γ) / (1 - γ) := one_add_div_one_sub_mono hgk0 hgkγ hγ1

end ReflectionPositivity
