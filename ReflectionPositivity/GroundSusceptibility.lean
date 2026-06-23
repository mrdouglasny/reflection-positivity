/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.GroundBridge
import ReflectionPositivity.AveragedSusceptibility

/-!
# Finite-periodic connected susceptibility bound

Piece F of `docs/gns-construction-plan.md`.

This file sums the finite-periodic connected two-point bridge from
`GroundBridge.lean`. The bridge theorem is stated for positive time
representatives `0 < t.val`, so the unconditional theorem below sums over the
positive representatives. A companion all-representatives theorem is provided
with an explicit zero-time hypothesis.
-/

open scoped BigOperators

namespace ReflectionPositivity

variable {S : Type*} [MeasurableSpace S]

private theorem geom_wrap_sum_le_two (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (Nt : ℕ) :
    ∑ d ∈ Finset.range Nt, (γ ^ d + γ ^ (Nt - d)) ≤ 2 / (1 - γ) := by
  have hgeom := geom_wrap_sum_le γ hγ0 hγ1 Nt
  have hden_pos : 0 < 1 - γ := by linarith
  have htwo : (1 + γ) / (1 - γ) ≤ 2 / (1 - γ) := by
    gcongr
    linarith
  exact le_trans hgeom htwo

private theorem sum_range_const_le_of_filter {c : ℝ} (hc : 0 ≤ c)
    (Nt : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ∑ _d ∈ (Finset.range Nt).filter p, c ≤ (Nt : ℝ) * c := by
  have hsubset : (Finset.range Nt).filter p ⊆ Finset.range Nt :=
    Finset.filter_subset _ _
  have hle : ∑ d ∈ (Finset.range Nt).filter p, c ≤ ∑ d ∈ Finset.range Nt, c :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => hc)
  simpa [Finset.sum_const, nsmul_eq_mul] using hle

private theorem sum_zmod_eq_sum_range (Nt : ℕ) [NeZero Nt] (f : ZMod Nt → ℝ) :
    ∑ t : ZMod Nt, f t = ∑ d ∈ Finset.range Nt, f (d : ZMod Nt) := by
  refine Finset.sum_bij (fun t _ => t.val) ?mem ?inj ?surj ?eq
  · intro t _
    exact Finset.mem_range.mpr (ZMod.val_lt t)
  · intro a _ b _ h
    exact ZMod.val_injective Nt h
  · intro d hd
    refine ⟨(d : ZMod Nt), Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hd)
  · intro t _
    have ht : ((t.val : ℕ) : ZMod Nt) = t := by
      simp [ZMod.natCast_val]
    simp [ht]

/-- **Positive-time finite-periodic connected susceptibility bound.**

This is the direct summation of
`pathConnectedTwoPoint_le_of_remainder` over the representatives where Piece E1
applies. The omitted zero representative is not controlled by the current E1
hypotheses. -/
theorem pathMeasure_connected_susceptibility_finite_periodic_bound_pos
    (Ts : TransferSystem S) (Ω : S → ℝ) (lambda0 γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (A B : MultiplicationCLMContract Ts.ν)
    (hRem : RemainderHypothesis Ts Ω lambda0 γ A B)
    (Nt : ℕ) [NeZero Nt] :
    ∑ d ∈ (Finset.range Nt).filter (fun d => 0 < d),
        |pathConnectedTwoPoint Ts A B Nt (d : ZMod Nt)|
      ≤ (‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖ *
          ‖hRem.G.vacuumPerp (B.M hRem.G.vacuum)‖) * (2 / (1 - γ))
        + hRem.C_rem * (Nt : ℝ) * γ ^ Nt := by
  set Cperp : ℝ :=
    ‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖ *
      ‖hRem.G.vacuumPerp (B.M hRem.G.vacuum)‖ with hCperp_def
  have hCperp_nonneg : 0 ≤ Cperp := by
    rw [hCperp_def]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hrem_nonneg : 0 ≤ hRem.C_rem * γ ^ Nt :=
    mul_nonneg hRem.C_rem_nonneg (pow_nonneg hγ0 _)
  have hterm :
      ∀ d ∈ (Finset.range Nt).filter (fun d => 0 < d),
        |pathConnectedTwoPoint Ts A B Nt (d : ZMod Nt)|
          ≤ Cperp * (γ ^ d + γ ^ (Nt - d)) + hRem.C_rem * γ ^ Nt := by
    intro d hd
    have hd_range : d < Nt := Finset.mem_range.mp (Finset.mem_filter.mp hd).1
    have hd_pos : 0 < d := (Finset.mem_filter.mp hd).2
    have hval : ((d : ZMod Nt).val) = d := ZMod.val_natCast_of_lt hd_range
    have h :=
      pathConnectedTwoPoint_le_of_remainder Ts Ω lambda0 γ A B hRem Nt (d : ZMod Nt)
        (by simpa [hval] using hd_pos)
        (by simpa [hval] using hd_range)
    simpa [finitePeriodicPerpEnvelope, hCperp_def, hval] using h
  have hgeom_filter :
      ∑ d ∈ (Finset.range Nt).filter (fun d => 0 < d),
          (γ ^ d + γ ^ (Nt - d))
        ≤ ∑ d ∈ Finset.range Nt, (γ ^ d + γ ^ (Nt - d)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun d _ _ => add_nonneg (pow_nonneg hγ0 _) (pow_nonneg hγ0 _))
  have hperp :
      ∑ d ∈ (Finset.range Nt).filter (fun d => 0 < d),
          Cperp * (γ ^ d + γ ^ (Nt - d))
        ≤ Cperp * (2 / (1 - γ)) := by
    rw [← Finset.mul_sum]
    exact le_trans
      (mul_le_mul_of_nonneg_left hgeom_filter hCperp_nonneg)
      (mul_le_mul_of_nonneg_left (geom_wrap_sum_le_two γ hγ0 hγ1 Nt) hCperp_nonneg)
  have hrem :
      ∑ _d ∈ (Finset.range Nt).filter (fun d => 0 < d), hRem.C_rem * γ ^ Nt
        ≤ hRem.C_rem * (Nt : ℝ) * γ ^ Nt := by
    calc
      ∑ _d ∈ (Finset.range Nt).filter (fun d => 0 < d), hRem.C_rem * γ ^ Nt
          ≤ (Nt : ℝ) * (hRem.C_rem * γ ^ Nt) :=
            sum_range_const_le_of_filter hrem_nonneg Nt (fun d => 0 < d)
      _ = hRem.C_rem * (Nt : ℝ) * γ ^ Nt := by ring
  calc
    ∑ d ∈ (Finset.range Nt).filter (fun d => 0 < d),
        |pathConnectedTwoPoint Ts A B Nt (d : ZMod Nt)|
        ≤ ∑ d ∈ (Finset.range Nt).filter (fun d => 0 < d),
            (Cperp * (γ ^ d + γ ^ (Nt - d)) + hRem.C_rem * γ ^ Nt) :=
          Finset.sum_le_sum hterm
    _ = (∑ d ∈ (Finset.range Nt).filter (fun d => 0 < d),
            Cperp * (γ ^ d + γ ^ (Nt - d)))
        + ∑ _d ∈ (Finset.range Nt).filter (fun d => 0 < d), hRem.C_rem * γ ^ Nt := by
          rw [Finset.sum_add_distrib]
    _ ≤ Cperp * (2 / (1 - γ)) + hRem.C_rem * (Nt : ℝ) * γ ^ Nt :=
          add_le_add hperp hrem

/-- All-time version over natural representatives, assuming the missing
zero-separation estimate explicitly. -/
theorem pathMeasure_connected_susceptibility_finite_periodic_bound_range
    (Ts : TransferSystem S) (Ω : S → ℝ) (lambda0 γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (A B : MultiplicationCLMContract Ts.ν)
    (hRem : RemainderHypothesis Ts Ω lambda0 γ A B)
    (Nt : ℕ) [NeZero Nt]
    (hzero :
      |pathConnectedTwoPoint Ts A B Nt (0 : ZMod Nt)|
        ≤ (‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖ *
            ‖hRem.G.vacuumPerp (B.M hRem.G.vacuum)‖) * (γ ^ 0 + γ ^ Nt)
          + hRem.C_rem * γ ^ Nt) :
    ∑ d ∈ Finset.range Nt, |pathConnectedTwoPoint Ts A B Nt (d : ZMod Nt)|
      ≤ (‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖ *
          ‖hRem.G.vacuumPerp (B.M hRem.G.vacuum)‖) * (2 / (1 - γ))
        + hRem.C_rem * (Nt : ℝ) * γ ^ Nt := by
  set Cperp : ℝ :=
    ‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖ *
      ‖hRem.G.vacuumPerp (B.M hRem.G.vacuum)‖ with hCperp_def
  have hCperp_nonneg : 0 ≤ Cperp := by
    rw [hCperp_def]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hterm :
      ∀ d ∈ Finset.range Nt,
        |pathConnectedTwoPoint Ts A B Nt (d : ZMod Nt)|
          ≤ Cperp * (γ ^ d + γ ^ (Nt - d)) + hRem.C_rem * γ ^ Nt := by
    intro d hd
    have hd_range : d < Nt := Finset.mem_range.mp hd
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · simpa [hCperp_def] using hzero
    · have hval : ((d : ZMod Nt).val) = d := ZMod.val_natCast_of_lt hd_range
      have h :=
        pathConnectedTwoPoint_le_of_remainder Ts Ω lambda0 γ A B hRem Nt (d : ZMod Nt)
          (by simpa [hval] using hd_pos)
          (by simpa [hval] using hd_range)
      simpa [finitePeriodicPerpEnvelope, hCperp_def, hval] using h
  have hperp :
      ∑ d ∈ Finset.range Nt, Cperp * (γ ^ d + γ ^ (Nt - d))
        ≤ Cperp * (2 / (1 - γ)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (geom_wrap_sum_le_two γ hγ0 hγ1 Nt) hCperp_nonneg
  have hrem :
      ∑ _d ∈ Finset.range Nt, hRem.C_rem * γ ^ Nt
        ≤ hRem.C_rem * (Nt : ℝ) * γ ^ Nt := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
  calc
    ∑ d ∈ Finset.range Nt, |pathConnectedTwoPoint Ts A B Nt (d : ZMod Nt)|
        ≤ ∑ d ∈ Finset.range Nt,
            (Cperp * (γ ^ d + γ ^ (Nt - d)) + hRem.C_rem * γ ^ Nt) :=
          Finset.sum_le_sum hterm
    _ = (∑ d ∈ Finset.range Nt, Cperp * (γ ^ d + γ ^ (Nt - d)))
        + ∑ _d ∈ Finset.range Nt, hRem.C_rem * γ ^ Nt := by
          rw [Finset.sum_add_distrib]
    _ ≤ Cperp * (2 / (1 - γ)) + hRem.C_rem * (Nt : ℝ) * γ ^ Nt :=
          add_le_add hperp hrem

/-- All-time connected susceptibility bound over `ZMod Nt`, assuming the
zero-separation estimate explicitly.

The positive-time terms are supplied by Piece E1; the zero-time term is a
separate hypothesis because Piece E1 requires `0 < t.val`. -/
theorem pathMeasure_connected_susceptibility_finite_periodic_bound
    (Ts : TransferSystem S) (Ω : S → ℝ) (lambda0 γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (A B : MultiplicationCLMContract Ts.ν)
    (hRem : RemainderHypothesis Ts Ω lambda0 γ A B)
    (Nt : ℕ) [NeZero Nt]
    (hzero :
      |pathConnectedTwoPoint Ts A B Nt (0 : ZMod Nt)|
        ≤ (‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖ *
            ‖hRem.G.vacuumPerp (B.M hRem.G.vacuum)‖) * (γ ^ 0 + γ ^ Nt)
          + hRem.C_rem * γ ^ Nt) :
    ∑ t : ZMod Nt, |pathConnectedTwoPoint Ts A B Nt t|
      ≤ (‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖ *
          ‖hRem.G.vacuumPerp (B.M hRem.G.vacuum)‖) * (2 / (1 - γ))
        + hRem.C_rem * (Nt : ℝ) * γ ^ Nt := by
  rw [sum_zmod_eq_sum_range]
  exact pathMeasure_connected_susceptibility_finite_periodic_bound_range
    Ts Ω lambda0 γ hγ0 hγ1 A B hRem Nt hzero

end ReflectionPositivity
