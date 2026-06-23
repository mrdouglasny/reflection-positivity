/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Multiplication-CLM contract for an `L²` Hilbert space

A **multiplication-CLM contract** packages, in one structure, an observable
`A : α → ℝ` together with the **multiplication operator** `M_A : L²(μ) →L[ℝ] L²(μ)`
it induces and the proofs that this operator (i) acts pointwise as `f ↦ A · f`
a.e. and (ii) is self-adjoint.

**Piece B of the GNS / ground-state-transform construction** (see
`docs/gns-construction-plan.md`).

## Why a contract rather than a definition

The GNS bridge in reflection-positivity is stated abstractly — it accepts a
multiplication CLM as input. The concrete construction of `M_A` from a
bounded `A` (the `mulCLM` API) lives in pphi2 (`Pphi2/TransferMatrix/L2Multiplication.lean`)
and is generic enough to instantiate this contract directly. Keeping the
contract abstract avoids cross-repo code moves and lets the bridge work on
any `M_A : L²(μ) →L[ℝ] L²(μ)` proven to be multiplication by a bounded
observable.

In the typical use case (e.g., pphi2 Layer-B2 Piece 2), the consumer
constructs a `MultiplicationCLMContract` from
`Pphi2.mulCLM`, `Pphi2.mulCLM_spec`, `Pphi2.mulCLM_isSelfAdjoint`.

## Main definitions

* `MultiplicationCLMContract μ` — the contract structure: an observable `A`,
  its measurability + a.e. boundedness, the CLM `M`, the a.e. spec
  `⇑(M f) =ᵐ A · f`, and the self-adjointness `IsSelfAdjoint M`.
-/

open MeasureTheory

namespace ReflectionPositivity

variable {α : Type*} [MeasurableSpace α]

/-- A **multiplication-CLM contract** for the L²-space `L²(α, μ; ℝ)`: an
observable `A : α → ℝ` together with the multiplication operator `M` it
defines, equipped with the a.e. spec and the self-adjointness proof. The
input the GNS / ground-state-transform bridge consumes from downstream
consumers (e.g., pphi2's `mulCLM`). -/
structure MultiplicationCLMContract (μ : Measure α) where
  /-- The (real-valued) bounded observable. -/
  A : α → ℝ
  /-- The observable is measurable. -/
  A_meas : Measurable A
  /-- The observable is a.e.-bounded (with some explicit bound `K > 0`). -/
  A_bound : ∃ K : ℝ, 0 < K ∧ ∀ᵐ x ∂μ, |A x| ≤ K
  /-- The multiplication operator `M_A : L²(μ) →L[ℝ] L²(μ)`. -/
  M : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ
  /-- The CLM acts pointwise as multiplication by `A` (a.e.). -/
  spec : ∀ f : Lp ℝ 2 μ, (⇑(M f) : α → ℝ) =ᵐ[μ] fun x => A x * f x
  /-- The multiplication operator is self-adjoint (since `A` is real). -/
  selfAdjoint : IsSelfAdjoint M

namespace MultiplicationCLMContract

variable {μ : Measure α}

/-- The bound `K` from the contract. -/
noncomputable def bound (C : MultiplicationCLMContract μ) : ℝ :=
  C.A_bound.choose

theorem bound_pos (C : MultiplicationCLMContract μ) : 0 < C.bound :=
  C.A_bound.choose_spec.1

theorem A_abs_le_bound (C : MultiplicationCLMContract μ) :
    ∀ᵐ x ∂μ, |C.A x| ≤ C.bound :=
  C.A_bound.choose_spec.2

end MultiplicationCLMContract

end ReflectionPositivity
