/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Graph homomorphism functions `f_H(G) := hom(G, H)`

For a weighted graph `H = (a, B)` (positive node weights
`a : V(H) → ℝ_{>0}` and symmetric real edge-weight matrix
`B : V(H) × V(H) → ℝ`), the **homomorphism function** is

  `f_H(G) := ∑_{φ : V(G) → V(H)} (∏_u α(φu)) · (∏_{uv ∈ E(G)} β(φu, φv))`.

This family is reflection-positive (the **easy direction** of the FLS
main theorem) with rank-connectivity `r(f_H, k) ≤ |V(H)|^k`.

The Freedman-Lovász-Schrijver main theorem (in
`FreedmanLovaszSchrijver.lean`) is the **converse**: any RP
multiplicative graph parameter with bounded `r(f, k)` growth is
a homomorphism function `f_H` for some weighted `H`.

## Main definitions (planned)

* `Graph.WeightedGraph` — a finite graph with node weights and a
  symmetric real edge-weight matrix.
* `Graph.homomorphismFunction H` — `f_H(G)` as defined above.

## Main theorems (planned)

* `Graph.homomorphismFunction.isMultiplicative` — `f_H(G₁ ⊔ G₂) = f_H(G₁) · f_H(G₂)`.
* `Graph.homomorphismFunction.isReflectionPositive` — `M(f_H, k)` is
  PSD for every `k`, with explicit rank bound
  `r(f_H, k) ≤ |V(H)|^k`. The PSD structure comes from the explicit
  factorization
  `M(f_H, k) = ∑_{φ : [k] → V(H)} α_φ · (column-vector of `f_{H,φ}`-extensions)·(its transpose)`.

## References

* M. Freedman, L. Lovász, A. Schrijver, *Reflection positivity, rank
  connectivity, and homomorphism of graphs*, JAMS 20 (2007), §2.4
  Lemma 2.3.

## Status

**Stub.** Parallel deliverable; lower priority than the critical-path
OS files.
-/

import ReflectionPositivity.Graph.ConnectionMatrix

namespace Graph

-- (definitions to be added)

end Graph
