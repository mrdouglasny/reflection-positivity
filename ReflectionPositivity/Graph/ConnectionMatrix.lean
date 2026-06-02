/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Graph reflection positivity (Freedman-Lovász-Schrijver) — connection matrix

For a graph parameter `f : Graph → ℝ` (multiplicative under disjoint
union) and `k ≥ 0`, the **connection matrix** `M(f, k)` has rows and
columns indexed by isomorphism classes of `k`-labeled graphs, with
entry at `(G₁, G₂)` given by `f(G₁ G₂)` where `G₁ G₂` is the product
(disjoint union with label-matched gluing).

A graph parameter `f` is **reflection-positive** when `M(f, k)` is
positive semi-definite for every `k`. This is the FLS reformulation
of OS reflection positivity for graph-theoretic / statistical-
mechanical settings.

## Main definitions (planned)

* `Graph.LabeledGraph k` — finite graphs with `k` distinguished
  labeled vertices (and possibly any number of unlabeled vertices).
  Equipped with: disjoint-union product `LabeledGraph k → LabeledGraph k → LabeledGraph k`
  (glue along labels) and an involution (relabeling).
* `Graph.connectionMatrix f k` — the infinite matrix indexed by
  isomorphism classes of `k`-labeled graphs, with entry
  `M(f, k)_{G₁, G₂} = f(G₁ G₂)`.
* `Graph.IsReflectionPositive f` — `M(f, k)` is positive semi-definite
  for every `k`.
* `Graph.rankConnectivity f k` — `r(f, k) := rk(M(f, k))`.

## Main theorems (planned)

* `Graph.IsReflectionPositive.diagonalNonneg` — `f(G G) ≥ 0` for every
  `k`-labeled `G` (diagonal of a PSD matrix is nonnegative).
* `Graph.rankConnectivity.subadditive` — `r(f, k + l) ≥ r(f, k) · r(f, l)`
  for multiplicative `f` (FLS Proposition 2.2).
* `Graph.IsReflectionPositive.quantumGraphNonneg` — for any
  `k`-labeled quantum graph `X = ∑ xᵢ Gᵢ`, `f(X²) ≥ 0` (the
  quantum-graph reformulation of RP).

## Relationship to OS reflection positivity

The shared abstract template: a *-semigroup with a PSD bilinear form
on its semigroup algebra. OS RP specializes the semigroup to
`L²(A_+)` with reflection `θ`; FLS RP specializes it to the algebra
of `k`-labeled graphs with the label-matched product and relabeling.
Both can be packaged via a common abstract `IsReflectionPositive`
predicate on `*-semigroups → ℝ`.

For the initial release, OS and FLS live in parallel without forced
sharing (per the PLAN). If the shared abstraction pays off in
practice, a refactor can lift the common content (GNS-style quotient
construction) into `Abstract.lean`.

## References

* M. Freedman, L. Lovász, A. Schrijver, *Reflection positivity, rank
  connectivity, and homomorphism of graphs*, J. Amer. Math. Soc. 20
  (2007), 37-51.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium
  Publications 60 (2012), Ch. 6.

## Status

**Stub.** Parallel deliverable; lower priority than the critical-path
OS files.
-/

namespace Graph

-- (definitions to be added)

end Graph
