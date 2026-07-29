/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RiemannExistence

/-!
# The rigidity criterion for the Inverse Galois Problem

This file assembles the rigidity method's headline theorem: a **rigidity certificate**
(`RigidityCertificate G`, purely group-theoretic and cheap to check) proves that `G` is an inverse
Galois group over `ℚ`.

The proof is the intended seam of the whole project:

1. represent `G` faithfully as `H = (cayley G).range ≤ Equiv.Perm (Fin (Nat.card G))`;
2. the Riemann Existence Theorem (`Rigidity.riemann_existence`, the analytic axiom) produces a
   regular resolvent family over `ℚ(T)` for `H`;
3. `IsInverseGalois.of_regular_family` runs the **proven** Hilbert-irreducibility descent
   `ℚ(T) → ℚ`, giving `IsInverseGalois H`;
4. transport back along `G ≃* H` (`IsInverseGalois.of_mulEquiv`).

## Main results

* `Rigidity.rigidity_realizable` — a rigidity certificate yields `IsInverseGalois G`.
-/

open Polynomial

namespace Rigidity

/-- **The rigidity criterion.**  A finite group possessing a rigidity certificate — rational
conjugacy classes with a unique generating product-one tuple, the group being centerless — is an
inverse Galois group over `ℚ`.

Modulo the single analytic axiom `riemann_existence_ax` (isolated in
`InverseGalois.Rigidity.RiemannExistence`, and normally routed through the `sorry`-bodied
`riemann_existence` during development), this reduces realizability of `G` to a finite, checkable
certificate. -/
theorem rigidity_realizable {G : Type*} [Group G] [Finite G]
    (cert : RigidityCertificate G) : IsInverseGalois G := by
  obtain ⟨F, Gp, hFm, hFd, hGm, hGd, hGirr, hGabs, hFsep, hland, hroot⟩ :=
    riemann_existence cert (cayley G) cayley_injective
  have hHG : IsInverseGalois (cayley G).range :=
    IsInverseGalois.of_regular_family (cayley G).range F Gp hFm hFd hGm hGd hGirr hGabs
      hFsep hland hroot
  exact hHG.of_mulEquiv (MonoidHom.ofInjective cayley_injective).symm

end Rigidity
