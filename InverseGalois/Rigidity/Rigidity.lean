/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET

/-!
# The rigidity criterion for the Inverse Galois Problem

This file assembles the rigidity method's headline theorem: a **rigidity certificate**
(`RigidityCertificate G`, purely group-theoretic and cheap to check) proves that `G` is an inverse
Galois group over `ℚ`.

The proof is the honest three-step chain resting on a single deep geometric input, the Riemann
Existence Theorem at the tame-inertia interface (`inertiaRootData_exists`, `RET.Descent.Tower`):

1. **Riemann Existence Theorem** — for the certificate's rigid generating product-one tuple, the
   geometric cover branched over the `r` points exists, carrying its tame inertia generators (which
   generate the geometric group with the product-one relation and realize the monodromy) and their
   cyclotomic conjugation under the arithmetic Galois group (Fried's branch-cycle formula).  This is
   the arithmetic model with its `InertiaRootData` (`inertiaRootData_exists`, `Descent.Tower`).
2. **Branch-cycle descent** `ℚ̄(T) → ℚ(T)` — rationality + rigidity + centerless carry that datum to a
   *regular* Galois extension of `ℚ(T)` with group `G` (`RigidityCertificate.isRegularInverseGalois`,
   via `branch_cycle_descent`).  Fully proven from step 1.
3. **Hilbert specialization** `ℚ(T) → ℚ` — a regular `ℚ(T)`-extension specializes to a `ℚ`-Galois
   extension with the same group (`IsRegularInverseGalois.isInverseGalois`, via the model translation
   `exists_regular_family` and the repository's Hilbert-irreducibility descent).  Fully proven.

Steps 2 and 3 are genuine, complete Lean proofs; the whole reduction pivots on step 1 — the
recognizable Riemann Existence Theorem, refined by Fried's branch-cycle formula and stated at exactly
the tame-inertia interface the descent consumes — which is the one genuinely geometric ingredient,
being built from the étale/tame fundamental-group theory under `RET.Pi1`.

## Main results

* `Rigidity.rigidity_realizable` — a rigidity certificate yields `IsInverseGalois G`.
-/

namespace Rigidity

/-- **The rigidity criterion.**  A finite group possessing a rigidity certificate — rational
conjugacy classes with a unique generating product-one tuple, the group being centerless — is an
inverse Galois group over `ℚ`.

This composes the honest three-step chain: the Riemann Existence Theorem at the tame-inertia
interface (`inertiaRootData_exists`), the branch-cycle descent to `ℚ(T)`, and Hilbert specialization
to `ℚ` — the latter two fully proven.  Modulo that single geometric input, realizability of `G`
reduces to a finite, checkable certificate. -/
theorem rigidity_realizable {G : Type} [Group G] [Finite G]
    (cert : RigidityCertificate G) : IsInverseGalois G :=
  cert.isRegularInverseGalois.isInverseGalois

end Rigidity
