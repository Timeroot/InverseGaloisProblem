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

The proof is the three-step chain resting on the Riemann Existence Theorem at the tame-inertia
interface (`inertiaRootData_exists`, `RET.Descent.Tower`):

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

Step 1 is the geometric one, built from the étale and tame fundamental-group theory under `RET.Pi1`
and the analytic construction of coverings under `RET.Analytic`; steps 2 and 3 are algebra.

## Main results

* `Rigidity.RigidityCertificate.isRegularInverseGalois` — a rigidity certificate yields
  `IsRegularInverseGalois G` (in `RET.Descent`).
* `Rigidity.rigidity_realizable` — hence `IsInverseGalois G`.
-/

namespace Rigidity

/-- **The rigidity criterion.**  A finite group possessing a rigidity certificate — rational
conjugacy classes with a unique generating product-one tuple, the group being centerless — is an
inverse Galois group over `ℚ`.

This composes the three-step chain: the Riemann Existence Theorem at the tame-inertia interface
(`inertiaRootData_exists`), the branch-cycle descent to `ℚ(T)`, and Hilbert specialization to `ℚ`.
Realizability of `G` therefore follows, unconditionally, from a finite checkable certificate.  The
intermediate `RigidityCertificate.isRegularInverseGalois` is the stronger statement, over `ℚ(T)`. -/
theorem rigidity_realizable {G : Type} [Group G] [Finite G]
    (cert : RigidityCertificate G) : IsInverseGalois G :=
  cert.isRegularInverseGalois.isInverseGalois

end Rigidity
