/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.InducedIso
import InverseGalois.CFT.TateCohomology.SylowInjective
import InverseGalois.CFT.TateCohomology.SylowSurjective

/-!
# Being the functions on a Sylow subgroup is already enough

A representation which is the functions on the group has no complete cohomology in any degree.  For
coefficients killed by a power of a prime that hypothesis is far stronger than it needs to be: it is
enough to be the functions on a Sylow subgroup for that prime.  Restriction to a Sylow subgroup is
injective on the part killed by a power of the prime, because corestriction after restriction is
multiplication by an index prime to it, and the restricted representation has no complete cohomology
at all, so nothing survives the restriction.

This is the sharp form of the vanishing a local-global principle asks for.  What has to be arranged
in an application is a statement about one Sylow subgroup of the Galois group of a finite extension,
not about the whole of it, and a Sylow subgroup is small enough that the statement can be arranged
by choosing the extension.

## Main results

* `InverseGalois.CFT.Tate.eq_zero_tateModule_of_isoInducedRep_sylow`: **a representation killed by
  a power of a prime whose restriction to a Sylow subgroup for that prime is the functions on that
  subgroup has no complete cohomology.**

## Tags

Tate cohomology, Sylow subgroup, induced representation, cohomologically trivial, restriction
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **A representation killed by a power of a prime whose restriction to a Sylow subgroup for that
prime is the functions on that subgroup has no complete cohomology.**  Restriction to the Sylow
subgroup kills every class, because there is nothing there for a class to restrict to, and
restriction to a Sylow subgroup is injective on the part killed by a power of the prime. -/
theorem eq_zero_tateModule_of_isoInducedRep_sylow {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {A : Rep k G} {X : Type u} [AddCommGroup X] [Module k X]
    (e : resObj (P : Subgroup G) A ≅ Rep.of (inducedRep k ↥(P : Subgroup G) X)) {j : ℕ}
    (hA : ∀ a : ↥A.V, p ^ j • a = 0) (n : ℤ) (y : tateModule A n) : y = 0 :=
  eq_zero_of_tateRes_sylow_eq_zero P
    (eq_zero_of_isZero (isZero_tateModule_of_isoInducedRep e n) _)
    (nsmul_eq_zero_tateModule_of_nsmul hA n y)

end

end InverseGalois.CFT.Tate
