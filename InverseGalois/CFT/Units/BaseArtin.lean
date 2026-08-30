/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Abelianization
import InverseGalois.CFT.Units.BaseTate

/-!
# The reciprocity law of a Galois extension of number fields

Tate's theorem applied to the fundamental class of the idele class group identifies the complete
cohomology of the trivial integral representation in degree minus two with the complete cohomology
of the idele class group in degree zero.  The left hand side is the abelianization of the Galois
group, so the composite is an isomorphism between the abelianization of the Galois group and the
complete cohomology of the idele class group in degree zero, which is the invariant idele classes
modulo the norms.

## Main definitions

* `InverseGalois.CFT.baseArtinEquiv`: **the reciprocity isomorphism between the abelianization of
  the Galois group of an extension of number fields and the complete cohomology of the idele class
  group in degree zero.**

## Tags

number field, idele class group, class formation, reciprocity, Artin map, abelianization
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open CategoryTheory NumberField

namespace InverseGalois.CFT

noncomputable section

open Tate

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **The reciprocity isomorphism of a Galois extension of number fields**: the abelianization of
the Galois group is the complete cohomology of the idele class group in degree zero, that is the
invariant idele classes modulo the norms from the extension. -/
def baseArtinEquiv :
    Additive (Abelianization Gal(K/k)) ≃ₗ[ℤ] tateModule (ideleClassRep k K) 0 :=
  (tateNegTwoTrivialEquiv Gal(K/k)).symm.trans (baseReciprocityEquiv k K)

end

end InverseGalois.CFT
