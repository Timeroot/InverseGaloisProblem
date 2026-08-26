/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Compositum

/-!
# The compositum of two nilpotent subextensions

An automorphism of a compositum of two normal subextensions is determined by its restrictions to
the two factors, so the Galois group of the compositum embeds in the product of the two Galois
groups.  Nilpotency is inherited by products and by subgroups, hence by the compositum.

The Scholz–Reichardt construction uses this to keep the constraint field of the auxiliary primes
nilpotent: that field is the compositum of an extension with `ℓ`-group Galois group and a
cyclotomic field, and nilpotency is exactly what makes a rational number which is not an `ℓ`-th
power stay a non-power there.

## Main results

* `InverseGalois.CFT.isNilpotent_sup`: **the compositum of two normal subextensions with nilpotent
  Galois groups has a nilpotent Galois group.**

## Tags

compositum, Galois group, nilpotent group, intermediate field
-/

namespace InverseGalois.CFT

open IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **The compositum of two normal subextensions with nilpotent Galois groups has a nilpotent
Galois group.**  Restriction to the two factors identifies the Galois group of the compositum with
a subgroup of the product of the two Galois groups. -/
theorem isNilpotent_sup (A B : IntermediateField F L) [Normal F ↥A] [Normal F ↥B]
    (hA : Group.IsNilpotent Gal(↥A/F)) (hB : Group.IsNilpotent Gal(↥B/F)) :
    Group.IsNilpotent Gal(↥(A ⊔ B)/F) := by
  haveI := hA
  haveI := hB
  exact nilpotent_of_mulEquiv
    (MonoidHom.ofInjective (galRestrictProd_injective A B)).symm

end InverseGalois.CFT
