/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Compositum

/-!
# The compositum of extensions of `ℓ`-power degree

An automorphism of a compositum of two normal subextensions is determined by its restrictions to
the two factors, so the Galois group of the compositum embeds in the product of the two Galois
groups.  If both factors have `ℓ`-power degree, so does the compositum, and the same follows for a
finite family of factors by induction.

This is what keeps the ramification arguments of the Scholz–Reichardt construction available after
the correcting cyclotomic characters have been adjoined: the enlarged field still has `ℓ`-power
degree, so its inertia subgroups away from `ℓ` are still tame and cyclic.

## Main results

* `InverseGalois.CFT.isPGroup_sup`: **the compositum of two normal subextensions whose Galois
  groups are `ℓ`-groups has an `ℓ`-group as Galois group.**
* `InverseGalois.CFT.isPGroup_finsetSup`: the same for the compositum of a finite family.

## Tags

compositum, Galois group, `p`-group, intermediate field
-/

namespace InverseGalois.CFT

open IntermediateField

variable {ℓ : ℕ}

/-- **A product of two `ℓ`-groups is an `ℓ`-group.** -/
theorem isPGroup_prod {G H : Type*} [Group G] [Group H] (hG : IsPGroup ℓ G) (hH : IsPGroup ℓ H) :
    IsPGroup ℓ (G × H) := by
  intro g
  obtain ⟨a, ha⟩ := hG g.1
  obtain ⟨b, hb⟩ := hH g.2
  have h1 : g.1 ^ ℓ ^ max a b = 1 := orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_iff_pow_eq_one.mpr ha).trans (pow_dvd_pow ℓ (le_max_left a b)))
  have h2 : g.2 ^ ℓ ^ max a b = 1 := orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_iff_pow_eq_one.mpr hb).trans (pow_dvd_pow ℓ (le_max_right a b)))
  exact ⟨max a b, Prod.ext (by simpa using h1) (by simpa using h2)⟩

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **The compositum of two normal subextensions whose Galois groups are `ℓ`-groups has an
`ℓ`-group as Galois group.**  Restriction to the two factors is an injective homomorphism into the
product of the two Galois groups. -/
theorem isPGroup_sup (A B : IntermediateField F L) [Normal F ↥A] [Normal F ↥B]
    (hA : IsPGroup ℓ Gal(↥A/F)) (hB : IsPGroup ℓ Gal(↥B/F)) :
    IsPGroup ℓ Gal(↥(A ⊔ B)/F) :=
  (isPGroup_prod hA hB).of_injective (galRestrictProd A B) (galRestrictProd_injective A B)

/-- The base field, seen as the smallest intermediate field, is normal over itself. -/
theorem normal_bot : Normal F ↥(⊥ : IntermediateField F L) :=
  Normal.of_algEquiv (IntermediateField.botEquiv F L).symm

variable {ι : Type*} (A : ι → IntermediateField F L)

/-- The compositum of a finite family of normal subextensions is normal. -/
theorem normal_finsetSup [∀ i, Normal F ↥(A i)] (s : Finset ι) : Normal F ↥(s.sup A) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sup_empty]
    exact normal_bot
  | cons a s _ ih =>
    haveI := ih
    rw [Finset.sup_cons]
    infer_instance

/-- **The compositum of a finite family of normal subextensions whose Galois groups are `ℓ`-groups
has an `ℓ`-group as Galois group.** -/
theorem isPGroup_finsetSup [∀ i, Normal F ↥(A i)] (hA : ∀ i, IsPGroup ℓ Gal(↥(A i)/F))
    (s : Finset ι) : IsPGroup ℓ Gal(↥(s.sup A)/F) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sup_empty]
    haveI : Subsingleton Gal(↥(⊥ : IntermediateField F L)/F) :=
      (AlgEquiv.autCongr (IntermediateField.botEquiv F L)).toEquiv.subsingleton
    exact fun g => ⟨0, by simpa using Subsingleton.elim g 1⟩
  | cons a s _ ih =>
    haveI := normal_finsetSup A s
    rw [Finset.sup_cons]
    exact isPGroup_sup (A a) (s.sup A) (hA a) ih

end InverseGalois.CFT
