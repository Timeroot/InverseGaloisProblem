/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleNormTower
import InverseGalois.CFT.Units.NormIndex

/-!
# A solvable extension whose norms exhaust the ideles is trivial

The first inequality says that a *cyclic* extension of number fields whose norms together with the
principal ideles exhaust the ideles of the base field is trivial.  The same conclusion holds for a
*solvable* extension, and that is the form in which the statement is used: the candidate extensions
produced by the second inequality are solvable, not cyclic.

A nontrivial finite solvable group has a nontrivial character with values in the complex numbers,
because its abelianization is a nontrivial finite commutative group and characters separate the
elements of such a group.  The quotient by the kernel of a character is a finite subgroup of the
complex units, hence cyclic, so a nontrivial solvable extension contains a nontrivial cyclic
subextension.  The norms from the top field are norms from the subextension, because the norm of a
tower is the composite of the two norms, so the subextension inherits the hypothesis and the cyclic
case makes it trivial.

Nothing here needs a topology on the ideles: the hypothesis is an exact equality of subgroups.

## Main results

* `InverseGalois.CFT.exists_complexChar_ker_ne_top`: **a nontrivial finite solvable group has a
  complex character whose kernel is proper.**
* `InverseGalois.CFT.isCyclic_quotient_ker_units`: the quotient of a finite group by the kernel of a
  character with values in the units of an integral domain is cyclic.
* `InverseGalois.CFT.ideleNorm_range_le_of_intermediateField`: the norms from the top field of a
  tower are norms from the middle field.
* `InverseGalois.CFT.subsingleton_gal_of_isSolvable_of_ideleDiag_sup_le`: **a solvable extension of
  number fields whose norms together with the principal ideles exhaust the ideles of the base field
  is trivial.**

## Tags

number field, idele, norm, first inequality, solvable extension
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

/-! ### The group-theoretic input -/

/-- **A nontrivial finite solvable group has a complex character whose kernel is proper.**  Its
abelianization is a nontrivial finite commutative group, and characters of a finite commutative
group with values in the complex numbers separate its elements. -/
theorem exists_complexChar_ker_ne_top (G : Type*) [Group G] [Finite G] [IsSolvable G]
    [Nontrivial G] : ∃ ψ : G →* ℂˣ, ψ.ker ≠ ⊤ := by
  obtain ⟨a, -, ha⟩ := SetLike.exists_of_lt (IsSolvable.commutator_lt_top_of_nontrivial G)
  have hne : Abelianization.of a ≠ 1 := fun h => ha ((QuotientGroup.eq_one_iff a).mp h)
  obtain ⟨φ, hφ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Abelianization G) ℂ hne
  refine ⟨φ.comp Abelianization.of, fun htop => hφ ?_⟩
  have hmem : a ∈ (φ.comp Abelianization.of).ker := by rw [htop]; trivial
  exact MonoidHom.mem_ker.mp hmem

/-- **The quotient of a finite group by the kernel of a character with values in the units of an
integral domain is cyclic**, since it is isomorphic to the image, a finite subgroup of the
units. -/
theorem isCyclic_quotient_ker_units {G : Type*} [Group G] [Finite G] {R : Type*} [CommRing R]
    [IsDomain R] (ψ : G →* Rˣ) : IsCyclic (G ⧸ ψ.ker) := by
  haveI : Finite ψ.range := Finite.of_surjective _ ψ.rangeRestrict_surjective
  exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange ψ).symm
    (QuotientGroup.quotientKerEquivRange ψ).symm.surjective

/-- The quotient of a group by a proper normal subgroup is nontrivial. -/
theorem nontrivial_quotient_of_ne_top {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (h : H ≠ ⊤) : Nontrivial (G ⧸ H) := by
  obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr h)
  exact nontrivial_of_ne (QuotientGroup.mk g) 1 fun hq => hg ((QuotientGroup.eq_one_iff g).mp hq)

/-! ### The norms of a tower -/

section Tower

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **The norms from the top field of a tower are norms from the middle field**: the norm of a tower
is the norm to the middle field followed by the norm from the middle field. -/
theorem ideleNorm_range_le_of_intermediateField (F : IntermediateField k K) [IsGalois k ↥F] :
    (ideleNorm k K).range ≤ (ideleNorm k ↥F).range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨ideleNorm (↥F) K x, ideleNorm_trans k (↥F) K x⟩

end Tower

/-! ### The solvable case of the first inequality -/

section SolvableNorm

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **A solvable extension of number fields whose norms together with the principal ideles exhaust
the ideles of the base field is trivial.**  Were the extension nontrivial, its Galois group would
have a proper normal subgroup with cyclic quotient, and the fixed field of that subgroup would be a
nontrivial cyclic subextension inheriting the hypothesis, contradicting the cyclic case. -/
theorem subsingleton_gal_of_isSolvable_of_ideleDiag_sup_le [IsSolvable Gal(K/k)]
    {D : AddSubgroup ↥(idele k)} (hD : D ≤ (ideleNorm k K).range)
    (htop : (ideleDiag k).range ⊔ D = ⊤) : Subsingleton Gal(K/k) := by
  rw [← not_nontrivial_iff_subsingleton]
  intro hnt
  obtain ⟨ψ, hψ⟩ := exists_complexChar_ker_ne_top Gal(K/k)
  haveI : IsCyclic (Gal(K/k) ⧸ ψ.ker) := isCyclic_quotient_ker_units ψ
  haveI : Nontrivial (Gal(K/k) ⧸ ψ.ker) := nontrivial_quotient_of_ne_top ψ.ker hψ
  set F := IntermediateField.fixedField ψ.ker with hF
  haveI : IsCyclic Gal(↥F/k) := isCyclic_of_surjective (IsGalois.normalAutEquivQuotient ψ.ker)
    (IsGalois.normalAutEquivQuotient ψ.ker).surjective
  haveI : Nontrivial Gal(↥F/k) := (IsGalois.normalAutEquivQuotient ψ.ker).injective.nontrivial
  have hsub : (ideleDiag k).range ⊔ (ideleNorm k ↥F).range = ⊤ :=
    top_le_iff.mp (htop ▸ sup_le_sup_left
      (hD.trans (ideleNorm_range_le_of_intermediateField F)) (ideleDiag k).range)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(↥F/k))
  haveI : NeZero (Nat.card Gal(↥F/k)) := ⟨Nat.card_pos.ne'⟩
  exact (not_nontrivial_iff_subsingleton.mpr
    (subsingleton_gal_of_ideleDiag_sup_ideleNorm_eq_top (K := ↥F) rfl hσ hsub)) inferInstance

end SolvableNorm

end InverseGalois.CFT
