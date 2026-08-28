/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.InertiaSubgroup
import InverseGalois.CFT.UnramifiedCompositum

/-!
# Restriction maps inertia onto inertia

Restriction to a normal subextension carries the inertia subgroup of a prime into the inertia
subgroup of the prime below it, and in fact *onto* it.  Both sides are counted: the image of a
subgroup under a homomorphism has order the order of the subgroup divided by the order of its
intersection with the kernel, the kernel of restriction is the subgroup fixing the subextension,
and the order of an inertia subgroup is the ramification index, which is multiplicative in a tower.
The two counts agree, and a subgroup contained in another of the same order is the whole of it.

Surjectivity is what makes a character of the Galois group of a subextension usable to correct the
ramification of a homomorphism defined upstairs: whatever the homomorphism does on inertia can be
matched by the inflated character precisely when the character already reaches, on the inertia
subgroup downstairs, everything that is wanted.

## Main results

* `InverseGalois.CFT.card_map_mul_card_inf_ker`: the order of the image of a subgroup times the
  order of its intersection with the kernel is the order of the subgroup.
* `InverseGalois.CFT.map_inertia_eq_inertia`: **restriction to a normal subextension maps the
  inertia subgroup of a prime onto the inertia subgroup of the prime below it.**
* `InverseGalois.CFT.inertia_eq_top_of_inertia_eq_top`: a normal subextension of an extension
  totally ramified at a prime is itself totally ramified there.

## Tags

inertia subgroup, ramification index, restriction, Galois group
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### Counting the image of a subgroup -/

/-- **The order of the image of a subgroup times the order of its intersection with the kernel is
the order of the subgroup.**  This is the first isomorphism theorem applied to the restriction of
the homomorphism to the subgroup. -/
theorem card_map_mul_card_inf_ker {Γ G : Type*} [Group Γ] [Group G] (f : Γ →* G) (I : Subgroup Γ) :
    Nat.card ↥(I.map f) * Nat.card ↥(f.ker ⊓ I : Subgroup Γ) = Nat.card ↥I := by
  have hker : (f.comp I.subtype).ker = (f.ker ⊓ I).subgroupOf I := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hrange : (f.comp I.subtype).range = I.map f := by
    ext y
    simp [MonoidHom.mem_range, Subgroup.mem_map]
  have h1 := Subgroup.card_mul_index (f.comp I.subtype).ker
  rw [Subgroup.index_ker, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := f.ker ⊓ I) (K := I) inf_le_right).toEquiv] at h1
  rw [mul_comm]
  exact h1

/-! ### Restriction of inertia subgroups -/

section Restrict

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N] {p : ℕ}

/-- **Restriction to a normal subextension maps the inertia subgroup of a prime onto the inertia
subgroup of the prime below it.**  The image is contained in the inertia subgroup downstairs, and
the two have the same order: the kernel of restriction is the subgroup fixing the subextension, so
the order of the image is the order of the inertia subgroup upstairs divided by the order of the
inertia subgroup over the subextension, which is the ramification index in the subextension, that
is, the order of the inertia subgroup downstairs. -/
theorem map_inertia_eq_inertia (F : IntermediateField ℚ N) [Normal ℚ ↥F] (hp : p.Prime)
    (P : Ideal (𝓞 N)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (Ideal.inertia Gal(N/ℚ) P).map (AlgEquiv.restrictNormalHom ↥F) =
      Ideal.inertia Gal(↥F/ℚ) (P.under (𝓞 ↥F)) := by
  haveI : NumberField ↥F := ⟨⟩
  haveI : IsGalois ℚ ↥F := ⟨⟩
  haveI := liesOver_under_intermediateField (p := p) F P
  haveI : P.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime (ne_bot_of_liesOver_natCast hp inferInstance) inferInstance
  have hgt := card_map_mul_card_inf_ker (AlgEquiv.restrictNormalHom ↥F) (Ideal.inertia Gal(N/ℚ) P)
  rw [IntermediateField.restrictNormalHom_ker, inf_comm, card_inertia_eq_mul F hp P,
    ← card_inertia_eq_ramificationIdx_span (K := ↥F) hp (P.under (𝓞 ↥F))] at hgt
  exact eq_of_le_of_card_eq (map_inertia_le_inertia F P)
    (Nat.eq_of_mul_eq_mul_right Nat.card_pos hgt)

/-- **A subextension of a totally ramified extension is totally ramified.**  Restriction is
surjective onto the Galois group of a normal subextension and maps inertia onto inertia, so the
whole group is reached. -/
theorem inertia_eq_top_of_inertia_eq_top (F : IntermediateField ℚ N) [Normal ℚ ↥F] (hp : p.Prime)
    (P : Ideal (𝓞 N)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (h : Ideal.inertia Gal(N/ℚ) P = ⊤) :
    Ideal.inertia Gal(↥F/ℚ) (P.under (𝓞 ↥F)) = ⊤ := by
  haveI : Normal ℚ N := IsGalois.to_normal
  rw [← map_inertia_eq_inertia F hp P, h]
  exact Subgroup.map_top_of_surjective _ (AlgEquiv.restrictNormalHom_surjective N)

end Restrict

end InverseGalois.CFT
