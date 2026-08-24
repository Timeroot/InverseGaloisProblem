/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.SecondInequality
import InverseGalois.CFT.Units.BaseChangeIndex

/-!
# The norm index of an extension of prime degree

The count of the norms of a radical extension asks the base field to carry a primitive root of
unity of the degree.  That hypothesis can be removed: adjoining a primitive `p`-th root of unity to
the base field is an extension of degree dividing `p - 1`, hence prime to `p`, and enlarging the
base field by an extension of degree prime to the degree can only increase the norm index.  So the
index upstairs, where the count applies, bounds the index downstairs, which the first inequality
bounds from below by the degree; the two bounds meet.

The construction is carried out inside an ambient field carrying a primitive `p`-th root of unity
`ζ`, for instance an algebraic closure of the extension.  The larger base field is the field
generated over the base by `ζ`, and the larger top field is the field generated over the extension
by `ζ`.  The latter is the compositum of the two, so it is normal over the base field, and its
degree over the larger base field is again `p`: it is divisible by `p` because the degree of the
larger base field is prime to `p`, and it is at most `p` because the degree of the root of unity
can only drop when the base field grows.

## Main results

* `InverseGalois.CFT.index_ideleDiag_sup_ideleNorm_of_ambient_primitiveRoot`: the index of the
  principal ideles together with the norms from an extension of prime degree is the degree, when a
  primitive root of unity of that degree is available in an ambient field.
* `InverseGalois.CFT.index_ideleDiag_sup_ideleNorm_eq_of_prime_degree`: **the index of the principal
  ideles together with the norms from an extension of prime degree is the degree**, with no
  hypothesis on the roots of unity of the base field.

## Tags

number field, idele, norm index, second inequality, cyclotomic extension, prime degree
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped IntermediateField

/-! ### An ambient field carrying the roots of unity -/

section Ambient

variable {k L Ω : Type*} [Field k] [NumberField k] [Field L] [NumberField L] [Field Ω]
  [Algebra k L] [Algebra L Ω] [Algebra k Ω] [IsScalarTower k L Ω] [IsGalois k L]
  [Algebra.IsAlgebraic L Ω] {p : ℕ} {ζ : Ω}

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
/-- **The index of the principal ideles together with the norms from an extension of prime degree
is the degree**, given a primitive root of unity of that degree in an ambient field.  Adjoining the
root of unity to the base field and to the extension produces a second extension of the same prime
degree over a base field which is an extension of the old one of degree prime to it, so the index
for the new pair bounds the index for the old one, and the first inequality bounds the latter from
below. -/
theorem index_ideleDiag_sup_ideleNorm_of_ambient_primitiveRoot (hp : p.Prime)
    (hζ : IsPrimitiveRoot ζ p) (hdeg : Module.finrank k L = p) :
    ((ideleDiag k).range ⊔ (ideleNorm k L).range).index = p := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Algebra.IsAlgebraic k Ω := Algebra.IsAlgebraic.trans k L Ω
  -- the cyclotomic field over the base
  set Zk : IntermediateField k Ω := k⟮ζ⟯ with hZk
  haveI : IsCyclotomicExtension {p} k ↥Zk := hζ.intermediateField_adjoin_isCyclotomicExtension k
  haveI : FiniteDimensional k ↥Zk :=
    IsCyclotomicExtension.finiteDimensional (S := {p}) (K := k) (C := ↥Zk)
  haveI : NumberField ↥Zk := NumberField.of_module_finite k ↥Zk
  haveI : IsGalois k ↥Zk := IsCyclotomicExtension.isGalois (S := {p}) (K := k) (L := ↥Zk)
  -- the top field
  set L' : IntermediateField L Ω := L⟮ζ⟯ with hL'
  haveI : FiniteDimensional L ↥L' :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := L) ζ)
  haveI : NumberField ↥L' := NumberField.of_module_finite L ↥L'
  -- the image of the given extension inside the ambient field
  set Lk : IntermediateField k Ω := (IsScalarTower.toAlgHom k L Ω).fieldRange
  haveI : Normal k ↥Lk :=
    Normal.of_algEquiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L Ω))
  -- the top field is the compositum
  have hsup : IntermediateField.restrictScalars k L' = Lk ⊔ Zk := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · intro x hx
      have hmem : ∀ y : L, (algebraMap L Ω) y ∈ (Lk ⊔ Zk : IntermediateField k Ω) := fun y =>
        le_sup_left (a := Lk) (b := Zk) ⟨y, rfl⟩
      have hEle : (L⟮ζ⟯ : IntermediateField L Ω)
          ≤ Subfield.toIntermediateField (K := L) (Lk ⊔ Zk).toSubfield hmem :=
        IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
          (le_sup_right (a := Lk) (b := Zk) (IntermediateField.mem_adjoin_simple_self k ζ)))
      exact hEle hx
    · rintro x ⟨y, rfl⟩
      exact IntermediateField.algebraMap_mem (L⟮ζ⟯ : IntermediateField L Ω) y
    · exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
        (IntermediateField.mem_adjoin_simple_self L ζ))
  haveI : Normal k ↥L' := Normal.of_algEquiv (IntermediateField.equivOfEq hsup).symm
  haveI : IsGalois k ↥L' := ⟨⟩
  haveI : IsGalois L ↥L' := IsGalois.tower_top_of_isGalois k L ↥L'
  -- the cyclotomic field sits inside the top field
  have hZle : Zk ≤ IntermediateField.restrictScalars k L' := hsup ▸ le_sup_right
  letI : Algebra ↥Zk ↥L' := (IntermediateField.inclusion hZle).toRingHom.toAlgebra
  haveI : IsScalarTower k ↥Zk ↥L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGalois ↥Zk ↥L' := IsGalois.tower_top_of_isGalois k ↥Zk ↥L'
  -- the root of unity, read in the cyclotomic field
  have hζmem : ζ ∈ Zk := by rw [hZk]; exact IntermediateField.mem_adjoin_simple_self k ζ
  have hζ' : IsPrimitiveRoot (⟨ζ, hζmem⟩ : ↥Zk) p := by
    rwa [← IsPrimitiveRoot.coe_submonoidClass_iff]
  -- the degree of the cyclotomic field is prime to `p`
  have hdvd0 : Nat.card Gal(↥Zk/k) ∣ Nat.card (ZMod p)ˣ := by
    rw [Nat.card_congr (MonoidHom.ofInjective (hζ'.autToPow_injective k)).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hp2 := hp.two_le
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hcardZ : Nat.card Gal(↥Zk/k) ∣ p - 1 := by rwa [hunits] at hdvd0
  have hZpos : 0 < Nat.card Gal(↥Zk/k) := Nat.card_pos
  have hcop : Nat.Coprime (Nat.card Gal(↥Zk/k)) p := by
    refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => ?_)
    have h1 : p ≤ Nat.card Gal(↥Zk/k) := Nat.le_of_dvd hZpos hdvd
    have h2 : Nat.card Gal(↥Zk/k) ≤ p - 1 := Nat.le_of_dvd (by omega) hcardZ
    omega
  have hcardeq : Nat.card Gal(↥Zk/k) = Module.finrank k ↥Zk :=
    IsGalois.card_aut_eq_finrank k ↥Zk
  have hcopfin : Nat.Coprime (Module.finrank k ↥Zk) p := hcardeq ▸ hcop
  -- the degree of the top field over the cyclotomic field is again `p`
  have hint : IsIntegral k ζ := Algebra.IsIntegral.isIntegral (R := k) ζ
  have hintL : IsIntegral L ζ := Algebra.IsIntegral.isIntegral (R := L) ζ
  have hmZ : Module.finrank k ↥Zk = (minpoly k ζ).natDegree := by
    rw [hZk]; exact IntermediateField.adjoin.finrank hint
  have hdL : Module.finrank L ↥L' = (minpoly L ζ).natDegree := by
    rw [hL']; exact IntermediateField.adjoin.finrank hintL
  have hdm : Module.finrank L ↥L' ≤ Module.finrank k ↥Zk := by
    rw [hmZ, hdL, ← (minpoly.monic hint).natDegree_map (algebraMap k L)]
    exact Polynomial.natDegree_le_of_dvd (minpoly.dvd_map_of_isScalarTower k L ζ)
      ((minpoly.monic hint).map (algebraMap k L)).ne_zero
  have ht1 : Module.finrank k L * Module.finrank L ↥L' = Module.finrank k ↥L' :=
    Module.finrank_mul_finrank k L ↥L'
  have ht2 : Module.finrank k ↥Zk * Module.finrank ↥Zk ↥L' = Module.finrank k ↥L' :=
    Module.finrank_mul_finrank k ↥Zk ↥L'
  have hmpos : 0 < Module.finrank k ↥Zk := Module.finrank_pos
  have hepos : 0 < Module.finrank ↥Zk ↥L' := Module.finrank_pos
  have hkey : Module.finrank k ↥Zk * Module.finrank ↥Zk ↥L' = p * Module.finrank L ↥L' := by
    rw [ht2, ← ht1, hdeg]
  have hpe : p ∣ Module.finrank ↥Zk ↥L' := by
    have hpd : p ∣ Module.finrank k ↥Zk * Module.finrank ↥Zk ↥L' := ⟨_, hkey⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hcopfin) hpd
  have hle : Module.finrank ↥Zk ↥L' ≤ p := by
    refine Nat.le_of_mul_le_mul_left ?_ hmpos
    calc Module.finrank k ↥Zk * Module.finrank ↥Zk ↥L'
        = p * Module.finrank L ↥L' := hkey
      _ ≤ p * Module.finrank k ↥Zk := Nat.mul_le_mul_left p hdm
      _ = Module.finrank k ↥Zk * p := mul_comm _ _
  have he : Module.finrank ↥Zk ↥L' = p := le_antisymm hle (Nat.le_of_dvd hepos hpe)
  -- the count upstairs, and the first inequality downstairs
  have hcard : Nat.card Gal(L/k) = p := by rw [IsGalois.card_aut_eq_finrank, hdeg]
  have hup : ((ideleDiag ↥Zk).range ⊔ (ideleNorm ↥Zk ↥L').range).index = p :=
    index_ideleDiag_sup_ideleNorm_of_prime_degree hp hζ' he
  have hdvdi := index_dvd_index_of_coprime (k := k) (L := L) (K' := ↥Zk) (L' := ↥L')
    (by rw [hcard]; exact hcop)
  rw [hup] at hdvdi
  haveI : IsCyclic Gal(L/k) := isCyclic_of_prime_card hcard
  obtain ⟨σ, hσgen⟩ := IsCyclic.exists_generator (α := Gal(L/k))
  exact le_antisymm (Nat.le_of_dvd hp.pos hdvdi) (first_inequality_index hσgen hcard)

end Ambient

/-! ### An arbitrary extension of prime degree -/

section PrimeDegree

variable {k L : Type*} [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
  [IsGalois k L] {p : ℕ}

/-- **The index of the principal ideles together with the norms from an extension of prime degree
is the degree.**  An algebraic closure of the extension carries a primitive root of unity of the
degree, which is all the descent from a cyclotomic base field needs. -/
theorem index_ideleDiag_sup_ideleNorm_eq_of_prime_degree (hp : p.Prime)
    (hdeg : Module.finrank k L = p) :
    ((ideleDiag k).range ⊔ (ideleNorm k L).range).index = p := by
  haveI : NeZero ((p : ℕ) : L) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure L) p
  exact index_ideleDiag_sup_ideleNorm_of_ambient_primitiveRoot (Ω := AlgebraicClosure L) hp hζ hdeg

end PrimeDegree

end InverseGalois.CFT
