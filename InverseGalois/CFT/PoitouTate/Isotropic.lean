/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.LocalSymbolPerfect

/-!
# Isotropic subgroups of a perfect self-pairing

A perfect pairing of a finite abelian group with itself, valued in the rationals modulo the
integers, makes the group its own group of characters.  Under that identification the elements
pairing trivially with a subgroup are the characters killing it, and those are exactly the
characters of the quotient: so **the orthogonal complement of a subgroup has as many elements as
the quotient by it**, and the two subgroups have complementary orders.

A subgroup pairing trivially with itself therefore cannot be bigger than half the group, and one
that is exactly half is its own orthogonal complement.  That is the shape of the global duality
statement for the classes of a number field modulo `p`-th powers: the global classes sit inside the
product of the local ones as a subgroup of exactly half the order, and pair trivially with
themselves by the product formula, so they are precisely their own orthogonal complement.

A pairing on a finite product of groups is assembled from pairings on the factors by multiplying
the local values.  It is nondegenerate as soon as each factor is, because a single factor can be
isolated by pairing against an element supported there.

## Main results

* `InverseGalois.CFT.card_dualAnnihilator`: the characters killing a subgroup are as many as the
  elements of the quotient by it.
* `InverseGalois.CFT.card_perpSubgroup_mul_card`: **the orthogonal complement of a subgroup under a
  perfect self-pairing has complementary order.**
* `InverseGalois.CFT.perpSubgroup_eq_self`: **a subgroup pairing trivially with itself whose order
  is the square root of the order of the group is its own orthogonal complement.**
* `InverseGalois.CFT.injective_flip_piPairing`: **a product of nondegenerate pairings is
  nondegenerate.**

## Tags

perfect pairing, Pontryagin duality, orthogonal complement, isotropic subgroup, maximal isotropic,
Poitou-Tate duality, class field theory
-/

namespace InverseGalois.CFT

/-! ### The characters killing a subgroup -/

section Annihilator

variable {A M : Type*} [CommGroup A] [CommGroup M]

/-- The characters of a group which kill a given subgroup. -/
def dualAnnihilator (V : Subgroup A) : Subgroup (A →* M) where
  carrier := {f | ∀ a ∈ V, f a = 1}
  one_mem' _ _ := rfl
  mul_mem' hf hg a ha := by simp [hf a ha, hg a ha]
  inv_mem' hf a ha := by simp [hf a ha]

@[simp]
theorem mem_dualAnnihilator {V : Subgroup A} {f : A →* M} :
    f ∈ dualAnnihilator V ↔ ∀ a ∈ V, f a = 1 := Iff.rfl

/-- The characters killing a subgroup are the characters of the quotient by it. -/
def dualAnnihilatorEquiv (V : Subgroup A) : ↥(dualAnnihilator (M := M) V) ≃ ((A ⧸ V) →* M) where
  toFun f := QuotientGroup.lift V f.1 fun x hx => f.2 x hx
  invFun g := ⟨g.comp (QuotientGroup.mk' V), fun a ha => by
    simp [(QuotientGroup.eq_one_iff a).2 ha]⟩
  left_inv f := by
    ext a
    rfl
  right_inv g := by
    ext a
    rfl

/-- The characters of a finite abelian group killing a subgroup are as many as the elements of the
quotient by that subgroup. -/
theorem card_dualAnnihilator [Finite A] (V : Subgroup A) :
    Nat.card ↥(dualAnnihilator (M := Multiplicative QModZ) V) = V.index := by
  rw [Nat.card_congr (dualAnnihilatorEquiv V), card_monoidHom_qModZ (A := A ⧸ V)]
  rfl

end Annihilator

/-! ### The orthogonal complement of a subgroup -/

section Perp

variable {A M : Type*} [CommGroup A] [CommGroup M]

/-- The elements pairing trivially with every element of a subgroup. -/
def perpSubgroup (φ : A →* A →* M) (V : Subgroup A) : Subgroup A :=
  Subgroup.comap φ.flip (dualAnnihilator V)

@[simp]
theorem mem_perpSubgroup {φ : A →* A →* M} {V : Subgroup A} {b : A} :
    b ∈ perpSubgroup φ V ↔ ∀ a ∈ V, φ a b = 1 := Iff.rfl

/-- A nondegenerate pairing of a finite abelian group with itself, valued in the rationals modulo
the integers, is perfect: every character is the pairing against an element. -/
theorem surjective_flip [Finite A] {φ : A →* A →* Multiplicative QModZ}
    (hφ : Function.Injective φ.flip) : Function.Surjective φ.flip := by
  haveI := finite_monoidHom_qModZ (A := A)
  rw [← MonoidHom.range_eq_top]
  refine Subgroup.eq_top_of_card_eq _ ?_
  have hq := Nat.card_congr (QuotientGroup.quotientKerEquivRange φ.flip).toEquiv
  rw [(MonoidHom.ker_eq_bot_iff _).2 hφ] at hq
  have hbot : Nat.card (A ⧸ (⊥ : Subgroup A)) = Nat.card A := Subgroup.index_bot
  rw [← hq, card_monoidHom_qModZ (A := A), hbot]

/-- The orthogonal complement of a subgroup under a perfect self-pairing has as many elements as
the quotient by that subgroup. -/
theorem card_perpSubgroup [Finite A] {φ : A →* A →* Multiplicative QModZ}
    (hφ : Function.Injective φ.flip) (V : Subgroup A) :
    Nat.card ↥(perpSubgroup φ V) = V.index := by
  rw [← card_dualAnnihilator V]
  refine Nat.card_congr (Equiv.ofBijective
    (fun b : ↥(perpSubgroup φ V) => (⟨φ.flip b, b.2⟩ : ↥(dualAnnihilator V))) ⟨?_, ?_⟩)
  · intro x y hxy
    exact Subtype.ext (hφ (congrArg Subtype.val hxy))
  · rintro ⟨f, hf⟩
    obtain ⟨b, rfl⟩ := surjective_flip hφ f
    exact ⟨⟨b, hf⟩, rfl⟩

/-- **A subgroup and its orthogonal complement under a perfect self-pairing have complementary
orders.** -/
theorem card_perpSubgroup_mul_card [Finite A] {φ : A →* A →* Multiplicative QModZ}
    (hφ : Function.Injective φ.flip) (V : Subgroup A) :
    Nat.card ↥(perpSubgroup φ V) * Nat.card ↥V = Nat.card A := by
  rw [card_perpSubgroup hφ V, V.index_mul_card]

/-- **A subgroup pairing trivially with itself whose order is the square root of the order of the
group is its own orthogonal complement**: the complement has the same order and contains it. -/
theorem perpSubgroup_eq_self [Finite A] {φ : A →* A →* Multiplicative QModZ}
    (hφ : Function.Injective φ.flip) {V : Subgroup A} (hle : V ≤ perpSubgroup φ V)
    (hcard : Nat.card ↥V * Nat.card ↥V = Nat.card A) : perpSubgroup φ V = V := by
  have h := card_perpSubgroup_mul_card hφ V
  rw [← hcard] at h
  have heq : Nat.card ↥(perpSubgroup φ V) = Nat.card ↥V :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  exact (Subgroup.eq_of_le_of_card_ge hle heq.le).symm

end Perp

/-! ### A pairing on a product of groups -/

section Pi

variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, CommGroup (A i)]
  {M : Type*} [CommGroup M]

/-- The pairing on a product of groups whose value is the product of the values of a family of
pairings on the factors. -/
def piPairing (φ : ∀ i, A i →* A i →* M) : (∀ i, A i) →* (∀ i, A i) →* M where
  toFun a :=
    { toFun := fun b => ∏ i, φ i (a i) (b i)
      map_one' := by simp
      map_mul' := fun b c => by simp [Finset.prod_mul_distrib] }
  map_one' := by ext b; simp
  map_mul' a a' := by ext b; simp [Finset.prod_mul_distrib]

@[simp]
theorem piPairing_apply (φ : ∀ i, A i →* A i →* M) (a b : ∀ i, A i) :
    piPairing φ a b = ∏ i, φ i (a i) (b i) := rfl

/-- **A product of nondegenerate pairings is nondegenerate**: an element pairing trivially with
everything pairs trivially with the elements supported at a single factor, which pins down its
component there. -/
theorem injective_flip_piPairing [DecidableEq ι] {φ : ∀ i, A i →* A i →* M}
    (hφ : ∀ i, Function.Injective (φ i).flip) : Function.Injective (piPairing φ).flip := by
  rw [injective_iff_map_eq_one]
  intro b hb
  funext j
  refine (injective_iff_map_eq_one (φ j).flip).1 (hφ j) (b j) ?_
  ext x
  have hx := congrArg (fun f => f (Pi.mulSingle j x)) hb
  simp only [MonoidHom.flip_apply, piPairing_apply, MonoidHom.one_apply] at hx
  rw [Finset.prod_eq_single j] at hx
  · simpa using hx
  · intro i _ hij
    rw [Pi.mulSingle_eq_of_ne hij, _root_.map_one, MonoidHom.one_apply]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end Pi

end InverseGalois.CFT
