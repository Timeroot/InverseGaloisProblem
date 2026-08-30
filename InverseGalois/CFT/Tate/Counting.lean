/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Finite
import InverseGalois.CFT.Tate.H0Norm

/-!
# A class that vanishes because the counting is tight

Two abelian groups carry commuting automorphisms, joined by an equivariant homomorphism, and the
induced map of zeroth Tate groups is surjective.  The target of that map is then finite as well,
and its order is at most the order of the source.  If moreover the target contains a class whose
order is at least the order bounding the source, the two Tate groups have the same order, so the
surjection is a bijection; and an element of the source whose image vanishes must vanish.

That is a counting argument, and it is the mechanism by which the fundamental class of a cyclic
auxiliary extension forces an element of the base to be a norm from a second extension disjoint
from it: the auxiliary extension supplies a class of the largest possible order, the second
inequality supplies the bound on the other Tate group, and the two together leave no room.

## Main results

* `InverseGalois.CFT.forall_mem_multiples_of_addEquiv`: a generator of an abelian group is carried
  to a generator by an isomorphism.
* `InverseGalois.CFT.surjective_of_mem_range_of_forall_mem_multiples`: a homomorphism whose range
  contains an element generating the target is surjective.
* `InverseGalois.CFT.tateH0.zsmul_mk_eq_zero`: the exponent annihilates the class of a fixed
  point.
* `InverseGalois.CFT.tateH0.exists_normHom_of_map_surjective`: **a fixed point whose image has the
  largest possible order is a norm**, when the induced map of Tate groups is surjective and the
  source is bounded by the exponent.

## Tags

Tate cohomology, norm, counting, fundamental class
-/

namespace InverseGalois.CFT

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] {σA : A ≃+ A} {σB : B ≃+ B} {n : ℕ}

/-- **A generator of an abelian group is carried to a generator by an isomorphism.** -/
theorem forall_mem_multiples_of_addEquiv (e : A ≃+ B) {b : A}
    (hb : ∀ z : A, z ∈ AddSubmonoid.multiples b) (w : B) :
    w ∈ AddSubmonoid.multiples (e b) := by
  obtain ⟨m, hm⟩ := hb (e.symm w)
  refine ⟨m, ?_⟩
  dsimp only at hm ⊢
  rw [← map_nsmul e m b, hm, AddEquiv.apply_symm_apply]

/-- **A homomorphism whose range contains an element generating the target is surjective.** -/
theorem surjective_of_mem_range_of_forall_mem_multiples {f : A →+ B} {b : B} (hb : b ∈ f.range)
    (hgen : ∀ z : B, z ∈ AddSubmonoid.multiples b) : Function.Surjective f := by
  intro z
  obtain ⟨m, hm⟩ := hgen z
  obtain ⟨a, ha⟩ := hb
  refine ⟨m • a, ?_⟩
  rw [map_nsmul, ha]
  exact hm

/-- The exponent annihilates the class of a fixed point: the corresponding multiple of the point
is its own norm. -/
theorem tateH0.zsmul_mk_eq_zero (x : B) (hx : σB x = x) :
    (n : ℤ) • tateH0.mk σB n x hx = 0 := by
  rw [natCast_zsmul, tateH0.nsmul_mk]
  exact (tateH0.mk_eq_zero_iff _ _).2 ⟨x, normHom_of_fixed σB n hx⟩

/-- **A fixed point whose image has the largest possible order is a norm.**  The order of the
image bounds the order of the target Tate group from below, the surjection bounds it from above by
the order of the source, and the source is bounded by the exponent, so all three agree and the
surjection is injective; the image of the class of the point is the class of a norm, hence
zero. -/
theorem tateH0.exists_normHom_of_map_surjective (f : A →+ B) (hf : ∀ a, f (σA a) = σB (f a))
    [Finite (tateH0 σA n)] (hcard : Nat.card (tateH0 σA n) ≤ n)
    (hsurj : Function.Surjective (tateH0.map (σA := σA) (σB := σB) n f hf))
    {a : A} (ha : σA a = a) {b : B} (hb : σB b = b) (hfa : f a = n • b)
    (hord : ∀ m : ℤ, m • tateH0.mk σB n b hb = 0 → (n : ℤ) ∣ m) :
    ∃ y, normHom σA n y = a := by
  haveI : Finite (tateH0 σB n) := Finite.of_surjective _ hsurj
  set x₀ : tateH0 σB n := tateH0.mk σB n b hb with hx₀
  have hdvd₁ : (n : ℤ) ∣ (addOrderOf x₀ : ℤ) :=
    hord _ (by rw [natCast_zsmul, addOrderOf_nsmul_eq_zero])
  have hdvd : n ∣ Nat.card (tateH0 σB n) :=
    dvd_trans (Int.ofNat_dvd.1 hdvd₁) (addOrderOf_dvd_natCard x₀)
  have hle₁ : n ≤ Nat.card (tateH0 σB n) := Nat.le_of_dvd Nat.card_pos hdvd
  have hle₂ : Nat.card (tateH0 σB n) ≤ Nat.card (tateH0 σA n) :=
    Nat.card_le_card_of_surjective _ hsurj
  have hEq : Nat.card (tateH0 σA n) = Nat.card (tateH0 σB n) := le_antisymm (by omega) hle₂
  have hbij : Function.Bijective (tateH0.map (σA := σA) (σB := σB) n f hf) :=
    (Nat.bijective_iff_surjective_and_card _).2 ⟨hsurj, hEq⟩
  refine (tateH0.mk_eq_zero_iff (σ := σA) a ha).1 (hbij.1 ?_)
  rw [tateH0.map_mk, map_zero]
  rw [show tateH0.mk σB n (f a) (by rw [← hf, ha]) = tateH0.mk σB n (n • b) (by rw [map_nsmul, hb])
    from by congr 1]
  exact (tateH0.mk_eq_zero_iff _ _).2 ⟨b, normHom_of_fixed σB n hb⟩

end InverseGalois.CFT
