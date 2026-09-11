/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.Layer

/-!
# A layer as a power of the roots of unity

Twisted Kummer theory reads the first cohomology of a Galois group with coefficients in a finite
module killed by a prime, and what it asks of those coefficients is that they be a finite power of
the group of roots of unity of that order.  A layer of the descending central series of a finite
group is exactly such a module: it is abelian, killed by the prime, and finite, so choosing a basis
of it over the field with that many elements writes it as a finite power of any group of that prime
order — in particular of the roots of unity, once they lie in the field being worked over.

The identification is not canonical, and nothing below asks it to be.  What matters is that one is
named once and for all, so that the arithmetic hypotheses which mention it can be stated.

## Main definitions

* `InverseGalois.Shafarevich.layerPiMulEquiv`: **a layer is a finite power of any group of prime
  order**, the prime being the one the central series is taken at.

## Main results

* `InverseGalois.Shafarevich.layerSub_pow_eq_one`: every element of a layer is killed by the prime.

## Tags

p-central series, elementary abelian, Kummer theory, roots of unity
-/

namespace InverseGalois.Shafarevich

section Pi

variable (ℓ : ℕ) [Fact ℓ.Prime] (P : Type*) [Group P] (j : ℕ)

omit [Fact ℓ.Prime] in
/-- **Every element of a layer is killed by the prime.** -/
theorem layerSub_pow_eq_one (e : ↥(layerSub ℓ P j)) : e ^ ℓ = 1 :=
  Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact pow_eq_one_of_mem_layerSub e.2)

variable [Finite P] (M : Type*) [CommGroup M] (hM : Nat.card M = ℓ)

include hM in
/-- **A layer is a finite power of any group whose order is the prime the central series is taken
at.**  The layer is a finite vector space over the field with that many elements, and a group of
that prime order is a one dimensional such space, so a basis of the layer writes it as a power of
the group indexed by the basis. -/
noncomputable def layerPiMulEquiv :
    ↥(layerSub ℓ P j) ≃* (Fin (Module.finrank (ZMod ℓ) (Layer ℓ P j)) → M) :=
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hZ : Nat.card (Multiplicative (ZMod ℓ)) = ℓ := by simp [Nat.card_eq_fintype_card]
  let eM : ZMod ℓ ≃+ Additive M :=
    AddEquiv.toMultiplicativeLeft.symm (mulEquivOfPrimeCardEq hZ hM)
  let e1 : Layer ℓ P j ≃+ (Fin (Module.finrank (ZMod ℓ) (Layer ℓ P j)) → ZMod ℓ) :=
    (Module.finBasis (ZMod ℓ) (Layer ℓ P j)).equivFun.toAddEquiv
  let e2 : (Fin (Module.finrank (ZMod ℓ) (Layer ℓ P j)) → ZMod ℓ) ≃+
      (Fin (Module.finrank (ZMod ℓ) (Layer ℓ P j)) → Additive M) :=
    AddEquiv.piCongrRight fun _ => eM
  let e3 : (Fin (Module.finrank (ZMod ℓ) (Layer ℓ P j)) → Additive M) ≃+
      Additive (Fin (Module.finrank (ZMod ℓ) (Layer ℓ P j)) → M) :=
    ⟨Equiv.refl _, fun _ _ => rfl⟩
  MulEquiv.toAdditive.symm ((e1.trans e2).trans e3)

end Pi

end InverseGalois.Shafarevich
