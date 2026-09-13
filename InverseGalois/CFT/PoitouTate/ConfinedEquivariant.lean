/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConfinedUnits
import InverseGalois.CFT.PoitouTate.TensorEquivariant

/-!
# The obstruction carried by a confined radicand, and the units that retire it

A tensor of confined units with a module whose valuation at the named places is invariant carries
an obstruction to being invariant itself.  The obstruction is a one cocycle with coefficients in
the confined units without order at the named places, and it vanishes exactly when the tensor may
be corrected to an invariant one with the same valuation.

**The obstruction is retired by one unit per named place**: a confined unit of order one at that
place and none at the other named ones, fixed by the automorphisms fixing the place.  The vector
of orders of a confined unit is equivariant, so such a family of units is a splitting of the
valuation carried by the action, and a splitting carried by the action kills the obstruction of
every tensor with invariant valuation.

At a place no automorphism but the identity fixes, the unit is free: the vector of orders is onto,
so a unit of order one there and none elsewhere exists, and there is nothing for it to be fixed by.
So the arithmetic is spent only at the places with a decomposition group.

The splitting is read after tensoring with the module, which the exponent kills, so the orders of
the unit are only ever asked for **up to a multiple of the exponent**.

## Main results

* `InverseGalois.CFT.tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer`: **one confined unit
  per named place, of order one there and none elsewhere and fixed by the automorphisms fixing the
  place, kills the obstruction.**
* `InverseGalois.CFT.tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_nontrivial`: the same,
  with the unit asked for only at the places some automorphism other than the identity fixes.
* `InverseGalois.CFT.tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod`,
  `InverseGalois.CFT.tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod_nontrivial`: **the
  orders of the unit are only asked for up to the exponent of the module.**

## Tags

group cohomology, S-unit, confined unit, divisor, decomposition group, obstruction
-/

set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField TensorProduct groupCohomology

/-! ### The units that retire the obstruction -/

section Confined

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K]
variable {C : Type} [CommGroup C] [MulDistribMulAction Gal(K/k) C]
variable (n : ℕ) (Tz Y Xs : Set (HeightOneSpectrum (𝓞 K)))
variable [Finite ↥Xs] [DecidableEq ↥Xs]
variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y] [IsGaloisStablePlaces k K Xs]

/-- **One confined unit per named place, of order one there and none at the other named places and
fixed by the automorphisms fixing it, kills the obstruction** of every tensor whose valuation is
invariant.

The vector of orders of a confined unit is equivariant, so the unit belonging to a place carries
with it the unit belonging to every place of the same orbit, and the family so assembled is a
splitting of the vector of orders carried by the action. -/
theorem tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer
    (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    (hstab : ∀ y : ↥Xs, ∃ u : ↥(confinedUnits K n Tz Y),
      confinedOrd n Tz Y Xs (Additive.ofMul u) = Finsupp.single y 1 ∧
        ∀ σ : Gal(K/k), σ • y = y → σ • u = u)
    {t : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C}
    (ht : ∀ σ : Gal(K/k), tensorVal C (confinedOrd n Tz Y Xs) (σ • t)
      = tensorVal C (confinedOrd n Tz Y Xs) t) :
    tensorInvariantClass C (confinedOrd n Tz Y Xs) (confinedSUnits n Tz Y Xs) hsurj
      (mem_confinedSUnits_iff n Tz Y Xs) ht = 0 :=
  tensorInvariantClass_eq_zero_of_stabilizer C (confinedOrd n Tz Y Xs)
    (confinedSUnits n Tz Y Xs) hsurj (mem_confinedSUnits_iff n Tz Y Xs)
    (confinedOrd_smul_apply n Tz Y Xs) hstab ht

/-- **The unit is only asked for at the places some automorphism other than the identity fixes.**

Where no automorphism but the identity fixes the place, the vector of orders being onto already
supplies a confined unit of order one there and none at the other named places, and the condition
that the automorphisms fixing the place fix the unit asks nothing of it. -/
theorem tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_nontrivial
    (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    (hstab : ∀ y : ↥Xs, (∃ σ : Gal(K/k), σ ≠ 1 ∧ σ • y = y) →
      ∃ u : ↥(confinedUnits K n Tz Y),
        confinedOrd n Tz Y Xs (Additive.ofMul u) = Finsupp.single y 1 ∧
          ∀ σ : Gal(K/k), σ • y = y → σ • u = u)
    {t : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C}
    (ht : ∀ σ : Gal(K/k), tensorVal C (confinedOrd n Tz Y Xs) (σ • t)
      = tensorVal C (confinedOrd n Tz Y Xs) t) :
    tensorInvariantClass C (confinedOrd n Tz Y Xs) (confinedSUnits n Tz Y Xs) hsurj
      (mem_confinedSUnits_iff n Tz Y Xs) ht = 0 := by
  refine tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer n Tz Y Xs hsurj
    (fun y => ?_) ht
  by_cases hy : ∃ σ : Gal(K/k), σ ≠ 1 ∧ σ • y = y
  · exact hstab y hy
  · push_neg at hy
    obtain ⟨a, ha⟩ := hsurj (Finsupp.single y 1)
    refine ⟨a.toMul, ha, fun σ hσ => ?_⟩
    have hσ1 : σ = 1 := by
      by_contra hc
      exact hy σ hc hσ
    rw [hσ1, one_smul]

/-- **The orders of the unit are only asked for up to the exponent.**

The splitting of the vector of orders is used only after tensoring with a module killed by the
exponent, so a unit whose order at its own named place is one and at the other named places is
zero, each up to a multiple of the exponent, serves just as well as one with those orders on the
nose. -/
theorem tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod (hexp : ∀ c : C, c ^ n = 1)
    (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    (hstab : ∀ y : ↥Xs, ∃ u : ↥(confinedUnits K n Tz Y),
      (∀ z : ↥Xs, (n : ℤ) ∣ confinedOrd n Tz Y Xs (Additive.ofMul u) z - Finsupp.single y 1 z) ∧
        ∀ σ : Gal(K/k), σ • y = y → σ • u = u)
    {t : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C}
    (ht : ∀ σ : Gal(K/k), tensorVal C (confinedOrd n Tz Y Xs) (σ • t)
      = tensorVal C (confinedOrd n Tz Y Xs) t) :
    tensorInvariantClass C (confinedOrd n Tz Y Xs) (confinedSUnits n Tz Y Xs) hsurj
      (mem_confinedSUnits_iff n Tz Y Xs) ht = 0 :=
  tensorInvariantClass_eq_zero_of_stabilizer_mod C (confinedOrd n Tz Y Xs)
    (confinedSUnits n Tz Y Xs) hsurj (mem_confinedSUnits_iff n Tz Y Xs)
    (confinedOrd_smul_apply n Tz Y Xs) n hexp hstab ht

/-- **The unit is only asked for, and only up to the exponent, at the places some automorphism
other than the identity fixes.**

Where no automorphism but the identity fixes the place, the vector of orders being onto already
supplies a confined unit of order one there and none at the other named places, and the condition
that the automorphisms fixing the place fix the unit asks nothing of it. -/
theorem tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod_nontrivial
    (hexp : ∀ c : C, c ^ n = 1) (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    (hstab : ∀ y : ↥Xs, (∃ σ : Gal(K/k), σ ≠ 1 ∧ σ • y = y) →
      ∃ u : ↥(confinedUnits K n Tz Y),
        (∀ z : ↥Xs, (n : ℤ) ∣ confinedOrd n Tz Y Xs (Additive.ofMul u) z - Finsupp.single y 1 z) ∧
          ∀ σ : Gal(K/k), σ • y = y → σ • u = u)
    {t : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C}
    (ht : ∀ σ : Gal(K/k), tensorVal C (confinedOrd n Tz Y Xs) (σ • t)
      = tensorVal C (confinedOrd n Tz Y Xs) t) :
    tensorInvariantClass C (confinedOrd n Tz Y Xs) (confinedSUnits n Tz Y Xs) hsurj
      (mem_confinedSUnits_iff n Tz Y Xs) ht = 0 := by
  refine tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod n Tz Y Xs hexp hsurj
    (fun y => ?_) ht
  by_cases hy : ∃ σ : Gal(K/k), σ ≠ 1 ∧ σ • y = y
  · exact hstab y hy
  · push_neg at hy
    obtain ⟨a, ha⟩ := hsurj (Finsupp.single y 1)
    refine ⟨a.toMul, fun z => ?_, fun σ hσ => ?_⟩
    · show (n : ℤ) ∣ confinedOrd n Tz Y Xs a z - Finsupp.single y 1 z
      rw [ha, sub_self]
      exact dvd_zero _
    · have hσ1 : σ = 1 := by
        by_contra hc
        exact hy σ hc hσ
      rw [hσ1, one_smul]

end Confined

end InverseGalois.CFT
