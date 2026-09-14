/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConfinedUnits
import InverseGalois.CFT.PoitouTate.TensorDescent

/-!
# Reading a confined unit a second time, at every place outside a finite set

The obstruction to correcting a radicand to an invariant one has coefficients in the confined units
of order zero at the named places.  That group is far too large to count with: its elements may have
any order at any of the infinitely many places where ramification is allowed, so it is not finitely
generated even after dividing by the powers of the exponent.

Read it again, at **every** place outside a finite set.  The order alone is not the right reading:
a confined unit has order divisible by the exponent outside the allowed set, so the plain order is
never onto.  Divide by the exponent there.  The resulting **weighted order** is an equivariant
homomorphism onto the free abelian group on the places outside the finite set — a permutation module
— and its kernel is a group of units for a finite set of places.

## Main definitions

* `InverseGalois.CFT.confinedWeightedOrd`: **the order of a confined unit at the places outside a
  finite set, divided by the exponent where the confinement makes it divisible.**
* `InverseGalois.CFT.confinedSWeightedOrd`: the same, read on the units of order zero at the named
  places.
* `InverseGalois.CFT.confinedTUnits`: the confined units of order zero at the named places and at
  every place outside the finite set.

## Main results

* `InverseGalois.CFT.confinedWeightedOrd_smul_apply`: **the weighted order is equivariant.**
* `InverseGalois.CFT.mem_confinedTUnits_iff`: the kernel of the weighted order is the group of units
  for the finite set.
* `InverseGalois.CFT.mem_range_map_tensorSubInclRep_confinedTensorInvariantClass`: **the obstruction
  class of a confined radicand whose divisor is invariant comes from the units for the finite set.**

## Tags

number field, place, order, confined unit, permutation module, S-unit, descent, group cohomology
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Rigidity.RET TensorProduct
open groupCohomology

/-! ### The weighted order at the places outside a finite set -/

section Weighted

variable {K : Type} [Field K] [NumberField K]
variable (n : ℕ) (Tz Y T : Set (HeightOneSpectrum (𝓞 K)))

open scoped Classical in
/-- **The order of a confined unit at the places outside a finite set, divided by the exponent
where the confinement makes it divisible.**  Inside the set where ramification is allowed the order
is read as it is; outside it the confinement makes the order a multiple of the exponent, and the
multiple is what is read. -/
noncomputable def confinedWeightedOrd :
    Additive ↥(confinedUnits K n Tz Y) →+ ({v : HeightOneSpectrum (𝓞 K) // v ∉ T} →₀ ℤ) where
  toFun u := Finsupp.ofSupportFinite
    (fun y => if (y : HeightOneSpectrum (𝓞 K)) ∈ Y then
        ord K (y : HeightOneSpectrum (𝓞 K)) (((u.toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : K)
      else ord K (y : HeightOneSpectrum (𝓞 K))
        (((u.toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : K) / (n : ℤ))
    (Set.Finite.subset (finite_support_ord T (((u.toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : K))
      (by
        intro y hy hzero
        exact hy (by simp only [hzero, Int.zero_ediv, ite_self])))
  map_zero' := by
    refine Finsupp.ext fun y => ?_
    have hzero : ord K (y : HeightOneSpectrum (𝓞 K))
        ((((0 : Additive ↥(confinedUnits K n Tz Y)).toMul :
          ↥(confinedUnits K n Tz Y)) : Kˣ) : K) = 0 := by
      show ord K (y : HeightOneSpectrum (𝓞 K)) (((1 : Kˣ) : K)) = 0
      rw [Units.val_one, ord_one]
    show (if (y : HeightOneSpectrum (𝓞 K)) ∈ Y then _ else _ / (n : ℤ)) = (0 : ℤ)
    by_cases hyY : (y : HeightOneSpectrum (𝓞 K)) ∈ Y
    · rw [if_pos hyY, hzero]
    · rw [if_neg hyY, hzero, Int.zero_ediv]
  map_add' u w := by
    refine Finsupp.ext fun y => ?_
    have hmul : ord K (y : HeightOneSpectrum (𝓞 K))
        ((((u + w).toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : K)
        = ord K (y : HeightOneSpectrum (𝓞 K))
            (((u.toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : K)
          + ord K (y : HeightOneSpectrum (𝓞 K))
            (((w.toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : K) := by
      show ord K (y : HeightOneSpectrum (𝓞 K))
        (((((u.toMul : ↥(confinedUnits K n Tz Y)) : Kˣ)
          * ((w.toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : Kˣ)) : K) = _
      rw [Units.val_mul, ord_mul _ (Units.ne_zero _) (Units.ne_zero _)]
    show (if (y : HeightOneSpectrum (𝓞 K)) ∈ Y then _ else _ / (n : ℤ))
      = (if (y : HeightOneSpectrum (𝓞 K)) ∈ Y then _ else _ / (n : ℤ))
        + (if (y : HeightOneSpectrum (𝓞 K)) ∈ Y then _ else _ / (n : ℤ))
    by_cases hyY : (y : HeightOneSpectrum (𝓞 K)) ∈ Y
    · rw [if_pos hyY, if_pos hyY, if_pos hyY, hmul]
    · have hdvd : (n : ℤ) ∣ ord K (y : HeightOneSpectrum (𝓞 K))
          (((u.toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : K) :=
        (mem_confinedUnits.1 (u.toMul : ↥(confinedUnits K n Tz Y)).2).2
          (y : HeightOneSpectrum (𝓞 K)) hyY
      rw [if_neg hyY, if_neg hyY, if_neg hyY, hmul, Int.add_ediv_of_dvd_left hdvd]

open scoped Classical in
@[simp]
theorem confinedWeightedOrd_apply_of_mem (u : Additive ↥(confinedUnits K n Tz Y))
    (y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) (hy : (y : HeightOneSpectrum (𝓞 K)) ∈ Y) :
    confinedWeightedOrd n Tz Y T u y = ord K (y : HeightOneSpectrum (𝓞 K))
      (((u.toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : K) := by
  show (if (y : HeightOneSpectrum (𝓞 K)) ∈ Y then _ else _ / (n : ℤ)) = _
  rw [if_pos hy]

open scoped Classical in
@[simp]
theorem confinedWeightedOrd_apply_of_notMem (u : Additive ↥(confinedUnits K n Tz Y))
    (y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) (hy : (y : HeightOneSpectrum (𝓞 K)) ∉ Y) :
    confinedWeightedOrd n Tz Y T u y = ord K (y : HeightOneSpectrum (𝓞 K))
      (((u.toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : K) / (n : ℤ) := by
  show (if (y : HeightOneSpectrum (𝓞 K)) ∈ Y then _ else _ / (n : ℤ)) = _
  rw [if_neg hy]

/-- **The weighted order vanishes at a place exactly when the order does.**  Where the exponent
divides, a vanishing quotient forces a vanishing order. -/
theorem confinedWeightedOrd_apply_eq_zero_iff (u : Additive ↥(confinedUnits K n Tz Y))
    (y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) :
    confinedWeightedOrd n Tz Y T u y = 0 ↔ ord K (y : HeightOneSpectrum (𝓞 K))
      (((u.toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : K) = 0 := by
  by_cases hyY : (y : HeightOneSpectrum (𝓞 K)) ∈ Y
  · rw [confinedWeightedOrd_apply_of_mem n Tz Y T u y hyY]
  · rw [confinedWeightedOrd_apply_of_notMem n Tz Y T u y hyY]
    obtain ⟨c, hc⟩ := (mem_confinedUnits.1 (u.toMul : ↥(confinedUnits K n Tz Y)).2).2
      (y : HeightOneSpectrum (𝓞 K)) hyY
    rcases eq_or_ne (n : ℤ) 0 with hn | hn
    · rw [hc, hn, zero_mul, Int.zero_ediv]
    · rw [hc, Int.mul_ediv_cancel_left _ hn]
      exact ⟨fun h => by rw [h, mul_zero], fun h => by
        rcases mul_eq_zero.1 h with h' | h'
        · exact absurd h' hn
        · exact h'⟩

end Weighted

/-! ### Equivariance -/

section Equivariant

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K]
variable (n : ℕ) (Tz Y T : Set (HeightOneSpectrum (𝓞 K)))
variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y]
  [IsGaloisStablePlaces k K T]

/-- The order of a translated confined unit at a place is its order at the place translated
back. -/
theorem ord_coe_smul_confinedUnits (σ : Gal(K/k)) (a : ↥(confinedUnits K n Tz Y))
    (v : HeightOneSpectrum (𝓞 K)) :
    ord K v (((σ • a : ↥(confinedUnits K n Tz Y)) : Kˣ) : K)
      = ord K (σ⁻¹ • v) (((a : ↥(confinedUnits K n Tz Y)) : Kˣ) : K) := by
  rw [coe_smul_stableSubgroup]
  have h := ord_galSmul σ (σ⁻¹ • v) (((a : ↥(confinedUnits K n Tz Y)) : Kˣ) : K)
  rwa [smul_inv_smul] at h

/-- **The weighted order is equivariant**: the weighted order of a translated confined unit at a
place is its weighted order at the place translated back.  The set where ramification is allowed is
stable, so the two readings use the same weight. -/
theorem confinedWeightedOrd_smul_apply (σ : Gal(K/k)) (a : ↥(confinedUnits K n Tz Y))
    (y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) :
    confinedWeightedOrd n Tz Y T (Additive.ofMul (σ • a)) y
      = confinedWeightedOrd n Tz Y T (Additive.ofMul a) (σ⁻¹ • y) := by
  have hmem : ((σ⁻¹ • y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) :
      HeightOneSpectrum (𝓞 K)) ∈ Y ↔ (y : HeightOneSpectrum (𝓞 K)) ∈ Y := by
    rw [coe_smul_outsidePlaces]
    exact IsGaloisStablePlaces.smul_mem_iff (k := k) σ⁻¹ (y : HeightOneSpectrum (𝓞 K))
  have hord := ord_coe_smul_confinedUnits n Tz Y σ a (y : HeightOneSpectrum (𝓞 K))
  by_cases hyY : (y : HeightOneSpectrum (𝓞 K)) ∈ Y
  · rw [confinedWeightedOrd_apply_of_mem n Tz Y T _ y hyY,
      confinedWeightedOrd_apply_of_mem n Tz Y T _ _ (hmem.2 hyY), coe_smul_outsidePlaces]
    exact hord
  · rw [confinedWeightedOrd_apply_of_notMem n Tz Y T _ y hyY,
      confinedWeightedOrd_apply_of_notMem n Tz Y T _ _ (fun hc => hyY (hmem.1 hc)),
      coe_smul_outsidePlaces]
    exact congrArg (fun z : ℤ => z / (n : ℤ)) hord

end Equivariant

/-! ### The units for the finite set -/

section Units

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K]
variable (n : ℕ) (Tz Y Xs T : Set (HeightOneSpectrum (𝓞 K)))

/-- **The weighted order read on the confined units of order zero at the named places.** -/
noncomputable def confinedSWeightedOrd :
    Additive ↥(confinedSUnits n Tz Y Xs) →+ ({v : HeightOneSpectrum (𝓞 K) // v ∉ T} →₀ ℤ) :=
  (confinedWeightedOrd n Tz Y T).comp
    (MonoidHom.toAdditive (confinedSUnits n Tz Y Xs).subtype)

theorem confinedSWeightedOrd_apply (u : Additive ↥(confinedSUnits n Tz Y Xs)) :
    confinedSWeightedOrd n Tz Y Xs T u
      = confinedWeightedOrd n Tz Y T (Additive.ofMul
        ((u.toMul : ↥(confinedSUnits n Tz Y Xs)) : ↥(confinedUnits K n Tz Y))) := rfl

/-- **The confined units of order zero at the named places and at every place outside a finite
set.** -/
def confinedTUnits : Subgroup ↥(confinedSUnits n Tz Y Xs) where
  carrier := {x | ∀ y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
    ord K (y : HeightOneSpectrum (𝓞 K))
      (((x : ↥(confinedSUnits n Tz Y Xs)) : ↥(confinedUnits K n Tz Y)) : Kˣ) = 0}
  mul_mem' {x y} hx hy z := by
    show ord K (z : HeightOneSpectrum (𝓞 K))
      ((((x : ↥(confinedSUnits n Tz Y Xs)) : ↥(confinedUnits K n Tz Y)) : Kˣ)
        * (((y : ↥(confinedSUnits n Tz Y Xs)) : ↥(confinedUnits K n Tz Y)) : Kˣ) : Kˣ) = 0
    rw [Units.val_mul, ord_mul _ (Units.ne_zero _) (Units.ne_zero _), hx z, hy z, add_zero]
  one_mem' z := by
    show ord K (z : HeightOneSpectrum (𝓞 K)) (((1 : Kˣ) : K)) = 0
    rw [Units.val_one, ord_one]
  inv_mem' {x} hx z := by
    show ord K (z : HeightOneSpectrum (𝓞 K))
      (((((x : ↥(confinedSUnits n Tz Y Xs)) : ↥(confinedUnits K n Tz Y)) : Kˣ)⁻¹ : Kˣ) : K) = 0
    rw [Units.val_inv_eq_inv_val, ord_inv, hx z, neg_zero]

/-- **The kernel of the weighted order is the group of units for the finite set.** -/
theorem mem_confinedTUnits_iff (a : ↥(confinedSUnits n Tz Y Xs)) :
    a ∈ confinedTUnits n Tz Y Xs T ↔
      confinedSWeightedOrd n Tz Y Xs T (Additive.ofMul a) = 0 := by
  rw [confinedSWeightedOrd_apply]
  refine ⟨fun h => Finsupp.ext fun y => ?_, fun h y => ?_⟩
  · simp only [Finsupp.coe_zero, Pi.zero_apply]
    rw [confinedWeightedOrd_apply_eq_zero_iff]
    exact h y
  · have h2 := congrArg
      (fun z : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} →₀ ℤ => z y) h
    simp only [Finsupp.coe_zero, Pi.zero_apply] at h2
    exact (confinedWeightedOrd_apply_eq_zero_iff n Tz Y T _ y).1 h2

variable [Finite ↥Xs] [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y]
  [IsGaloisStablePlaces k K Xs] [IsGaloisStablePlaces k K T]

/-- **The units for the finite set are carried into themselves by the Galois group.** -/
instance isStableSubgroup_confinedTUnits :
    IsStableSubgroup Gal(K/k) (confinedTUnits n Tz Y Xs T) where
  smul_mem σ {a} ha := fun y => by
    have hcoe : (((σ • a : ↥(confinedSUnits n Tz Y Xs)) :
        ↥(confinedUnits K n Tz Y)) : Kˣ)
        = ((σ • ((a : ↥(confinedSUnits n Tz Y Xs)) :
          ↥(confinedUnits K n Tz Y)) : ↥(confinedUnits K n Tz Y)) : Kˣ) := by
      rw [coe_smul_stableSubgroup]
    rw [hcoe]
    exact (ord_coe_smul_confinedUnits n Tz Y σ _ (y : HeightOneSpectrum (𝓞 K))).trans
      (ha ⟨σ⁻¹ • (y : HeightOneSpectrum (𝓞 K)), fun hc => y.2
        ((IsGaloisStablePlaces.smul_mem_iff (k := k) (T := T) σ⁻¹
          (y : HeightOneSpectrum (𝓞 K))).1 hc)⟩)

end Units

/-! ### The obstruction read at the units for the finite set -/

section Descent

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [Finite Gal(K/k)]
variable (n : ℕ) (Tz Y Xs T : Set (HeightOneSpectrum (𝓞 K))) [Finite ↥Xs]
variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y]
  [IsGaloisStablePlaces k K Xs] [IsGaloisStablePlaces k K T]
variable {C : Type} [CommGroup C] [MulDistribMulAction Gal(K/k) C]

open scoped Classical in
/-- **The obstruction class of a confined radicand whose divisor is invariant comes from the units
for the finite set.**

The named places are read first and the obstruction lives on the units of order zero there; reading
those again, at every place outside a finite set, cuts them down to the units for that set.  Nothing
is asked at the places of the second reading: the cocycle is the difference between a translate of
the radicand and the radicand, so its order at a place fixed by an automorphism is already a
coboundary.  All that is asked is that the second reading be onto. -/
theorem mem_range_map_tensorSubInclRep_confinedTensorInvariantClass
    (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    (hsurjT : Function.Surjective (confinedSWeightedOrd n Tz Y Xs T))
    {t : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C}
    (ht : ∀ σ : Gal(K/k), tensorVal C (confinedOrd n Tz Y Xs) (σ • t)
      = tensorVal C (confinedOrd n Tz Y Xs) t) :
    tensorInvariantClass C (confinedOrd n Tz Y Xs) (confinedSUnits n Tz Y Xs) hsurj
        (mem_confinedSUnits_iff n Tz Y Xs) ht ∈
      LinearMap.range (groupCohomology.map (MonoidHom.id Gal(K/k))
        (A := Rep.ofDistribMulAction ℤ Gal(K/k)
          (Additive ↥(confinedTUnits n Tz Y Xs T) ⊗[ℤ] Additive C))
        (tensorSubInclRep Gal(K/k) C (confinedTUnits n Tz Y Xs T)) 1).hom :=
  mem_range_map_tensorSubInclRep_tensorInvariantClass C (confinedOrd n Tz Y Xs)
    (confinedSUnits n Tz Y Xs) (confinedWeightedOrd n Tz Y T)
    (confinedSWeightedOrd n Tz Y Xs T) (confinedTUnits n Tz Y Xs T) (fun _ => rfl) hsurjT
    (mem_confinedTUnits_iff n Tz Y Xs T) (confinedWeightedOrd_smul_apply n Tz Y T) hsurj
    (mem_confinedSUnits_iff n Tz Y Xs) ht

end Descent

end InverseGalois.CFT
