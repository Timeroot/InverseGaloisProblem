/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConfinedWeighted
import InverseGalois.CFT.PoitouTate.LocalClassPlaces

/-!
# The second reading of a confined unit is onto

Reading a confined unit at every place outside a finite set produces a homomorphism to the free
abelian group on the places outside that set, and the descent which consumes it asks that the
homomorphism be onto.  Being onto is a statement about one place at a time: a homomorphism to a free
abelian group is onto as soon as each generator is hit.

A generator at a place `v` outside the finite set is hit by an element whose divisor is `v` minus a
prime inside the finite set of the same class.  Three demands are made of that element.  It must be
a local `n`-th power at the named places, which is what the refined class group arranges for free.
Its order must be divisible by `n` away from the places where ramification is allowed, which is
automatic where the divisor vanishes and is bought elsewhere by replacing the element by its `n`-th
power — a replacement which multiplies the order by `n` and so leaves the weighted order alone,
since that is where the reading divides by `n`.  And it must have no order at the named places,
which is why the prime it is compared with is chosen away from them.

So the finite set has to contain the named places and the places carrying the local conditions, and
to contain one prime of each refined class besides.  That last is the **correction room**, and the
refined class group being finite is what makes it small.

## Main results

* `InverseGalois.CFT.surjective_of_forall_single`: a homomorphism to a free abelian group is onto
  as soon as every generator is hit.
* `InverseGalois.CFT.confinedSWeightedOrd_eq_single`: **a confined unit whose order outside the
  finite set sits at one place, with the weight that place carries, is read as the generator
  there.**
* `InverseGalois.CFT.surjective_confinedSWeightedOrd_of_reps`: **the second reading is onto once
  every place outside the finite set has a prime of the same refined class inside it which is not
  named.**
* `InverseGalois.CFT.exists_surjective_confinedSWeightedOrd`: **such a finite set exists, stable
  under the Galois group and larger than the named places by a number the field alone decides.**

## Tags

number field, place, order, confined unit, correction room, class group, surjective
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

/-! ### Onto a free abelian group -/

section Single

/-- **A homomorphism to a free abelian group is onto as soon as every generator is hit.**  Every
element is a sum of multiples of generators, and both sums and multiples of values are values. -/
theorem surjective_of_forall_single {A ι : Type*} [AddCommGroup A]
    (f : A →+ (ι →₀ ℤ)) (h : ∀ i : ι, ∃ a : A, f a = Finsupp.single i 1) :
    Function.Surjective f := by
  intro m
  induction m using Finsupp.induction_linear with
  | zero => exact ⟨0, _root_.map_zero f⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [_root_.map_add, ha, hb]⟩
  | single i c =>
    obtain ⟨a, ha⟩ := h i
    refine ⟨c • a, ?_⟩
    rw [_root_.map_zsmul, ha]
    simp [Finsupp.smul_single]

end Single

/-! ### Reading a single place -/

section Read

variable {K : Type} [Field K] [NumberField K]
variable (n : ℕ) (Tz Y Xs T : Set (HeightOneSpectrum (𝓞 K)))

theorem confinedSWeightedOrd_apply_of_mem (b : ↥(confinedSUnits n Tz Y Xs))
    (y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) (hy : (y : HeightOneSpectrum (𝓞 K)) ∈ Y) :
    confinedSWeightedOrd n Tz Y Xs T (Additive.ofMul b) y
      = ord K (y : HeightOneSpectrum (𝓞 K))
        (((b : ↥(confinedUnits K n Tz Y)) : Kˣ) : K) :=
  confinedWeightedOrd_apply_of_mem n Tz Y T _ y hy

theorem confinedSWeightedOrd_apply_of_notMem (b : ↥(confinedSUnits n Tz Y Xs))
    (y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) (hy : (y : HeightOneSpectrum (𝓞 K)) ∉ Y) :
    confinedSWeightedOrd n Tz Y Xs T (Additive.ofMul b) y
      = ord K (y : HeightOneSpectrum (𝓞 K))
        (((b : ↥(confinedUnits K n Tz Y)) : Kˣ) : K) / (n : ℤ) :=
  confinedWeightedOrd_apply_of_notMem n Tz Y T _ y hy

open scoped Classical in
/-- **A confined unit whose order outside the finite set sits at one place, with the weight that
place carries, is read by the second reading as the generator there.**  Where ramification is
allowed the order is read as it is, so the order asked for is one; where it is not the order is
divided by the exponent, so the order asked for is the exponent. -/
theorem confinedSWeightedOrd_eq_single [NeZero n] (b : ↥(confinedSUnits n Tz Y Xs))
    {u : HeightOneSpectrum (𝓞 K)} (huT : u ∉ T)
    (hY : ∀ p ∉ T, p ∈ Y →
      ord K p (((b : ↥(confinedUnits K n Tz Y)) : Kˣ) : K) = if p = u then 1 else 0)
    (hnY : ∀ p ∉ T, p ∉ Y →
      ord K p (((b : ↥(confinedUnits K n Tz Y)) : Kˣ) : K)
        = (n : ℤ) * (if p = u then 1 else 0)) :
    confinedSWeightedOrd n Tz Y Xs T (Additive.ofMul b) = Finsupp.single ⟨u, huT⟩ 1 := by
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  refine Finsupp.ext fun y => ?_
  by_cases hyu : (y : HeightOneSpectrum (𝓞 K)) = u
  · have hsingle : (Finsupp.single (⟨u, huT⟩ : {v : HeightOneSpectrum (𝓞 K) // v ∉ T})
        (1 : ℤ)) y = 1 := by
      rw [Finsupp.single_apply,
        if_pos (Subtype.ext hyu.symm : (⟨u, huT⟩ :
          {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) = y)]
    rw [hsingle]
    by_cases hyY : (y : HeightOneSpectrum (𝓞 K)) ∈ Y
    · rw [confinedSWeightedOrd_apply_of_mem n Tz Y Xs T b y hyY,
        hY (y : HeightOneSpectrum (𝓞 K)) y.2 hyY, if_pos hyu]
    · rw [confinedSWeightedOrd_apply_of_notMem n Tz Y Xs T b y hyY,
        hnY (y : HeightOneSpectrum (𝓞 K)) y.2 hyY, if_pos hyu,
        Int.mul_ediv_cancel_left _ hn]
  · have hsingle : (Finsupp.single (⟨u, huT⟩ : {v : HeightOneSpectrum (𝓞 K) // v ∉ T})
        (1 : ℤ)) y = 0 := by
      rw [Finsupp.single_apply, if_neg fun hc => hyu (congrArg Subtype.val hc).symm]
    rw [hsingle]
    by_cases hyY : (y : HeightOneSpectrum (𝓞 K)) ∈ Y
    · rw [confinedSWeightedOrd_apply_of_mem n Tz Y Xs T b y hyY,
        hY (y : HeightOneSpectrum (𝓞 K)) y.2 hyY, if_neg hyu]
    · rw [confinedSWeightedOrd_apply_of_notMem n Tz Y Xs T b y hyY,
        hnY (y : HeightOneSpectrum (𝓞 K)) y.2 hyY, if_neg hyu, mul_zero, Int.zero_ediv]

end Read

/-! ### Onto, given a correction room -/

section Surj

variable {K : Type} [Field K] [NumberField K]
variable (n : ℕ) (Tz Y Xs T : Set (HeightOneSpectrum (𝓞 K)))

open scoped Classical in
/-- **The second reading is onto once every place outside the finite set has, inside it, a prime of
the same refined class which is not named.**  Where ramification is allowed the comparing prime is
asked to be one of those places too, and the element comparing the two serves as it is; elsewhere
its exponent-th power serves, which costs nothing because the reading divides by the exponent
exactly there. -/
theorem surjective_confinedSWeightedOrd_of_reps [NeZero n] (hXsT : Xs ⊆ T)
    (hreps : ∀ v ∉ T, ∃ w, w ∉ Xs ∧ w ∈ T ∧ (v ∈ Y → w ∈ Y) ∧
      clsLocalPlace K n Tz v = clsLocalPlace K n Tz w) :
    Function.Surjective (confinedSWeightedOrd n Tz Y Xs T) := by
  refine surjective_of_forall_single _ fun i => ?_
  obtain ⟨w, hwXs, hwT, hwY, hcls⟩ := hreps (i : HeightOneSpectrum (𝓞 K)) i.2
  obtain ⟨x, hx1, hxord⟩ := exists_ord_sub_of_clsLocalPlace_eq hcls
  have hxw : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ T →
      ord K p ((x : Kˣ) : K) = if p = (i : HeightOneSpectrum (𝓞 K)) then 1 else 0 := by
    intro p hp
    have hpw : p ≠ w := fun hc => hp (hc ▸ hwT)
    rw [hxord p, if_neg hpw, sub_zero]
  have hxXs : ∀ q : ↥Xs, ord K (q : HeightOneSpectrum (𝓞 K)) ((x : Kˣ) : K) = 0 := by
    intro q
    have hqi : (q : HeightOneSpectrum (𝓞 K)) ≠ (i : HeightOneSpectrum (𝓞 K)) :=
      fun hc => i.2 (hc ▸ hXsT q.2)
    have hqw : (q : HeightOneSpectrum (𝓞 K)) ≠ w := fun hc => hwXs (hc ▸ q.2)
    rw [hxord _, if_neg hqi, if_neg hqw, sub_zero]
  by_cases hiY : (i : HeightOneSpectrum (𝓞 K)) ∈ Y
  · have hdvd : ∀ p ∉ Y, (n : ℤ) ∣ ord K p ((x : Kˣ) : K) := by
      intro p hp
      have hpi : p ≠ (i : HeightOneSpectrum (𝓞 K)) := fun hc => hp (hc ▸ hiY)
      have hpw : p ≠ w := fun hc => hp (hc ▸ hwY hiY)
      rw [hxord p, if_neg hpi, if_neg hpw, sub_zero]
      exact dvd_zero _
    refine ⟨Additive.ofMul (⟨⟨x, mem_confinedUnits.mpr ⟨hx1, hdvd⟩⟩, hxXs⟩ :
      ↥(confinedSUnits n Tz Y Xs)), ?_⟩
    refine confinedSWeightedOrd_eq_single n Tz Y Xs T _ i.2 (fun p hp _ => hxw p hp)
      fun p hp hpY => ?_
    have hpi : p ≠ (i : HeightOneSpectrum (𝓞 K)) := fun hc => hpY (hc ▸ hiY)
    rw [hxw p hp, if_neg hpi, mul_zero]
  · have hxne : ((x : Kˣ) : K) ≠ 0 := Units.ne_zero x
    have hpow : ∀ p : HeightOneSpectrum (𝓞 K),
        ord K p (((x ^ n : Kˣ) : K)) = (n : ℤ) * ord K p ((x : Kˣ) : K) := by
      intro p
      rw [Units.val_pow_eq_pow_val, ord_pow p hxne n]
    have hx1' : ∀ v ∈ Tz, localClassHom v n (x ^ n) = 1 :=
      (mem_localPowerUnits K n Tz).mp (pow_mem ((mem_localPowerUnits K n Tz).mpr hx1) n)
    have hdvd : ∀ p ∉ Y, (n : ℤ) ∣ ord K p (((x ^ n : Kˣ) : K)) := by
      intro p _
      rw [hpow p]
      exact dvd_mul_right _ _
    have hxXs' : ∀ q : ↥Xs,
        ord K (q : HeightOneSpectrum (𝓞 K)) (((x ^ n : Kˣ) : K)) = 0 := by
      intro q
      rw [hpow _, hxXs q, mul_zero]
    refine ⟨Additive.ofMul (⟨⟨x ^ n, mem_confinedUnits.mpr ⟨hx1', hdvd⟩⟩, hxXs'⟩ :
      ↥(confinedSUnits n Tz Y Xs)), ?_⟩
    refine confinedSWeightedOrd_eq_single n Tz Y Xs T _ i.2 (fun p hp hpY => ?_)
      fun p hp _ => ?_
    · have hpi : p ≠ (i : HeightOneSpectrum (𝓞 K)) := fun hc => hiY (hc ▸ hpY)
      rw [hpow p, hxw p hp, if_neg hpi, mul_zero]
    · rw [hpow p, hxw p hp]

end Surj

/-! ### The correction room -/

section Assemble

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [Finite Gal(K/k)]
variable (n : ℕ) [NeZero n] (Tz Y Xs : Set (HeightOneSpectrum (𝓞 K)))
  [Finite ↥Tz] [IsGaloisStablePlaces k K Xs]

/-- **A finite set of places, stable under the Galois group and larger than the named places by a
number the field and its extension alone decide, outside which the second reading is onto.**  The
set is the named places, the places carrying the local conditions, and one prime for each refined
class; the last is the only part not fixed in advance, and the refined class group being finite is
what bounds it. -/
theorem exists_surjective_confinedSWeightedOrd :
    ∃ Aux : Set (HeightOneSpectrum (𝓞 K)), Aux.Finite ∧ IsGaloisStablePlaces k K Aux ∧
      Nat.card ↥Aux ≤ Nat.card Gal(K/k) * (2 * Nat.card (localIdealClass K n Tz)) ∧
      Function.Surjective (confinedSWeightedOrd n Tz Y Xs (Xs ∪ (Tz ∪ Aux))) := by
  obtain ⟨A, hAfin, hAstable, hAXs, hAcard, hAin, hAout⟩ :=
    exists_stable_localClass_reps (k := k) n Tz Xs Y
  refine ⟨A, hAfin, hAstable, hAcard, ?_⟩
  refine surjective_confinedSWeightedOrd_of_reps n Tz Y Xs (Xs ∪ (Tz ∪ A))
    Set.subset_union_left fun v hv => ?_
  have hvXs : v ∉ Xs := fun hc => hv (Set.mem_union_left _ hc)
  by_cases hvY : v ∈ Y
  · obtain ⟨w, hwA, hwY, hwc⟩ := hAin v hvY hvXs
    exact ⟨w, hAXs w hwA, Set.mem_union_right _ (Set.mem_union_right _ hwA),
      fun _ => hwY, hwc.symm⟩
  · obtain ⟨w, hwA, hwc⟩ := hAout v hvXs
    exact ⟨w, hAXs w hwA, Set.mem_union_right _ (Set.mem_union_right _ hwA),
      fun hc => absurd hc hvY, hwc.symm⟩

end Assemble

end InverseGalois.CFT
