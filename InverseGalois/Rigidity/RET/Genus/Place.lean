/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.OrdValuation

/-!
# Places of a function field and the primes of a chart

A *place* of a field `F` is a valuation subring of `F` other than `F` itself: a local ring of
functions "regular at a point", the point being invisible and the ring standing in for it.  A
*chart* is a Dedekind subring `B` with fraction field `F`; its height-one primes are the points
visible in that chart.

The two descriptions agree.  Every height-one prime of the chart gives a place — the functions of
non-negative order there — and conversely every place containing the chart comes from exactly one
prime of it, namely the prime of functions of the chart that vanish at the place.  The point of the
correspondence is that the left-hand side does not mention the chart: a place is an intrinsic
object, so places found in different charts can be compared, which is what a divisor on a curve
needs.

The proof that a place containing the chart is the local ring of its prime uses the local
description of functions of non-negative order at a prime
(`Rigidity.RET.exists_den_notMem_of_ord_nonneg`): such a function is a fraction whose denominator
avoids the prime, hence is a unit of the place, so the fraction lies in the place.  Conversely a
function of negative order has an inverse lying in the maximal ideal of the place, so it cannot
itself lie in the place.

## Main definitions

* `Rigidity.RET.placeSubring` — the place attached to a height-one prime of a chart.
* `Rigidity.RET.underPrime` — the prime of the chart under a place containing it.
* `Rigidity.RET.underPlace` — that prime, packaged as a point of the height-one spectrum.

## Main results

* `Rigidity.RET.placeSubring_injective` — distinct primes give distinct places.
* `Rigidity.RET.placeSubring_underPlace` — a place containing the chart is the place of its prime.
* `Rigidity.RET.underPlace_placeSubring` — the prime under the place of a prime is that prime.
-/

open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section


namespace Rigidity.RET

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

/-! ## The place of a prime -/

variable (F : Type*) [Field F] [Algebra B F] [IsFractionRing B F]

/-- **The place attached to a height-one prime of a chart**: the functions of non-negative order
there. -/
def placeSubring (v : HeightOneSpectrum B) : ValuationSubring F := (v.valuation F).valuationSubring

theorem mem_placeSubring_iff_valuation (v : HeightOneSpectrum B) (x : F) :
    x ∈ placeSubring F v ↔ v.valuation F x ≤ 1 := Iff.rfl

/-- **A function lies in the place of a prime exactly when its order there is non-negative.** -/
theorem mem_placeSubring (v : HeightOneSpectrum B) {x : F} (hx : x ≠ 0) :
    x ∈ placeSubring F v ↔ 0 ≤ ord F v x :=
  valuation_le_one_iff_ord_nonneg F v hx

/-- The chart is contained in every one of its places. -/
theorem algebraMap_mem_placeSubring (v : HeightOneSpectrum B) (b : B) :
    algebraMap B F b ∈ placeSubring F v :=
  IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := F) v b

/-- A place is a proper subring: some function has a pole at the prime. -/
theorem placeSubring_ne_top (v : HeightOneSpectrum B) : placeSubring F v ≠ ⊤ := by
  rw [Ne, placeSubring, Valuation.valuationSubring_eq_top_iff, not_not]
  infer_instance

/-- **Distinct primes of a chart give distinct places.** -/
theorem placeSubring_injective : Function.Injective (placeSubring F (B := B)) := fun _ _ h =>
  IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
    ((Valuation.isEquiv_iff_valuationSubring _ _).mpr h)

/-! ## The prime under a place -/

variable {F}

/-- **The prime of the chart under a place**: the functions of the chart vanishing at the place. -/
def underPrime (A : ValuationSubring F) (hBA : ∀ b : B, algebraMap B F b ∈ A) : Ideal B where
  carrier := {b : B | A.valuation (algebraMap B F b) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    show A.valuation (algebraMap B F (a + b)) < 1
    rw [map_add]
    exact A.valuation.map_add_lt ha hb
  smul_mem' := by
    intro c b hb
    show A.valuation (algebraMap B F (c • b)) < 1
    have hc : A.valuation (algebraMap B F c) ≤ 1 :=
      A.valuation_le_one ⟨algebraMap B F c, hBA c⟩
    rw [smul_eq_mul, map_mul, Valuation.map_mul]
    calc A.valuation (algebraMap B F c) * A.valuation (algebraMap B F b)
        ≤ 1 * A.valuation (algebraMap B F b) := mul_le_mul_left hc _
      _ = A.valuation (algebraMap B F b) := one_mul _
      _ < 1 := hb

omit [IsDedekindDomain B] [IsFractionRing B F] in
@[simp]
theorem mem_underPrime {A : ValuationSubring F} {hBA : ∀ b : B, algebraMap B F b ∈ A} {b : B} :
    b ∈ underPrime A hBA ↔ A.valuation (algebraMap B F b) < 1 := Iff.rfl

omit [IsDedekindDomain B] [IsFractionRing B F] in
/-- An element of the chart outside the prime has valuation one: it is a unit of the place. -/
theorem valuation_eq_one_of_notMem_underPrime {A : ValuationSubring F}
    {hBA : ∀ b : B, algebraMap B F b ∈ A} {b : B} (hb : b ∉ underPrime A hBA) :
    A.valuation (algebraMap B F b) = 1 :=
  le_antisymm (A.valuation_le_one ⟨algebraMap B F b, hBA b⟩) (not_lt.mp (mem_underPrime.not.mp hb))

omit [IsDedekindDomain B] [IsFractionRing B F] in
theorem underPrime_isPrime (A : ValuationSubring F) (hBA : ∀ b : B, algebraMap B F b ∈ A) :
    (underPrime A hBA).IsPrime := by
  constructor
  · intro htop
    have h1 : (1 : B) ∈ underPrime A hBA := by rw [htop]; trivial
    rw [mem_underPrime, map_one, map_one] at h1
    exact absurd h1 (lt_irrefl 1)
  · intro x y hxy
    by_contra hcon
    push_neg at hcon
    obtain ⟨hx, hy⟩ := hcon
    rw [mem_underPrime, map_mul, Valuation.map_mul,
      valuation_eq_one_of_notMem_underPrime hx, valuation_eq_one_of_notMem_underPrime hy,
      one_mul] at hxy
    exact absurd hxy (lt_irrefl 1)

/-- **A proper place has a genuine prime under it.**  A function outside the place is a fraction
whose denominator must then vanish at the place. -/
theorem underPrime_ne_bot (A : ValuationSubring F) (hBA : ∀ b : B, algebraMap B F b ∈ A)
    (hA : A ≠ ⊤) : underPrime A hBA ≠ ⊥ := by
  -- a function outside the place
  obtain ⟨y, hy⟩ : ∃ y : F, y ∉ A := by
    by_contra hcon
    push_neg at hcon
    exact hA (ValuationSubring.ext _ _ fun x => ⟨fun _ => trivial, fun _ => hcon x⟩)
  have hyv : 1 < A.valuation y := not_le.mp (fun h => hy (A.mem_of_valuation_le_one y h))
  -- write it as a fraction of elements of the chart
  obtain ⟨⟨a, b, hb⟩, hab⟩ := IsLocalization.surj B⁰ y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hva : A.valuation (algebraMap B F a) ≤ 1 := A.valuation_le_one ⟨_, hBA a⟩
  have hmul : A.valuation y * A.valuation (algebraMap B F b) = A.valuation (algebraMap B F a) := by
    rw [← Valuation.map_mul]
    exact congrArg A.valuation hab
  -- the denominator vanishes at the place
  have hbmem : b ∈ underPrime A hBA := by
    rw [mem_underPrime]
    by_contra hle
    push_neg at hle
    have hb1 : A.valuation (algebraMap B F b) = 1 :=
      le_antisymm (A.valuation_le_one ⟨_, hBA b⟩) hle
    rw [hb1, mul_one] at hmul
    exact absurd (hmul ▸ hyv) (not_lt.mpr hva)
  intro hbot
  rw [hbot] at hbmem
  exact hb0 (Ideal.mem_bot.mp hbmem)

/-- **The point of the height-one spectrum under a proper place containing the chart.** -/
def underPlace (A : ValuationSubring F) (hBA : ∀ b : B, algebraMap B F b ∈ A) (hA : A ≠ ⊤) :
    HeightOneSpectrum B where
  asIdeal := underPrime A hBA
  isPrime := underPrime_isPrime A hBA
  ne_bot := underPrime_ne_bot A hBA hA

@[simp]
theorem underPlace_asIdeal (A : ValuationSubring F) (hBA : ∀ b : B, algebraMap B F b ∈ A)
    (hA : A ≠ ⊤) : (underPlace A hBA hA).asIdeal = underPrime A hBA := rfl

/-! ## The classification -/

/-- **A place containing the chart is the place of its prime.** -/
theorem placeSubring_underPlace (A : ValuationSubring F) (hBA : ∀ b : B, algebraMap B F b ∈ A)
    (hA : A ≠ ⊤) : placeSubring F (underPlace A hBA hA) = A := by
  set v := underPlace A hBA hA with hv
  refine ValuationSubring.ext _ _ fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · -- a function of non-negative order is a fraction with denominator a unit of the place
    rcases eq_or_ne x 0 with rfl | hx0
    · exact A.zero_mem
    obtain ⟨a, s, hs, hsa⟩ :=
      exists_den_notMem_of_ord_nonneg F v ((mem_placeSubring F v hx0).mp hx)
    have hs1 : A.valuation (algebraMap B F s) = 1 :=
      valuation_eq_one_of_notMem_underPrime (hBA := hBA) hs
    have hval : A.valuation x = A.valuation (algebraMap B F a) := by
      have := congrArg A.valuation hsa
      rwa [Valuation.map_mul, hs1, one_mul] at this
    exact A.mem_of_valuation_le_one x (hval ▸ A.valuation_le_one ⟨_, hBA a⟩)
  · -- a function of negative order would have its inverse in the maximal ideal of the place
    rcases eq_or_ne x 0 with rfl | hx0
    · exact (placeSubring F v).zero_mem
    rw [mem_placeSubring F v hx0]
    by_contra hneg
    push_neg at hneg
    have hinvne : x⁻¹ ≠ 0 := inv_ne_zero hx0
    have hinv : 0 ≤ ord F v x⁻¹ := by rw [ord_inv]; omega
    obtain ⟨a, s, hs, hsa⟩ := exists_den_notMem_of_ord_nonneg F v hinv
    have hs1 : A.valuation (algebraMap B F s) = 1 :=
      valuation_eq_one_of_notMem_underPrime (hBA := hBA) hs
    have hsne : algebraMap B F s ≠ 0 := by
      intro h
      rw [h, map_zero] at hs1
      exact absurd hs1 zero_ne_one
    -- the numerator vanishes at the prime, so the inverse has valuation less than one
    have hane : algebraMap B F a ≠ 0 := by
      rw [← hsa]; exact mul_ne_zero hsne hinvne
    have ha0 : a ≠ 0 := fun h => hane (by rw [h, map_zero])
    have hs0 : s ≠ 0 := fun h => hsne (by rw [h, map_zero])
    have hordS : ord F v (algebraMap B F s) = 0 := by
      have hnp : ¬ 0 < ord F v (algebraMap B F s) := fun hpos =>
        hs ((mem_iff_ord_pos (K := F) v hs0).mpr hpos)
      have := ord_nonneg (K := F) v s
      omega
    have hordA : 0 < ord F v (algebraMap B F a) := by
      have := congrArg (ord F v) hsa
      rw [ord_mul v hsne hinvne, hordS, zero_add, ord_inv] at this
      omega
    have hamem : a ∈ v.asIdeal := (mem_iff_ord_pos (K := F) v ha0).mpr hordA
    have havlt : A.valuation (algebraMap B F a) < 1 := by
      rw [hv, underPlace_asIdeal, mem_underPrime] at hamem
      exact hamem
    have hxinv : A.valuation x⁻¹ < 1 := by
      have := congrArg A.valuation hsa
      rw [Valuation.map_mul, hs1, one_mul] at this
      rw [this]; exact havlt
    have hxle : A.valuation x ≤ 1 := (ValuationSubring.valuation_le_one_iff A x).mpr hx
    have hone : A.valuation x * A.valuation x⁻¹ = 1 := by
      rw [← Valuation.map_mul, mul_inv_cancel₀ hx0, Valuation.map_one]
    have : (1 : A.ValueGroup) < 1 := by
      calc (1 : A.ValueGroup) = A.valuation x * A.valuation x⁻¹ := hone.symm
        _ ≤ 1 * A.valuation x⁻¹ := mul_le_mul_left hxle _
        _ = A.valuation x⁻¹ := one_mul _
        _ < 1 := hxinv
    exact absurd this (lt_irrefl 1)

/-- **The prime under the place of a prime is that prime.** -/
theorem underPlace_placeSubring (v : HeightOneSpectrum B) :
    underPlace (placeSubring F v) (algebraMap_mem_placeSubring F v) (placeSubring_ne_top F v)
      = v :=
  placeSubring_injective F
    (placeSubring_underPlace (placeSubring F v) (algebraMap_mem_placeSubring F v)
      (placeSubring_ne_top F v))

end Rigidity.RET
