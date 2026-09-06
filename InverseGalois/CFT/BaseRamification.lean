/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.BaseCompositum
import InverseGalois.CFT.Units.FrobeniusPlace
import InverseGalois.CFT.Units.RatRamIdx

/-!
# Ramification in a compositum with a Galois extension of the rationals

The Galois group of the compositum of a number field with a Galois extension of the rationals is
the Galois group of the latter, through restriction, as soon as the two are unramified at disjoint
sets of primes.  Restriction carries inertia to inertia: an automorphism of the compositum that is
trivial on the residues at a place restricts to an automorphism of the subfield that is trivial on
the residues at the place below.  Restriction being injective, the inertia group of the compositum
over the number field embeds in the inertia group of the subfield over the rationals.

The order of an inertia group is the ramification index, so a place of the compositum whose trace
on the subfield is unramified over the rationals is itself unramified over the number field.  This
is what makes the compositum with a cyclotomic field unramified away from the conductor over an
arbitrary base, exactly as the cyclotomic field is over the rationals.

## Main results

* `InverseGalois.CFT.card_inertia_eq_ramIdx`: **the order of the inertia group at a place is the
  ramification index of that place.**
* `InverseGalois.CFT.inertia_eq_bot_iff_ramIdx_eq_one`: **a place is unramified exactly when its
  inertia group is trivial.**
* `InverseGalois.CFT.galRestrictSub_mem_inertia`: **restriction to the subfield carries inertia to
  inertia.**
* `InverseGalois.CFT.ramIdx_eq_one_of_ramIdx_eq_one`: **a place of the compositum whose trace on
  the subfield is unramified over the rationals is unramified over the number field.**

## Tags

number field, compositum, inertia group, ramification index, unramified, Galois group
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField

/-! ### The order of an inertia group -/

section Card

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **The order of the inertia group at a place is the ramification index of that place.** -/
theorem card_inertia_eq_ramIdx (w : HeightOneSpectrum (𝓞 K)) :
    Nat.card ↥(Ideal.inertia Gal(K/k) w.asIdeal) = ramIdx (𝓞 k) w := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI := isMaximal_of_ne_bot_base w.asIdeal w.ne_bot
  haveI := finite_quotient_of_ne_bot_base w.asIdeal w.ne_bot
  haveI := isMaximal_under_of_ne_bot_base (k := k) w.asIdeal w.ne_bot
  haveI := isSeparable_residue_of_ne_bot_base (k := k) w.asIdeal w.ne_bot
  haveI : w.asIdeal.LiesOver (w.asIdeal.under (𝓞 k)) := ⟨rfl⟩
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(K/k)) (w.asIdeal.under (𝓞 k))
      (under_ne_bot_base (k := k) w.asIdeal w.ne_bot) w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under (𝓞 k)) w.asIdeal Gal(K/k),
    ramIdx, primeUnder_asIdeal]

/-- **A place is unramified exactly when its inertia group is trivial.** -/
theorem inertia_eq_bot_iff_ramIdx_eq_one (w : HeightOneSpectrum (𝓞 K)) :
    Ideal.inertia Gal(K/k) w.asIdeal = ⊥ ↔ ramIdx (𝓞 k) w = 1 := by
  rw [← Subgroup.card_eq_one, card_inertia_eq_ramIdx]

end Card

/-! ### Restriction carries inertia to inertia -/

section Transfer

variable {k F₀ E : Type} [Field k] [NumberField k] [Field F₀] [NumberField F₀] [IsGalois ℚ F₀]
  [Field E] [NumberField E] [Algebra k E] [Algebra F₀ E] [IsScalarTower ℚ k E]
  [IsScalarTower ℚ F₀ E] [IsGalois k E]

omit [IsGalois k E] in
/-- **Restriction to the subfield commutes with the inclusion of the rings of integers.** -/
theorem galRestrictSub_smul_ringOfIntegers (σ : Gal(E/k)) (y : 𝓞 F₀) :
    algebraMap (𝓞 F₀) (𝓞 E) (galRestrictSub k F₀ E σ • y) = σ • algebraMap (𝓞 F₀) (𝓞 E) y := by
  refine Subtype.ext ?_
  show algebraMap F₀ E ((galRestrictSub k F₀ E σ • y : 𝓞 F₀) : F₀) = _
  rw [show ((galRestrictSub k F₀ E σ • y : 𝓞 F₀) : F₀)
      = galRestrictSub k F₀ E σ (y : F₀) from rfl, galRestrictSub_algebraMap σ (y : F₀)]
  rfl

omit [IsGalois k E] in
/-- **Restriction to the subfield carries inertia to inertia.**  An automorphism trivial on the
residues at a place of the compositum is trivial on the residues at the place below it. -/
theorem galRestrictSub_mem_inertia (w : HeightOneSpectrum (𝓞 E)) {σ : Gal(E/k)}
    (hσ : σ ∈ Ideal.inertia Gal(E/k) w.asIdeal) :
    galRestrictSub k F₀ E σ ∈ Ideal.inertia Gal(F₀/ℚ) (primeUnder (𝓞 F₀) w).asIdeal := by
  intro y
  show galRestrictSub k F₀ E σ • y - y ∈ (primeUnder (𝓞 F₀) w).asIdeal
  rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_sub,
    galRestrictSub_smul_ringOfIntegers]
  exact hσ _

omit [IsGalois k E] in
/-- **A place of the compositum whose trace on the subfield has trivial inertia over the rationals
has trivial inertia over the number field.** -/
theorem inertia_eq_bot_of_inertia_eq_bot
    (hgen : Algebra.adjoin k (Set.range (algebraMap F₀ E)) = ⊤) (w : HeightOneSpectrum (𝓞 E))
    (h : Ideal.inertia Gal(F₀/ℚ) (primeUnder (𝓞 F₀) w).asIdeal = ⊥) :
    Ideal.inertia Gal(E/k) w.asIdeal = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun σ hσ => ?_
  refine galRestrictSub_injective hgen ?_
  rw [map_one]
  exact (Subgroup.eq_bot_iff_forall _).mp h _ (galRestrictSub_mem_inertia w hσ)

/-- **A place of the compositum whose trace on the subfield is unramified over the rationals is
unramified over the number field.** -/
theorem ramIdx_eq_one_of_ramIdx_eq_one
    (hgen : Algebra.adjoin k (Set.range (algebraMap F₀ E)) = ⊤) (w : HeightOneSpectrum (𝓞 E))
    (h : ramIdx (𝓞 ℚ) (primeUnder (𝓞 F₀) w) = 1) : ramIdx (𝓞 k) w = 1 :=
  (inertia_eq_bot_iff_ramIdx_eq_one w).mp
    (inertia_eq_bot_of_inertia_eq_bot hgen w ((inertia_eq_bot_iff_ramIdx_eq_one _).mpr h))

end Transfer

end InverseGalois.CFT
