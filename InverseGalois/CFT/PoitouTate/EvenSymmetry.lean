/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ClosingChainPositive
import InverseGalois.CFT.PoitouTate.ClosingChainRamified
import InverseGalois.CFT.PoitouTate.FrobConjugate

/-!
# The value of a unit at a conjugate place and at the inverse conjugate

A unit ramified exactly at one place takes, at the Frobenius automorphism of the place moved by an
automorphism of the base, the same value as at the Frobenius automorphism of the place moved by the
inverse automorphism.  Reciprocity exchanges the unit and its image: the value at the moved place
of the unit equals the value at the place of the image of the unit, and moving the place back by
the inverse automorphism recovers the unit itself.

The two values are therefore a function of the *pair* formed by an automorphism and its inverse.
That is what lets a rule which selects one member of each such pair solve the system of three
trivialisation equations at the exponent two.

## Main results

* `InverseGalois.CFT.placeFrobValue_smul_eq_placeFrobValue_inv_smul`: **the value at a conjugate
  place equals the value at the inverse conjugate place.**

## Tags

number field, place, Frobenius automorphism, reciprocity, Galois orbit
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section Symmetry

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **The value of a unit at the Frobenius automorphism of a conjugate of its own place equals its
value at the Frobenius automorphism of the inverse conjugate.**  Reciprocity turns the first into
the value at the place itself of the image of the unit, and the image of the unit read at the place
moved back by the inverse automorphism is the unit again. -/
theorem placeFrobValue_smul_eq_placeFrobValue_inv_smul
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ 2) {T : Finset (HeightOneSpectrum (𝓞 K))}
    (hT : ∀ (τ : Gal(K/k)) (u : HeightOneSpectrum (𝓞 K)), u ∈ T → τ • u ∈ T)
    {Q : HeightOneSpectrum (𝓞 K)} {σ : Gal(K/k)} (hσQ : σ • Q ≠ Q) (hQT : Q ∉ T)
    (hσQT : σ • Q ∉ T) (hQn : ¬ P Q ∣ 2) (hσQn : ¬ P (σ • Q) ∣ 2) (hσQn' : ¬ P (σ⁻¹ • Q) ∣ 2)
    {z : Kˣ} (hpos : ∀ φ : K →+* ℝ, 0 < φ (z : K))
    (hz : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ Q → (2 : ℤ) ∣ placeValue u z)
    (hzp : ∀ u : HeightOneSpectrum (𝓞 K), P u ∣ 2 →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ 2 = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom z)
    (hneg : ∀ u ∈ T, IsNegOnePow (u.adicCompletion K) 2)
    (hiso : ∀ u ∈ T, ∃ d : localClasses u 2, localClassHom u 2 z ∈ Subgroup.zpowers d ∧
      localClassHom u 2 (galUnits σ z) ∈ Subgroup.zpowers d)
    (hcop : IsCoprime (placeValue Q z) (2 : ℤ)) :
    placeFrobValue hres hζ (σ • Q) z = placeFrobValue hres hζ (σ⁻¹ • Q) z := by
  have hb : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ σ • Q →
      (2 : ℤ) ∣ placeValue u (galUnits σ z) :=
    fun u huT hu => dvd_placeValue_galUnits_of_notMem hT σ hz u huT hu
  have h1 : placeFrobValue hres hζ (σ • Q) z = placeFrobValue hres hζ Q (galUnits σ z) :=
    placeFrobValue_eq_placeFrobValue_of_isotropic_pos Nat.prime_two hres hζ (Ne.symm hσQ) hQT
      hσQT hQn hσQn (forall_pos_galUnits σ hpos) hz hb hzp hneg hiso hcop (Int.ModEq.refl _)
      (by rw [placeValue_galSmul Q σ z])
  have h2 : placeFrobValue hres hζ (σ⁻¹ • Q) (galUnits σ⁻¹ (galUnits σ z)) =
      placeFrobValue hres hζ Q (galUnits σ z) :=
    placeFrobValue_galUnits hres hζ σ⁻¹ hQn hσQn' (hb Q hQT fun h => hσQ h.symm)
  rw [h1, ← h2, galUnits_eq_smul, galUnits_eq_smul, inv_smul_smul]

end Symmetry

end InverseGalois.CFT
