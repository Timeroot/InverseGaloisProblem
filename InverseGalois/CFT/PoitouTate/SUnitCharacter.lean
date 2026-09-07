/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.FrobeniusCharacter
import InverseGalois.CFT.PoitouTate.SUnitPlace
import InverseGalois.CFT.PoitouTate.TorsionCharacter
import InverseGalois.CFT.Units.PlaceTower

/-!
# A character of the units is the value at a Frobenius automorphism

A character of a group of units of a number field with values in the elements of the rationals
modulo the integers killed by a prime is the same thing as a character with values in the roots of
unity of that order: the elements killed by the prime are the multiples of its reciprocal, so a
value is named by a residue modulo the prime, and the residues modulo the prime name the powers of
a primitive root of unity of that order.  The translation is faithful, so the two characters are
trivial at the same places.

Feeding the translated character to the construction of a place prescribed by a character of the
`S`-units therefore produces a finite place at which the value at the Frobenius automorphism is
trivial exactly where the given character is.  Two characters killed by a prime, the first trivial
wherever the second is, are proportional, so the value at the Frobenius automorphism of that place
is a fixed power of the given character, and the exponent is prime to the order because the given
character is not trivial.

## Main definitions

* `InverseGalois.CFT.rootOfUnityChar`: **the character with values in the powers of a primitive
  root of unity attached to a character killed by the order of that root.**

## Main results

* `InverseGalois.CFT.rootOfUnityChar_eq_one_iff`: the translation is trivial exactly where the
  character is.
* `InverseGalois.CFT.exists_place_placeFrobValue_eq_zpow_character`: **outside any prescribed
  finite set of finite places of the bottom field there is a place, completely split in the number
  field the `S`-units are taken from, at which the value at the Frobenius automorphism is a power
  prime to the order of the given character of the units.**

## Tags

character, root of unity, Frobenius, S-unit, Chebotarev, completely split, class field theory
-/

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

/-! ### A character killed by a prime, read in the roots of unity -/

section Transport

variable {G : Type*} [Group G] {p : ℕ} [NeZero p]

/-- The residue modulo the exponent naming the value of a character killed by that exponent. -/
noncomputable def pTorsionResidue (χ : G →* Multiplicative QModZ) (hχ : ∀ g, χ g ^ p = 1)
    (g : G) : ZMod p :=
  (exists_zmodQModZ_eq_of_pow_eq_one (hχ g)).choose

/-- The residue naming a value of a character killed by the exponent does name it. -/
theorem ofAdd_zmodQModZ_pTorsionResidue (χ : G →* Multiplicative QModZ) (hχ : ∀ g, χ g ^ p = 1)
    (g : G) : Multiplicative.ofAdd (zmodQModZ p (pTorsionResidue χ hχ g)) = χ g :=
  (exists_zmodQModZ_eq_of_pow_eq_one (hχ g)).choose_spec

/-- The residue naming a value of a character killed by the exponent, read additively. -/
theorem zmodQModZ_pTorsionResidue (χ : G →* Multiplicative QModZ) (hχ : ∀ g, χ g ^ p = 1)
    (g : G) : zmodQModZ p (pTorsionResidue χ hχ g) = Multiplicative.toAdd (χ g) := by
  rw [← ofAdd_zmodQModZ_pTorsionResidue χ hχ g]
  rfl

/-- The residue naming the value of a character is additive, because the residues modulo the
exponent name the elements killed by it without repetition. -/
theorem pTorsionResidue_mul (χ : G →* Multiplicative QModZ) (hχ : ∀ g, χ g ^ p = 1) (g h : G) :
    pTorsionResidue χ hχ (g * h) = pTorsionResidue χ hχ g + pTorsionResidue χ hχ h := by
  refine zmodQModZ_injective p ?_
  rw [_root_.map_add, zmodQModZ_pTorsionResidue, zmodQModZ_pTorsionResidue,
    zmodQModZ_pTorsionResidue, _root_.map_mul, toAdd_mul]

/-- The residue naming the value of a character vanishes exactly where the character is trivial. -/
theorem pTorsionResidue_eq_zero_iff (χ : G →* Multiplicative QModZ) (hχ : ∀ g, χ g ^ p = 1)
    (g : G) : pTorsionResidue χ hχ g = 0 ↔ χ g = 1 := by
  constructor
  · intro h
    rw [← ofAdd_zmodQModZ_pTorsionResidue χ hχ g, h, _root_.map_zero]
    rfl
  · intro h
    refine zmodQModZ_injective p ?_
    rw [zmodQModZ_pTorsionResidue, h, toAdd_one, _root_.map_zero]

variable {R : Type*} [CommRing R] {ζ : Rˣ}

omit [NeZero p] in
/-- A power of a primitive root of unity named by a residue modulo its order is trivial exactly
when the residue is. -/
theorem coe_zmodEquivZPowers_eq_one_iff (hζ : IsPrimitiveRoot ζ p) (c : ZMod p) :
    ((hζ.zmodEquivZPowers c).toMul : Rˣ) = 1 ↔ c = 0 := by
  constructor
  · intro h
    refine hζ.zmodEquivZPowers.injective ?_
    rw [_root_.map_zero]
    exact _root_.toMul_eq_one.1 (Subtype.ext h)
  · rintro rfl
    rw [_root_.map_zero]
    rfl

/-- **The character with values in the powers of a primitive root of unity attached to a character
killed by the order of that root.**  A value of the given character is named by a residue modulo
the order, and the residues modulo the order name the powers of the root of unity. -/
noncomputable def rootOfUnityChar (hζ : IsPrimitiveRoot ζ p) (χ : G →* Multiplicative QModZ)
    (hχ : ∀ g, χ g ^ p = 1) : G →* Rˣ where
  toFun g := ((hζ.zmodEquivZPowers (pTorsionResidue χ hχ g)).toMul : Rˣ)
  map_one' := by
    rw [(pTorsionResidue_eq_zero_iff χ hχ 1).2 (_root_.map_one χ), _root_.map_zero]
    rfl
  map_mul' g h := by
    rw [pTorsionResidue_mul, _root_.map_add]
    rfl

/-- **The translation of a character into the roots of unity is trivial exactly where the
character is.** -/
theorem rootOfUnityChar_eq_one_iff (hζ : IsPrimitiveRoot ζ p) (χ : G →* Multiplicative QModZ)
    (hχ : ∀ g, χ g ^ p = 1) (g : G) : rootOfUnityChar hζ χ hχ g = 1 ↔ χ g = 1 := by
  rw [show rootOfUnityChar hζ χ hχ g
      = ((hζ.zmodEquivZPowers (pTorsionResidue χ hχ g)).toMul : Rˣ) from rfl,
    coe_zmodEquivZPowers_eq_one_iff, pTorsionResidue_eq_zero_iff]

end Transport

/-! ### The place at which a character of the units is the value at a Frobenius automorphism -/

section Place

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A]
  {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] {p : ℕ} [NeZero p]
  {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **Outside any prescribed finite set of finite places of the bottom field there is a place,
completely split in the number field the `S`-units are taken from, at which the value at the
Frobenius automorphism is trivial exactly at the `S`-units a character killed by the exponent
kills.**  The character is translated into the roots of unity of that order, where the construction
of a place prescribed by a character of the `S`-units applies to it, and the translation is trivial
exactly where the character is. -/
theorem exists_place_frobValue_eq_one_iff_torsionChar (hp : p.Prime)
    {X : Set (HeightOneSpectrum (𝓞 ↥Ω))} (hXfin : X.Finite)
    (hXstab : ∀ (σ : Gal(↥Ω/k)) {v : HeightOneSpectrum (𝓞 ↥Ω)}, v ∈ X → σ • v ∈ X)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {U : Subgroup (↥Ω)ˣ} (hU : U ≤ sUnits ↥Ω X) (χ : ↥U →* Multiplicative QModZ)
    (hχ : ∀ u, χ u ^ p = 1)
    (hχpow : ∀ (u : (↥Ω)ˣ) (hu : u ∈ U) (y : (↥Ω)ˣ), u = y ^ p → χ ⟨u, hu⟩ = 1)
    (hne : ∃ u : ↥U, χ u ≠ 1) (T : Finset (HeightOneSpectrum (𝓞 k))) :
    ∃ V : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 k) V ∉ T ∧
      stabilizer Gal(↥Ω/k) V = ⊥ ∧ ¬ Pc (primeUnder (𝓞 K) V) ∣ p ∧
      ∀ (u : Kˣ) (hu : Units.map (algebraMap K ↥Ω : K →* ↥Ω) u ∈ U),
        (p : ℤ) ∣ placeValue (primeUnder (𝓞 K) V) u →
          (placeFrobValue hres hζ (primeUnder (𝓞 K) V) u = 1 ↔ χ ⟨_, hu⟩ = 1) := by
  have hζΩ : IsPrimitiveRoot (algebraMap K ↥Ω ζ) p :=
    hζ.map_of_injective (algebraMap K ↥Ω).injective
  obtain ⟨ζu, hζu⟩ : ∃ ζu : (↥Ω)ˣ, IsPrimitiveRoot ζu p :=
    ⟨(hζΩ.isUnit hp.ne_zero).unit, hζΩ.isUnit_unit hp.ne_zero⟩
  obtain ⟨V, hVT, hVstab, hVP, hViff⟩ :=
    exists_place_frobValue_eq_one_iff_character_sUnits hp hXfin hXstab hζ hres hU
      (rootOfUnityChar hζu χ hχ)
      (fun u hu y hy => (rootOfUnityChar_eq_one_iff hζu χ hχ _).2 (hχpow u hu y hy))
      (by
        obtain ⟨u, hu⟩ := hne
        exact ⟨u, fun h => hu ((rootOfUnityChar_eq_one_iff hζu χ hχ u).1 h)⟩) T
  exact ⟨V, hVT, hVstab, hVP, fun u hu hdvd =>
    (hViff u hu hdvd).trans (rootOfUnityChar_eq_one_iff hζu χ hχ _)⟩

/-- **Outside any prescribed finite set of finite places of the bottom field there is a place,
completely split in the number field the `S`-units are taken from, at which the value at the
Frobenius automorphism is a fixed power, prime to the exponent, of a given character of a group of
units of the middle field.**  A field embedding is injective, so the character transports to the
image of the group of units in the top field, where the prescription of a place applies to it; the
place so obtained has a Frobenius character trivial exactly where the given character is, and two
characters killed by a prime, the first trivial wherever the second is, are proportional. -/
theorem exists_place_placeFrobValue_eq_zpow_character (hp : p.Prime)
    {X : Set (HeightOneSpectrum (𝓞 ↥Ω))} (hXfin : X.Finite)
    (hXstab : ∀ (σ : Gal(↥Ω/k)) {v : HeightOneSpectrum (𝓞 ↥Ω)}, v ∈ X → σ • v ∈ X)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {W : Subgroup Kˣ}
    (hW : Subgroup.map (Units.map (algebraMap K ↥Ω : K →* ↥Ω)) W ≤ sUnits ↥Ω X)
    (T : Finset (HeightOneSpectrum (𝓞 k)))
    (hWval : ∀ u ∈ W, ∀ Q : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) Q ∉ T →
      (p : ℤ) ∣ placeValue Q u)
    (χ : ↥W →* Multiplicative QModZ) (hχ : ∀ u, χ u ^ p = 1)
    (hχpow : ∀ (u : ↥W) (y : (↥Ω)ˣ),
      Units.map (algebraMap K ↥Ω : K →* ↥Ω) (u : Kˣ) = y ^ p → χ u = 1)
    (hne : ∃ u, χ u ≠ 1) :
    ∃ V : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 k) V ∉ T ∧
      stabilizer Gal(↥Ω/k) V = ⊥ ∧ ¬ Pc (primeUnder (𝓞 K) V) ∣ p ∧
      ∃ j : ℤ, ¬ (p : ℤ) ∣ j ∧
        ∀ u : ↥W, placeFrobValue hres hζ (primeUnder (𝓞 K) V) (u : Kˣ) = χ u ^ j := by
  have hfinj : Function.Injective (Units.map (algebraMap K ↥Ω : K →* ↥Ω)) :=
    Units.map_injective (algebraMap K ↥Ω).injective
  have hesymm : ∀ (u : Kˣ) (hu : u ∈ W)
      (hfu : Units.map (algebraMap K ↥Ω : K →* ↥Ω) u
        ∈ Subgroup.map (Units.map (algebraMap K ↥Ω : K →* ↥Ω)) W),
      (W.equivMapOfInjective _ hfinj).symm ⟨_, hfu⟩ = ⟨u, hu⟩ :=
    fun _ _ _ => (W.equivMapOfInjective _ hfinj).symm_apply_eq.2 (Subtype.ext rfl)
  obtain ⟨V, hVT, hVstab, hVP, hViff⟩ :=
    exists_place_frobValue_eq_one_iff_torsionChar hp hXfin hXstab hζ hres hW
      (χ.comp (W.equivMapOfInjective _ hfinj).symm.toMonoidHom) (fun _ => hχ _)
      (fun u hu y hy => by
        obtain ⟨v, hv, rfl⟩ := hu
        show χ ((W.equivMapOfInjective _ hfinj).symm ⟨_, _⟩) = 1
        rw [hesymm v hv]
        exact hχpow ⟨v, hv⟩ y hy)
      (by
        obtain ⟨u, hu⟩ := hne
        refine ⟨W.equivMapOfInjective _ hfinj u, ?_⟩
        show χ ((W.equivMapOfInjective _ hfinj).symm
          ((W.equivMapOfInjective _ hfinj) u)) ≠ 1
        rwa [MulEquiv.symm_apply_apply]) T
  refine ⟨V, hVT, hVstab, hVP, ?_⟩
  have hQT : primeUnder (𝓞 k) (primeUnder (𝓞 K) V) ∉ T := by
    rwa [primeUnder_primeUnder k K V]
  have hkey : ∀ u : ↥W,
      placeFrobValue hres hζ (primeUnder (𝓞 K) V) (u : Kˣ) = 1 ↔ χ u = 1 := by
    intro u
    refine (hViff (u : Kˣ) (Subgroup.mem_map_of_mem _ u.2) (hWval _ u.2 _ hQT)).trans ?_
    show χ ((W.equivMapOfInjective _ hfinj).symm ⟨_, _⟩) = 1 ↔ χ u = 1
    rw [hesymm (u : Kˣ) u.2]
  have hFapp : ∀ u : ↥W, ((placeFrobValueHom hres hζ (primeUnder (𝓞 K) V)).comp W.subtype) u
      = placeFrobValue hres hζ (primeUnder (𝓞 K) V) (u : Kˣ) :=
    fun u => placeFrobValueHom_apply hres hζ (primeUnder (𝓞 K) V) (u : Kˣ)
  obtain ⟨j, hj⟩ := exists_zpow_eq_of_forall_eq_one hp
    ((placeFrobValueHom hres hζ (primeUnder (𝓞 K) V)).comp W.subtype) χ
    (fun u => by rw [hFapp u]; exact pow_placeFrobValue_eq_one hres hζ _ _) hχ
    fun u h => (hFapp u).trans ((hkey u).2 h)
  obtain ⟨u₀, hu₀⟩ := hne
  exact ⟨j, not_dvd_of_zpow_eq_ne_one hχ (x := u₀) (fun h =>
    hu₀ ((hkey u₀).1 ((hFapp u₀).symm.trans ((hj u₀).trans h)))),
    fun u => (hFapp u).symm.trans (hj u)⟩

end Place

end InverseGalois.CFT
