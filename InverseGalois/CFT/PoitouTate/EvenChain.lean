/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.EvenSymmetry

/-!
# Three units, and the three orbits of their places

Three units of a number field, each ramified at a single place and each carrying the same value at
the Frobenius automorphism of its own place moved by any automorphism of the base, have a product
which is trivial at every nontrivial conjugate of each of the three places.  The mechanism is the
same at each of the three orbits, and it is a rule which selects one member of each pair formed by
an automorphism and its inverse.

At a conjugate of the first place the value of the first unit is the common value; the second unit
contributes that value or nothing according as the automorphism belongs to the selected half or
not, and the third unit contributes it or nothing according as the *inverse* automorphism does.
Exactly one of the two contributions is made unless the automorphism is its own inverse, when
neither is made and the common value is itself trivial.  So the product is either the square of the
common value or the value at an involution, and both are trivial.

At a conjugate of the second and of the third place the same three contributions appear, cyclically
permuted, but two of them have first to be moved there by reciprocity: the value of a unit at a
conjugate of a *later* place is the value of the later unit at the inversely moved earlier place,
which is exactly where the rule governing the recursion prescribes it.

## Main results

* `InverseGalois.CFT.eq_one_of_halfRule_three`: **a product of three values, one of them free and
  the other two governed by a half set, is trivial.**
* `InverseGalois.CFT.placeFrobValue_smul_eq_inv_smul_of_unramified`: the symmetry between an
  automorphism and its inverse, for a unit ramified at a single place.
* `InverseGalois.CFT.placeFrobValue_smul_eq_placeFrobValue_inv_smul_of_forall_pos`: **the value of
  a unit at a moved place of another unit equals the value of that other unit at the inversely
  moved place of the first.**
* `InverseGalois.CFT.placeFrobValue_first_orbit_eq_one`,
  `InverseGalois.CFT.placeFrobValue_second_orbit_eq_one`,
  `InverseGalois.CFT.placeFrobValue_third_orbit_eq_one`: **the product of the three units is
  trivial at every nontrivial conjugate of each of the three places.**

## Tags

number field, place, Frobenius automorphism, reciprocity, half set, involution
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### A product of three values governed by a half set -/

/-- **A product of three values, one of them free and the other two governed by a half set, is
trivial.**  The two governed values are the free one when the automorphism, respectively its
inverse, belongs to the half set, and are trivial otherwise.  Exactly one of the two belongs to it
unless the automorphism is its own inverse, in which case neither does and the free value is itself
trivial. -/
theorem eq_one_of_halfRule_three {G M : Type*} [Group G] [CommGroup M] {L : Set G}
    (hL1 : ∀ τ : G, τ = τ⁻¹ → τ ∉ L) (hL2 : ∀ τ : G, τ ≠ τ⁻¹ → (τ ∈ L ↔ τ⁻¹ ∉ L)) {σ : G}
    {a b c : M} (ha : a * a = 1) (hinv : σ = σ⁻¹ → a = 1) (hb : σ ∈ L → b = a)
    (hb1 : σ ∉ L → b = 1) (hc : σ⁻¹ ∈ L → c = a) (hc1 : σ⁻¹ ∉ L → c = 1) : a * b * c = 1 := by
  by_cases hσ : σ = σ⁻¹
  · rw [hinv hσ, hb1 (hL1 σ hσ), hc1 (by rw [← hσ]; exact hL1 σ hσ), one_mul, one_mul]
  · by_cases hm : σ ∈ L
    · rw [hb hm, hc1 ((hL2 σ hσ).1 hm), mul_one, ha]
    · have hm' : σ⁻¹ ∈ L := by
        by_contra hcon
        exact hm ((hL2 σ hσ).2 hcon)
      rw [hb1 hm, hc hm', mul_one, ha]

/-! ### Reciprocity between two units, each ramified at a single place -/

section Reciprocity

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **The value of a unit ramified at a single place, at the Frobenius automorphism of a conjugate
of that place, equals its value at the inverse conjugate.**  Nothing is asked of the unit away from
its own place beyond an even order, so the reciprocity law applies with no prescribed set at
all. -/
theorem placeFrobValue_smul_eq_inv_smul_of_unramified
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ 2) {Q : HeightOneSpectrum (𝓞 K)} {σ : Gal(K/k)}
    (hσQ : σ • Q ≠ Q) (hQn : ¬ P Q ∣ 2) (hσQn : ¬ P (σ • Q) ∣ 2) (hσQn' : ¬ P (σ⁻¹ • Q) ∣ 2)
    {x : Kˣ} (hpos : ∀ φ : K →+* ℝ, 0 < φ (x : K))
    (hx : ∀ u : HeightOneSpectrum (𝓞 K), u ≠ Q → (2 : ℤ) ∣ placeValue u x)
    (hxp : ∀ u : HeightOneSpectrum (𝓞 K), P u ∣ 2 →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ 2 = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom x)
    (hcop : IsCoprime (placeValue Q x) (2 : ℤ)) :
    placeFrobValue hres hζ (σ • Q) x = placeFrobValue hres hζ (σ⁻¹ • Q) x :=
  placeFrobValue_smul_eq_placeFrobValue_inv_smul (T := ∅) hres hζ
    (fun _ u h => absurd h (Finset.notMem_empty u)) hσQ
    (Finset.notMem_empty _) (Finset.notMem_empty _) hQn hσQn hσQn' hpos
    (fun u _ hu => hx u hu) hxp (fun u hu => absurd hu (Finset.notMem_empty u))
    (fun u hu => absurd hu (Finset.notMem_empty u)) hcop

/-- **The value of a unit at the Frobenius automorphism of a moved place of a second unit equals
the value of the second unit at the inversely moved place of the first.**  Each unit is ramified at
a single place and the two values there agree modulo two and are prime to it; reciprocity exchanges
the two units, and moving the place back by the inverse automorphism recovers the second unit. -/
theorem placeFrobValue_smul_eq_placeFrobValue_inv_smul_of_forall_pos
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ 2) {V W : HeightOneSpectrum (𝓞 K)} {σ : Gal(K/k)}
    (hVW : V ≠ σ • W) (hVn : ¬ P V ∣ 2) (hVn' : ¬ P (σ⁻¹ • V) ∣ 2) (hWn : ¬ P (σ • W) ∣ 2)
    {x y : Kˣ} (hypos : ∀ φ : K →+* ℝ, 0 < φ (y : K))
    (hx : ∀ u : HeightOneSpectrum (𝓞 K), u ≠ V → (2 : ℤ) ∣ placeValue u x)
    (hy : ∀ u : HeightOneSpectrum (𝓞 K), u ≠ W → (2 : ℤ) ∣ placeValue u y)
    (hxp : ∀ u : HeightOneSpectrum (𝓞 K), P u ∣ 2 →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ 2 = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom x)
    {m : ℤ} (hm : IsCoprime m (2 : ℤ)) (hxV : placeValue V x ≡ m [ZMOD (2 : ℤ)])
    (hyW : placeValue W y ≡ m [ZMOD (2 : ℤ)]) :
    placeFrobValue hres hζ (σ • W) x = placeFrobValue hres hζ (σ⁻¹ • V) y := by
  have h1 : placeFrobValue hres hζ (σ • W) x = placeFrobValue hres hζ V (galUnits σ y) :=
    placeFrobValue_eq_placeFrobValue_of_forall_pos Nat.prime_two hres hζ hVW hVn hWn
      (forall_pos_galUnits σ hypos) hx (dvd_placeValue_galUnits σ hy) hxp hm hxV
      (by rw [placeValue_galSmul]; exact hyW)
  have h2 : placeFrobValue hres hζ (σ⁻¹ • V) (galUnits σ⁻¹ (galUnits σ y))
      = placeFrobValue hres hζ V (galUnits σ y) :=
    placeFrobValue_galUnits hres hζ σ⁻¹ hVn hVn' (dvd_placeValue_galUnits σ hy V hVW)
  rw [h1, ← h2, galUnits_eq_smul, galUnits_eq_smul, inv_smul_smul]

end Reciprocity

/-! ### The three orbits -/

section Orbits

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}
  (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
  {ζ : K} (hζ : IsPrimitiveRoot ζ 2) {L : Set Gal(K/k)}
  (hL1 : ∀ τ : Gal(K/k), τ = τ⁻¹ → τ ∉ L)
  (hL2 : ∀ τ : Gal(K/k), τ ≠ τ⁻¹ → (τ ∈ L ↔ τ⁻¹ ∉ L))
  {Q R S : HeightOneSpectrum (𝓞 K)} {x y z : Kˣ} {σ : Gal(K/k)}

/-- A unit whose local class at a place is the local class of a second unit there has the same
value at the Frobenius automorphism of that place. -/
private theorem placeFrobValue_eq_of_localClassHom_eq_pair {v : HeightOneSpectrum (𝓞 K)} {a b : Kˣ}
    (h : localClassHom v 2 a = localClassHom v 2 b) :
    placeFrobValue hres hζ v a = placeFrobValue hres hζ v b :=
  placeFrobValue_eq_of_localClassHom_eq hres hζ v h

/-- A unit whose local class at a place is trivial has trivial value at the Frobenius automorphism
of that place. -/
private theorem placeFrobValue_eq_one_of_localClassHom_eq_one {v : HeightOneSpectrum (𝓞 K)}
    {a : Kˣ} (h : localClassHom v 2 a = 1) : placeFrobValue hres hζ v a = 1 :=
  (placeFrobValue_eq_of_localClassHom_eq hres hζ v (b := 1)
    (by rw [h, _root_.map_one])).trans (placeFrobValue_one hres hζ v)

include hL1 hL2 in
/-- **At a nontrivial conjugate of the first of the three places the product of the three units is
trivial.**  The first unit contributes the common value, the second contributes it or nothing
according as the automorphism belongs to the selected half, and the third according as the inverse
automorphism does. -/
theorem placeFrobValue_first_orbit_eq_one
    (hinv : σ = σ⁻¹ → placeFrobValue hres hζ (σ • Q) x = 1)
    (hy : (σ ∈ L → localClassHom (σ • Q) 2 y = localClassHom (σ • Q) 2 x) ∧
      (σ ∉ L → localClassHom (σ • Q) 2 y = 1))
    (hz : (σ⁻¹ ∈ L → localClassHom (σ • Q) 2 z = localClassHom (σ • Q) 2 x) ∧
      (σ⁻¹ ∉ L → localClassHom (σ • Q) 2 z = 1)) :
    placeFrobValue hres hζ (σ • Q) (x * y * z) = 1 := by
  rw [placeFrobValue_mul, placeFrobValue_mul]
  refine eq_one_of_halfRule_three hL1 hL2 ?_ hinv
    (fun h => placeFrobValue_eq_of_localClassHom_eq_pair hres hζ (hy.1 h))
    (fun h => placeFrobValue_eq_one_of_localClassHom_eq_one hres hζ (hy.2 h))
    (fun h => placeFrobValue_eq_of_localClassHom_eq_pair hres hζ (hz.1 h))
    (fun h => placeFrobValue_eq_one_of_localClassHom_eq_one hres hζ (hz.2 h))
  rw [← pow_two]
  exact pow_placeFrobValue_eq_one hres hζ _ _

include hL1 hL2 in
/-- **At a nontrivial conjugate of the second of the three places the product of the three units is
trivial.**  The second unit contributes the common value, the third contributes it or nothing
according as the automorphism belongs to the selected half, and the first is carried by reciprocity
to the inversely moved first place, where the second unit contributes it or nothing according as
the inverse automorphism belongs to the selected half. -/
theorem placeFrobValue_second_orbit_eq_one
    (hsym : placeFrobValue hres hζ (σ⁻¹ • Q) x = placeFrobValue hres hζ (σ • Q) x)
    (hpig : placeFrobValue hres hζ (σ • R) y = placeFrobValue hres hζ (σ • Q) x)
    (hrec : placeFrobValue hres hζ (σ • R) x = placeFrobValue hres hζ (σ⁻¹ • Q) y)
    (hinv : σ = σ⁻¹ → placeFrobValue hres hζ (σ • Q) x = 1)
    (hy : (σ⁻¹ ∈ L → localClassHom (σ⁻¹ • Q) 2 y = localClassHom (σ⁻¹ • Q) 2 x) ∧
      (σ⁻¹ ∉ L → localClassHom (σ⁻¹ • Q) 2 y = 1))
    (hz : (σ ∈ L → localClassHom (σ • R) 2 z = localClassHom (σ • R) 2 y) ∧
      (σ ∉ L → localClassHom (σ • R) 2 z = 1)) :
    placeFrobValue hres hζ (σ • R) (x * y * z) = 1 := by
  rw [placeFrobValue_mul, placeFrobValue_mul, hrec, hpig, mul_rotate]
  refine eq_one_of_halfRule_three hL1 hL2 ?_ hinv
    (fun h => ((placeFrobValue_eq_of_localClassHom_eq_pair hres hζ (hz.1 h)).trans hpig))
    (fun h => placeFrobValue_eq_one_of_localClassHom_eq_one hres hζ (hz.2 h))
    (fun h => ((placeFrobValue_eq_of_localClassHom_eq_pair hres hζ (hy.1 h)).trans hsym))
    (fun h => placeFrobValue_eq_one_of_localClassHom_eq_one hres hζ (hy.2 h))
  rw [← pow_two]
  exact pow_placeFrobValue_eq_one hres hζ _ _

include hL1 hL2 in
/-- **At a nontrivial conjugate of the third of the three places the product of the three units is
trivial.**  The third unit contributes the common value, and the other two are carried by
reciprocity to the inversely moved first and second places, where the third unit contributes the
common value or nothing according as the automorphism, respectively its inverse, belongs to the
selected half. -/
theorem placeFrobValue_third_orbit_eq_one
    (hsym : placeFrobValue hres hζ (σ⁻¹ • Q) x = placeFrobValue hres hζ (σ • Q) x)
    (hpig : placeFrobValue hres hζ (σ • S) z = placeFrobValue hres hζ (σ • Q) x)
    (hpig' : placeFrobValue hres hζ (σ⁻¹ • R) y = placeFrobValue hres hζ (σ⁻¹ • Q) x)
    (hrecx : placeFrobValue hres hζ (σ • S) x = placeFrobValue hres hζ (σ⁻¹ • Q) z)
    (hrecy : placeFrobValue hres hζ (σ • S) y = placeFrobValue hres hζ (σ⁻¹ • R) z)
    (hinv : σ = σ⁻¹ → placeFrobValue hres hζ (σ • Q) x = 1)
    (hzQ : (σ ∈ L → localClassHom (σ⁻¹ • Q) 2 z = localClassHom (σ⁻¹ • Q) 2 x) ∧
      (σ ∉ L → localClassHom (σ⁻¹ • Q) 2 z = 1))
    (hzR : (σ⁻¹ ∈ L → localClassHom (σ⁻¹ • R) 2 z = localClassHom (σ⁻¹ • R) 2 y) ∧
      (σ⁻¹ ∉ L → localClassHom (σ⁻¹ • R) 2 z = 1)) :
    placeFrobValue hres hζ (σ • S) (x * y * z) = 1 := by
  rw [placeFrobValue_mul, placeFrobValue_mul, hrecx, hrecy, hpig, mul_rotate, mul_rotate]
  refine eq_one_of_halfRule_three hL1 hL2 ?_ hinv
    (fun h => ((placeFrobValue_eq_of_localClassHom_eq_pair hres hζ (hzQ.1 h)).trans hsym))
    (fun h => placeFrobValue_eq_one_of_localClassHom_eq_one hres hζ (hzQ.2 h))
    (fun h => ((placeFrobValue_eq_of_localClassHom_eq_pair hres hζ (hzR.1 h)).trans
      (hpig'.trans hsym)))
    (fun h => placeFrobValue_eq_one_of_localClassHom_eq_one hres hζ (hzR.2 h))
  rw [← pow_two]
  exact pow_placeFrobValue_eq_one hres hζ _ _

end Orbits

end InverseGalois.CFT
