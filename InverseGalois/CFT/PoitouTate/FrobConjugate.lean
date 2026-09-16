/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ClosingChain
import InverseGalois.CFT.PoitouTate.ConfinedDiagonal

/-!
# The value at a Frobenius automorphism of a conjugated place, for the exponent two

For the exponent two the value of a unit of a number field at the Frobenius automorphism of a
finite place is determined by whether the unit is a square in the completion there: such a value is
killed by two, and the rationals modulo the integers contain exactly two elements killed by two, so
a value killed by two is read off from its triviality alone.

That rigidity carries the value along the Galois group.  A Galois automorphism identifies the
completion at a place with the completion at the image of the place, so a unit is a square at a
place exactly when its image is a square at the image of the place; the two values at the Frobenius
automorphisms are then trivial together, hence equal.

## Main results

* `InverseGalois.CFT.eq_of_sq_eq_one_of_eq_one_iff`: two elements of the rationals modulo the
  integers killed by two which are trivial together are equal.
* `InverseGalois.CFT.placeFrobValue_eq_one_iff_localClassHom_eq_one`: the value of a unit at the
  Frobenius automorphism of a place where it is unramified is trivial exactly when its local class
  there is trivial.
* `InverseGalois.CFT.placeFrobValue_galUnits`: **the value at the Frobenius automorphism of the
  image of a place, of the image of a unit, is the value of the unit at the Frobenius automorphism
  of the place**, for the exponent two.

## Tags

power residue symbol, Frobenius, conjugate place, quadratic, number field, class field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### Two elements killed by two -/

section Torsion

/-- **Two elements of the rationals modulo the integers killed by two which are trivial together
are equal.**  Each is a multiple of one half, and there are only two such multiples. -/
theorem eq_of_sq_eq_one_of_eq_one_iff {x y : Multiplicative QModZ} (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) (h : x = 1 ↔ y = 1) : x = y := by
  have key : ∀ c : ZMod 2, Multiplicative.ofAdd (zmodQModZ 2 c) = 1 ↔ c = 0 := by
    intro c
    rw [_root_.ofAdd_eq_one]
    exact ⟨fun hc => zmodQModZ_injective 2 (by rw [hc, map_zero]), fun hc => by rw [hc, map_zero]⟩
  obtain ⟨c, hc⟩ := mem_range_zmodQModZ_of_pow_eq_one 2 hx
  obtain ⟨d, hd⟩ := mem_range_zmodQModZ_of_pow_eq_one 2 hy
  have hc' : Multiplicative.ofAdd (zmodQModZ 2 c) = x := hc
  have hd' : Multiplicative.ofAdd (zmodQModZ 2 d) = y := hd
  rw [← hc', ← hd'] at h ⊢
  have hall : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  rw [hall c d (by rw [← key c, ← key d]; exact h)]

end Torsion

/-! ### The value at a Frobenius automorphism and the local class -/

section Class

variable {k : Type} [Field k] [NumberField k] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 k) → ℕ}

/-- The value of the trivial unit at a Frobenius automorphism is trivial. -/
theorem placeFrobValue_one (hres : ∀ v : HeightOneSpectrum (𝓞 k),
    HasResidueChar (v.adicCompletion k) (P v) (E v)) {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (v : HeightOneSpectrum (𝓞 k)) : placeFrobValue hres hζ v 1 = 1 := by
  rw [placeFrobValue_def, _root_.map_one, _root_.map_one]

/-- **The value of a unit at the Frobenius automorphism of a place where it is unramified is
trivial exactly when its local class there is trivial.** -/
theorem placeFrobValue_eq_one_iff_localClassHom_eq_one (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) {v : HeightOneSpectrum (𝓞 k)} (hv : ¬ P v ∣ n) {a : kˣ}
    (ha : (n : ℤ) ∣ placeValue v a) :
    placeFrobValue hres hζ v a = 1 ↔ localClassHom v n a = 1 := by
  refine ⟨localClassHom_eq_one_of_placeFrobValue_eq_one hn hres hζ hv ha, fun h => ?_⟩
  rw [placeFrobValue_eq_of_localClassHom_eq hres hζ v (b := 1) (by rw [h, _root_.map_one])]
  exact placeFrobValue_one hres hζ v

end Class

/-! ### Moving the place -/

section Move

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **The value at the Frobenius automorphism of the image of a place, of the image of a unit, is
the value of the unit at the Frobenius automorphism of the place**, for the exponent two.  Both
values are killed by two, and each is trivial exactly when the unit is a square in the completion,
a property the automorphism carries from one completion to the other. -/
theorem placeFrobValue_galUnits (hres : ∀ v : HeightOneSpectrum (𝓞 K),
    HasResidueChar (v.adicCompletion K) (P v) (E v)) {ζ : K} (hζ : IsPrimitiveRoot ζ 2)
    (σ : Gal(K/k)) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ P v ∣ 2) (hσv : ¬ P (σ • v) ∣ 2)
    {a : Kˣ} (ha : (2 : ℤ) ∣ placeValue v a) :
    placeFrobValue hres hζ (σ • v) (galUnits σ a) = placeFrobValue hres hζ v a := by
  refine eq_of_sq_eq_one_of_eq_one_iff (pow_placeFrobValue_eq_one hres hζ _ _)
    (pow_placeFrobValue_eq_one hres hζ _ _) ?_
  rw [placeFrobValue_eq_one_iff_localClassHom_eq_one Nat.prime_two hres hζ hσv
      (by rw [placeValue_galSmul]; exact ha),
    placeFrobValue_eq_one_iff_localClassHom_eq_one Nat.prime_two hres hζ hv ha]
  exact localClassHom_galUnits_eq_one_iff σ v 2 a

end Move

end InverseGalois.CFT
