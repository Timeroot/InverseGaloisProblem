/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.SymbolProduct
import InverseGalois.CFT.Brauer.TameUnramified

/-!
# Reciprocity between two units of a number field ramified at a single place each

A unit of a number field whose value at a finite place is divisible by the exponent has a value at
the Frobenius automorphism of that place, its norm residue symbol there against a uniformiser.  Two
units, each of which has value divisible by the exponent at every finite place but one, and the
first of which is a power in every completion whose residue characteristic divides the exponent,
satisfy a reciprocity law: the value of the first at the Frobenius automorphism of the exceptional
place of the second, raised to the value of the second there, is the value of the second at the
Frobenius automorphism of the exceptional place of the first, raised to the value of the first
there.

This is the product formula, read once the two exceptional places are the only ones which can
contribute.  At a place with residue characteristic dividing the exponent the first unit is a power,
so the symbol is trivial.  At every other place away from the two exceptional ones both units have
value divisible by the exponent, and the symbol of two such units is trivial.  What is left is the
symbol at the exceptional place of the first, where the second unit is unramified, and the symbol
at the exceptional place of the second, where the first unit is unramified; each of those is a
value at a Frobenius automorphism raised to a value, and they are mutually inverse.

## Main definitions

* `InverseGalois.CFT.placeFrobValue`: **the value of a unit of a number field at the Frobenius
  automorphism of a finite place.**

## Main results

* `InverseGalois.CFT.placeFrobValue_mul`, `InverseGalois.CFT.placeFrobValue_inv`: the value at a
  Frobenius automorphism is a homomorphism.
* `InverseGalois.CFT.placeFrobValue_eq_one_iff`: the value of a unit at the Frobenius automorphism
  of a place where it is unramified is trivial exactly when it is a power in the completion.
* `InverseGalois.CFT.localSymbol_eq_placeFrobValue_zpow`,
  `InverseGalois.CFT.localSymbol_eq_placeFrobValue_zpow_right`: the norm residue symbol at a place
  where one argument is unramified is the value of that argument at the Frobenius automorphism,
  raised to the value of the other argument.
* `InverseGalois.CFT.placeFrobValue_zpow_eq_zpow`: **reciprocity between two units each unramified
  away from a single place.**

## Tags

norm residue symbol, power residue symbol, product formula, reciprocity, Frobenius, unramified,
number field, class field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### The value of a unit at the Frobenius automorphism of a place -/

section Reciprocity

variable {k : Type} [Field k] [NumberField k] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 k) → ℕ}

/-- **The value of a unit of a number field at the Frobenius automorphism of a finite place**: the
value at the Frobenius automorphism of the image of that unit in the completion. -/
noncomputable def placeFrobValue (hres : ∀ v : HeightOneSpectrum (𝓞 k),
    HasResidueChar (v.adicCompletion k) (P v) (E v)) {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (v : HeightOneSpectrum (𝓞 k)) (a : kˣ) : Multiplicative QModZ :=
  frobValue (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
    (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
    (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)

theorem placeFrobValue_def (hres : ∀ v : HeightOneSpectrum (𝓞 k),
    HasResidueChar (v.adicCompletion k) (P v) (E v)) {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (v : HeightOneSpectrum (𝓞 k)) (a : kˣ) :
    placeFrobValue hres hζ v a
      = frobValue (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a) := rfl

/-- The value at a Frobenius automorphism is multiplicative. -/
theorem placeFrobValue_mul (hres : ∀ v : HeightOneSpectrum (𝓞 k),
    HasResidueChar (v.adicCompletion k) (P v) (E v)) {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (v : HeightOneSpectrum (𝓞 k)) (a b : kˣ) :
    placeFrobValue hres hζ v (a * b)
      = placeFrobValue hres hζ v a * placeFrobValue hres hζ v b := by
  rw [placeFrobValue_def, placeFrobValue_def, placeFrobValue_def, _root_.map_mul, _root_.map_mul]

/-- The value at a Frobenius automorphism takes a reciprocal to a reciprocal. -/
theorem placeFrobValue_inv (hres : ∀ v : HeightOneSpectrum (𝓞 k),
    HasResidueChar (v.adicCompletion k) (P v) (E v)) {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (v : HeightOneSpectrum (𝓞 k)) (a : kˣ) :
    placeFrobValue hres hζ v a⁻¹ = (placeFrobValue hres hζ v a)⁻¹ := by
  rw [placeFrobValue_def, placeFrobValue_def, _root_.map_inv, _root_.map_inv]

/-- The value at a Frobenius automorphism is killed by the exponent. -/
theorem pow_placeFrobValue_eq_one (hres : ∀ v : HeightOneSpectrum (𝓞 k),
    HasResidueChar (v.adicCompletion k) (P v) (E v)) {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (v : HeightOneSpectrum (𝓞 k)) (a : kˣ) : placeFrobValue hres hζ v a ^ n = 1 :=
  pow_frobValue_eq_one _ _ _ _

/-- **The value at the Frobenius automorphism of a place where a unit has value divisible by the
exponent is trivial exactly when that unit is a power in the completion.** -/
theorem placeFrobValue_eq_one_iff (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) {v : HeightOneSpectrum (𝓞 k)} (hv : ¬ P v ∣ n) {a : kˣ}
    (ha : (n : ℤ) ∣ placeValue v a) :
    placeFrobValue hres hζ v a = 1
      ↔ ∃ c : (v.adicCompletion k)ˣ,
          c ^ n = Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a :=
  frobValue_eq_one_iff _ _ _ hn hv ha

/-- **The norm residue symbol at a place where the first argument has value divisible by the
exponent** is the value of that argument at the Frobenius automorphism, raised to the value of the
second argument. -/
theorem localSymbol_eq_placeFrobValue_zpow (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) {v : HeightOneSpectrum (𝓞 k)} (hv : ¬ P v ∣ n) {a : kˣ}
    (ha : (n : ℤ) ∣ placeValue v a) (b : kˣ) :
    localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b)
      = placeFrobValue hres hζ v a ^ placeValue v b :=
  localSymbol_eq_frobValue_zpow _ _ _ hn hv ha _

/-- **The norm residue symbol at a place where the second argument has value divisible by the
exponent** is the inverse of the value of that argument at the Frobenius automorphism, raised to
the value of the first argument. -/
theorem localSymbol_eq_placeFrobValue_zpow_right (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) {v : HeightOneSpectrum (𝓞 k)} (hv : ¬ P v ∣ n) {b : kˣ}
    (hb : (n : ℤ) ∣ placeValue v b) (a : kˣ) :
    localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b)
      = (placeFrobValue hres hζ v b ^ placeValue v a)⁻¹ :=
  localSymbol_eq_frobValue_zpow_right _ _ _ hn hv hb _

/-- **Reciprocity between two units of a number field each unramified away from a single place**,
for an odd prime exponent whose roots of unity the field contains.  The first unit is asked to be a
power in every completion whose residue characteristic divides the exponent, which makes its symbol
trivial there; away from the two exceptional places both units have value divisible by the
exponent, so their symbol is trivial as well; and the product formula leaves the two exceptional
places, at each of which the symbol is a value at a Frobenius automorphism raised to a value. -/
theorem placeFrobValue_zpow_eq_zpow (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) {v w : HeightOneSpectrum (𝓞 k)} (hvw : v ≠ w)
    (hvn : ¬ P v ∣ n) (hwn : ¬ P w ∣ n) {a b : kˣ}
    (ha : ∀ u : HeightOneSpectrum (𝓞 k), u ≠ v → (n : ℤ) ∣ placeValue u a)
    (hb : ∀ u : HeightOneSpectrum (𝓞 k), u ≠ w → (n : ℤ) ∣ placeValue u b)
    (hap : ∀ u : HeightOneSpectrum (𝓞 k), P u ∣ n →
      ∃ c : (u.adicCompletion k)ˣ,
        c ^ n = Units.map (algebraMap k (u.adicCompletion k)).toMonoidHom a) :
    placeFrobValue hres hζ w a ^ placeValue w b
      = placeFrobValue hres hζ v b ^ placeValue v a := by
  classical
  have hS : ∀ u : HeightOneSpectrum (𝓞 k), u ∉ ({v, w} : Finset (HeightOneSpectrum (𝓞 k))) →
      localSymbol (hres u) (isUnitValGen_one (valued_adicCompletion_surjective u))
        (hζ.map_of_injective (algebraMap k (u.adicCompletion k)).injective)
        (Units.map (algebraMap k (u.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (u.adicCompletion k)).toMonoidHom b) = 1 := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    push_neg at hu
    by_cases hun : P u ∣ n
    · exact localSymbol_eq_one_of_isPow_left _ _ _ (hap u hun) _
    · exact localSymbol_eq_one_of_dvd_of_dvd _ _ _ hn hun (ha u hu.1) (hb u hu.2)
  have hprod := prod_localSymbol_eq_one_of_ne_two hn hn2 hres hζ a b {v, w} hS
  rw [Finset.prod_pair hvw, localSymbol_eq_placeFrobValue_zpow_right hn hres hζ hvn (hb v hvw) a,
    localSymbol_eq_placeFrobValue_zpow hn hres hζ hwn (ha w (Ne.symm hvw)) b] at hprod
  exact (inv_mul_eq_one.mp hprod).symm

end Reciprocity

end InverseGalois.CFT
