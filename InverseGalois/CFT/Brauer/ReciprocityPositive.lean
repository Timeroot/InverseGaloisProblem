/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.RealSymbolPositive
import InverseGalois.CFT.Brauer.SymbolProduct
import InverseGalois.CFT.Brauer.SymbolReciprocity

/-!
# Reciprocity for a second argument positive at every real embedding

The product formula over all the places of a number field splits into a product of power residue
symbols over the finite places and a product of symbols over the infinite ones.  A second argument
which every real embedding sends to a positive number contributes nothing to the archimedean half,
so for such an argument the finite half is by itself trivial.

That is the shape of the product formula which the reciprocity law between two units, each
unramified away from a single finite place, really needs.  Asking the second unit to be positive at
every real embedding replaces the demand that minus one be a power of the exponent, which at the
exponent two forces the field to be totally complex and so cannot be met by a field with a real
place.

## Main results

* `InverseGalois.CFT.prod_localSymbol_eq_one_of_forall_pos`: **the product formula for the power
  residue symbol over the finite places, for a second argument positive at every real embedding.**
* `InverseGalois.CFT.placeFrobValue_zpow_eq_zpow_of_forall_pos`: **reciprocity between two units
  each unramified away from a single place, the second positive at every real embedding.**

## Tags

power residue symbol, product formula, reciprocity, totally positive, Frobenius, number field,
class field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section Positive

variable {k : Type} [Field k] [NumberField k] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 k) → ℕ}

/-- **The product formula for the power residue symbol over the finite places, for a second
argument positive at every real embedding.**  The archimedean half of the product formula is
trivial for such an argument, so the finite half is trivial on its own. -/
theorem prod_localSymbol_eq_one_of_forall_pos (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) (a : kˣ) {b : kˣ} (hb : ∀ φ : k →+* ℝ, 0 < φ (b : k))
    (S : Finset (HeightOneSpectrum (𝓞 k)))
    (hS : ∀ v ∉ S,
      localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1) :
    ∏ v ∈ S, localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1 := by
  have h := prod_localSymbol_mul_prod_archSymbol_eq_one hn hres hζ a b S hS
  rwa [prod_archSymbol_eq_one_of_forall_pos a b hb, mul_one] at h

/-- **Reciprocity between two units of a number field each unramified away from a single place**,
for a prime exponent whose roots of unity the field contains and a second unit positive at every
real embedding.  The first unit is asked to be a power in every completion whose residue
characteristic divides the exponent, which makes its symbol trivial there; away from the two
exceptional places both units have value divisible by the exponent, so their symbol is trivial as
well; and the product formula leaves the two exceptional places, at each of which the symbol is a
value at a Frobenius automorphism raised to a value. -/
theorem placeFrobValue_zpow_eq_zpow_of_forall_pos (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) {v w : HeightOneSpectrum (𝓞 k)} (hvw : v ≠ w)
    (hvn : ¬ P v ∣ n) (hwn : ¬ P w ∣ n) {a b : kˣ}
    (hbpos : ∀ φ : k →+* ℝ, 0 < φ (b : k))
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
  have hprod := prod_localSymbol_eq_one_of_forall_pos hn hres hζ a hbpos {v, w} hS
  rw [Finset.prod_pair hvw, localSymbol_eq_placeFrobValue_zpow_right hn hres hζ hvn (hb v hvw) a,
    localSymbol_eq_placeFrobValue_zpow hn hres hζ hwn (ha w (Ne.symm hvw)) b] at hprod
  exact (inv_mul_eq_one.mp hprod).symm

end Positive

end InverseGalois.CFT
