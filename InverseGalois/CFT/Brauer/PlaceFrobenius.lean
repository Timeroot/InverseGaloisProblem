/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.FrobeniusBaseChange
import InverseGalois.CFT.Brauer.PlaceUnramified
import InverseGalois.CFT.Local.RootOfUnityValued

/-!
# The Frobenius of a completion on the roots of unity

The splitting theory of division algebras measures an element of the completion `K_w` by the
absolute value `divisionNorm`, the degree-th root of the absolute value of its algebra norm, while
the arithmetic of the completion measures it by the valuation it carries as a completion.  At a
place whose ramification index is one the two agree on the questions that matter: an element is an
integer for one exactly when it is an integer for the other, and it is congruent to zero for one
exactly when it is congruent to zero for the other.  Indeed the value of the algebra norm is the
degree-th power of the value, and a degree-th power is at most one exactly when its base is.

Consequently the Frobenius automorphism of the completion, which is defined by its effect on the
residues of the division algebra, raises every integer to the power given by the number of residues
of the base, modulo the maximal ideal.  Roots of unity of order invertible in the residue field are
separated by the maximal ideal, so **the Frobenius raises such a root of unity to the power given by
the number of residues of the base**, with no choice left.  This is the cyclotomic description of
the Frobenius, and it is obtained here without ever constructing a global Frobenius element.

## Main results

* `InverseGalois.CFT.divisionNorm_le_one_iff_adicCompletion`: at an unramified place the integers of
  the division algebra are the integers of the valuation.
* `InverseGalois.CFT.divisionNorm_lt_one_iff_adicCompletion`: at an unramified place the maximal
  ideal of the division algebra is the maximal ideal of the valuation.
* `InverseGalois.CFT.isValuedFrobenius_of_isDivisionFrobenius`: **at an unramified place a Frobenius
  for the division algebra is a Frobenius for the valuation.**
* `InverseGalois.CFT.divisionFrobenius_rootOfUnity_adicCompletion`: **the Frobenius of a completion
  raises a root of unity of order invertible in the residue field to the power given by the number
  of residues of the base.**
* `InverseGalois.CFT.restrictToBase_divisionFrobenius_rootOfUnity`: the same for a root of unity of
  the number field itself.

## Tags

number field, completion, unramified place, Frobenius, root of unity, division algebra, class field
theory
-/

set_option synthInstance.maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module MulAction NumberField

/-! ### The value of a natural number in a completion -/

section NatCast

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

/-- The value of a natural number in the completion is its value in the number field. -/
theorem valued_natCast_adicCompletion (m : ℕ) :
    Valued.v ((m : ℕ) : w.adicCompletion K) = w.valuation K (m : K) := by
  rw [← map_natCast (toAdicCompletion w) m, toAdicCompletion_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

end NatCast

section PlaceFrobenius

attribute [local instance] isGalois_adicCompletion

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

/-! ### The two measures of an element of the completion -/

variable (k) in
/-- **At an unramified place the integers of the division algebra are the integers of the
valuation.**  The absolute value of the division algebra is the degree-th root of the absolute value
of the algebra norm, whose value is the degree-th power of the value of the element. -/
theorem divisionNorm_le_one_iff_adicCompletion (hram : ramIdx (𝓞 k) w = 1)
    (z : w.adicCompletion K) :
    divisionNorm ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) z ≤ 1
      ↔ Valued.v z ≤ 1 := by
  have hn0 : finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) ≠ 0 :=
    (Module.finrank_pos (R := (primeUnder (𝓞 k) w).adicCompletion k)
      (M := w.adicCompletion K)).ne'
  have hpos : (0 : ℝ)
      < 1 / (finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) : ℝ) :=
    div_pos one_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0))
  have hrp := Real.rpow_le_rpow_iff
    (norm_nonneg (Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) z)) zero_le_one hpos
  rw [Real.one_rpow] at hrp
  have hnorm : ‖Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) z‖ ≤ 1
      ↔ Valued.v (Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) z) ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff
  rw [divisionNorm, hrp, hnorm, valued_algebraNorm_adicCompletion k w hram z]
  exact pow_le_one_iff_of_nonneg zero_le' hn0

variable (k) in
/-- **At an unramified place the maximal ideal of the division algebra is the maximal ideal of the
valuation**, for the same reason that the two rings of integers agree. -/
theorem divisionNorm_lt_one_iff_adicCompletion (hram : ramIdx (𝓞 k) w = 1)
    (z : w.adicCompletion K) :
    divisionNorm ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) z < 1
      ↔ Valued.v z < 1 := by
  have hn0 : finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) ≠ 0 :=
    (Module.finrank_pos (R := (primeUnder (𝓞 k) w).adicCompletion k)
      (M := w.adicCompletion K)).ne'
  have hpos : (0 : ℝ)
      < 1 / (finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) : ℝ) :=
    div_pos one_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0))
  have hrp := Real.rpow_lt_rpow_iff
    (norm_nonneg (Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) z)) zero_le_one hpos
  rw [Real.one_rpow] at hrp
  have hnorm : ‖Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) z‖ < 1
      ↔ Valued.v (Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) z) < 1 :=
    Valued.toNormedField.norm_lt_one_iff
  rw [divisionNorm, hrp, hnorm, valued_algebraNorm_adicCompletion k w hram z]
  exact pow_lt_one_iff_of_nonneg zero_le' hn0

/-! ### The Frobenius in the language of the valuation -/

variable (k) in
/-- **At an unramified place a Frobenius for the division algebra is a Frobenius for the
valuation.**  Being an integer and being congruent to zero mean the same for the two measures. -/
theorem isValuedFrobenius_of_isDivisionFrobenius (hram : ramIdx (𝓞 k) w = 1)
    {σ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K}
    (hσ : IsDivisionFrobenius σ) :
    IsValuedFrobenius (Nat.card (DivisionResidue ((primeUnder (𝓞 k) w).adicCompletion k)
      ((primeUnder (𝓞 k) w).adicCompletion k))) σ := by
  intro x hx
  have hmem : x ∈ divisionIntegers ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) :=
    mem_divisionIntegers.2 ((divisionNorm_le_one_iff_adicCompletion k w hram x).2 hx)
  exact (divisionNorm_lt_one_iff_adicCompletion k w hram _).1
    ((isDivisionFrobenius_iff σ).1 hσ ⟨x, hmem⟩)

variable (k) in
/-- **A Frobenius of a completion raises a root of unity of order invertible in the residue field to
the power given by the number of residues of the base.**  The image and the power are roots of unity
of the same order which are congruent modulo the maximal ideal, and such roots of unity are
separated by it. -/
theorem apply_rootOfUnity_of_isDivisionFrobenius (hram : ramIdx (𝓞 k) w = 1)
    {σ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K}
    (hσ : IsDivisionFrobenius σ) {m : ℕ} (hm : m ≠ 0)
    (hmv : Valued.v ((m : ℕ) : w.adicCompletion K) = 1) {ζ : w.adicCompletion K}
    (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ Nat.card (DivisionResidue ((primeUnder (𝓞 k) w).adicCompletion k)
      ((primeUnder (𝓞 k) w).adicCompletion k)) :=
  (isValuedFrobenius_of_isDivisionFrobenius k w hram hσ).apply_rootOfUnity hm hmv hζ

variable (k) in
/-- **The Frobenius of a completion raises a root of unity of order invertible in the residue field
to the power given by the number of residues of the base.**  This is the cyclotomic description of
the Frobenius of an unramified place. -/
theorem divisionFrobenius_rootOfUnity_adicCompletion (hram : ramIdx (𝓞 k) w = 1) {m : ℕ}
    (hm : m ≠ 0) (hmv : Valued.v ((m : ℕ) : w.adicCompletion K) = 1)
    {ζ : w.adicCompletion K} (hζ : ζ ^ m = 1) :
    divisionFrobenius ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
        (fun z hz => exists_divisionNorm_eq_norm_adicCompletion k w hram z hz) ζ
      = ζ ^ Nat.card (DivisionResidue ((primeUnder (𝓞 k) w).adicCompletion k)
        ((primeUnder (𝓞 k) w).adicCompletion k)) :=
  apply_rootOfUnity_of_isDivisionFrobenius k w hram
    (isDivisionFrobenius_divisionFrobenius _ _ _) hm hmv hζ

/-! ### The Frobenius on the roots of unity of the number field -/

variable (k) in
/-- **The Frobenius of a completion raises a root of unity of the number field to the power given by
the number of residues of the base.**  Every automorphism of the completion restricts to an
automorphism of the extension, compatibly with the inclusion of the extension into its completion,
so the statement about the completion is a statement about the extension. -/
theorem restrictToBase_divisionFrobenius_rootOfUnity (hram : ramIdx (𝓞 k) w = 1) {m : ℕ}
    (hm : m ≠ 0) (hmv : w.valuation K (m : K) = 1) {ζ : K} (hζ : ζ ^ m = 1) :
    restrictToBase k w (divisionFrobenius ((primeUnder (𝓞 k) w).adicCompletion k)
        (w.adicCompletion K)
        (fun z hz => exists_divisionNorm_eq_norm_adicCompletion k w hram z hz)) ζ
      = ζ ^ Nat.card (DivisionResidue ((primeUnder (𝓞 k) w).adicCompletion k)
        ((primeUnder (𝓞 k) w).adicCompletion k)) := by
  refine (toAdicCompletion w).injective ?_
  rw [toAdicCompletion_restrictToBase k w _ ζ, map_pow]
  exact divisionFrobenius_rootOfUnity_adicCompletion k w hram hm
    (by rw [valued_natCast_adicCompletion w m]; exact hmv)
    (by rw [← map_pow, hζ, map_one])

end PlaceFrobenius

end InverseGalois.CFT
