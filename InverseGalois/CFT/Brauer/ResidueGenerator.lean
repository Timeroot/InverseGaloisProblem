/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.DivisionTeichmuller
import InverseGalois.CFT.Brauer.InvariantBaseChange
import InverseGalois.CFT.Brauer.ResidueCard

/-!
# A generator of the residues with a prescribed power

The Teichmüller lift of a generator of the residues of a complete field is a root of unity of order
one less than the number of residues whose powers meet every element of absolute value one.  Its
power of complementary exponent is then a root of unity of order the exponent, and the roots of
unity of that order form a cyclic group, so a prescribed root of unity of that order is a power of
it with an exponent prime to the order.

Replacing the generator by the corresponding power of itself makes the prescribed root of unity the
value of the complementary power exactly, and the replacement is still a generator provided the
exponent is prime to one less than the number of residues.  An exponent prime to the order lifts to
an exponent prime to one less than the number of residues, because reduction of the units of one
cyclic group of residues onto the units of a quotient is surjective.  So a prescribed root of unity
whose order divides one less than the number of residues is the complementary power of some
generator of the residues.

## Main results

* `InverseGalois.CFT.exists_norm_eq_one_pow_eq_of_isPrimitiveRoot`: **a root of unity of order
  dividing one less than the number of residues is the power of complementary exponent of an
  element of absolute value one whose powers meet every element of absolute value one.**
* `InverseGalois.CFT.exists_valued_eq_one_pow_eq_of_isPrimitiveRoot`: the same statement for the
  completion of a number field at a finite place, in terms of its valuation.

## Tags

local field, residue field, Teichmüller lift, root of unity, primitive root, generator, class field
theory
-/

namespace InverseGalois.CFT

/-! ### The generator attached to a root of unity -/

section Generic

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]

variable (K) in
/-- **A root of unity of order dividing one less than the number of residues is the power of
complementary exponent of an element of absolute value one whose powers meet every element of
absolute value one.**  The Teichmüller lift of a generator of the residues has such a power of
order the prescribed one, the prescribed root of unity is a power of that with exponent prime to
the order, and any lift of that exponent to one prime to the order of the Teichmüller lift replaces
the generator by another one with the prescribed power. -/
theorem exists_norm_eq_one_pow_eq_of_isPrimitiveRoot {N : ℕ} (hN : N ≠ 0)
    (hdvd : N ∣ Nat.card (DivisionResidue K K) - 1) {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    ∃ u : K, ‖u‖ = 1 ∧ u ^ ((Nat.card (DivisionResidue K K) - 1) / N) = ζ ∧
      ∀ x : K, ‖x‖ = 1 → ∃ i : ℕ, ‖x - u ^ i‖ < 1 := by
  classical
  haveI : NeZero N := ⟨hN⟩
  have hQ1 : 1 < Nat.card (DivisionResidue K K) := Finite.one_lt_card
  set Q := Nat.card (DivisionResidue K K) with hQdef
  have hQ0 : Q - 1 ≠ 0 := by omega
  haveI : NeZero (Q - 1) := ⟨hQ0⟩
  set M := (Q - 1) / N with hMdef
  have hMN : M * N = Q - 1 := Nat.div_mul_cancel hdvd
  -- the Teichmüller lift of a generator of the residues
  obtain ⟨y, hypow, hyord, hycov⟩ := exists_rootOfUnity_pow_divisionNorm_sub_lt_one K K
  have hyprim : IsPrimitiveRoot y (Q - 1) := ⟨hypow, hyord⟩
  have hynorm : ‖y‖ = 1 := by
    have hp : ‖y‖ ^ (Q - 1) = 1 := by rw [← norm_pow, hypow, norm_one]
    rcases lt_trichotomy ‖y‖ 1 with hlt | heq | hgt
    · have hone := pow_lt_one₀ (norm_nonneg y) hlt hQ0
      rw [hp] at hone
      exact absurd hone (lt_irrefl 1)
    · exact heq
    · have hone := one_lt_pow₀ hgt hQ0
      rw [hp] at hone
      exact absurd hone (lt_irrefl 1)
  -- the prescribed root of unity is a power of the complementary power of that lift
  have hηprim : IsPrimitiveRoot (y ^ M) N := hyprim.pow (by omega) hMN.symm
  obtain ⟨s, -, hs⟩ := hηprim.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hspr : IsPrimitiveRoot ((y ^ M) ^ s) N := by rw [hs]; exact hζ
  have hscop : Nat.Coprime s N := (hηprim.pow_iff_coprime (Nat.pos_of_ne_zero hN) s).mp hspr
  -- an exponent prime to one less than the number of residues reducing to it
  obtain ⟨t, htcop, htmod⟩ : ∃ t : ℕ, Nat.Coprime t (Q - 1) ∧ (t : ZMod N) = (s : ZMod N) := by
    obtain ⟨tu, htu⟩ := ZMod.unitsMap_surjective (m := Q - 1) (n := N) hdvd
      (ZMod.unitOfCoprime s hscop)
    refine ⟨((tu : ZMod (Q - 1))).val, ZMod.val_coe_unit_coprime tu, ?_⟩
    have h2 : ((ZMod.unitsMap hdvd tu : (ZMod N)ˣ) : ZMod N)
        = ((tu : ZMod (Q - 1)).cast : ZMod N) := rfl
    rw [htu, ZMod.coe_unitOfCoprime] at h2
    rw [ZMod.natCast_val]
    exact h2.symm
  refine ⟨y ^ t, by rw [norm_pow, hynorm, one_pow], ?_, ?_⟩
  · rw [← pow_mul, mul_comm t M, pow_mul]
    refine Eq.trans ?_ hs
    refine (hηprim.isOfFinOrder hN).pow_eq_pow_iff_modEq.mpr ?_
    rw [← hηprim.eq_orderOf]
    exact (ZMod.natCast_eq_natCast_iff t s N).mp htmod
  · intro x hx
    obtain ⟨i, hi⟩ := hycov x (by rw [divisionNorm_base]; exact hx)
    rw [divisionNorm_base] at hi
    set jz : ZMod (Q - 1) := (ZMod.unitOfCoprime t htcop)⁻¹ * (i : ZMod (Q - 1)) with hjzdef
    refine ⟨jz.val, ?_⟩
    have hcancel : (t : ZMod (Q - 1)) * jz = (i : ZMod (Q - 1)) := by
      have hu : ((ZMod.unitOfCoprime t htcop : (ZMod (Q - 1))ˣ) : ZMod (Q - 1))
          = (t : ZMod (Q - 1)) := ZMod.coe_unitOfCoprime t htcop
      rw [hjzdef, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
    have hpow : (y ^ t) ^ jz.val = y ^ i := by
      rw [← pow_mul]
      refine (hyprim.isOfFinOrder hQ0).pow_eq_pow_iff_modEq.mpr ?_
      rw [← hyprim.eq_orderOf]
      refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id]
      exact hcancel
    rw [hpow]
    exact hi

end Generic

/-! ### The completion of a number field at a finite place -/

section Adic

open IsDedekindDomain NumberField

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- **A root of unity of a completion whose order divides one less than the number of residues is
the power of complementary exponent of a unit of the completion whose powers meet every unit.** -/
theorem exists_valued_eq_one_pow_eq_of_isPrimitiveRoot {N : ℕ} (hN : N ≠ 0)
    (hdvd : N ∣ Nat.card (DivisionResidue (v.adicCompletion K) (v.adicCompletion K)) - 1)
    {ζ : v.adicCompletion K} (hζ : IsPrimitiveRoot ζ N) :
    ∃ u : v.adicCompletion K, Valued.v u = 1 ∧
      u ^ ((Nat.card (DivisionResidue (v.adicCompletion K) (v.adicCompletion K)) - 1) / N) = ζ ∧
      ∀ x : v.adicCompletion K, Valued.v x = 1 → ∃ i : ℕ, Valued.v (x - u ^ i) < 1 := by
  obtain ⟨u, hunorm, hupow, hucov⟩ :=
    exists_norm_eq_one_pow_eq_of_isPrimitiveRoot (v.adicCompletion K) hN hdvd hζ
  refine ⟨u, norm_eq_one_iff_valued_eq_one.1 hunorm, hupow, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ := hucov x (norm_eq_one_iff_valued_eq_one.2 hx)
  exact ⟨i, Valued.toNormedField.norm_lt_one_iff.1 hi⟩

end Adic

end InverseGalois.CFT
