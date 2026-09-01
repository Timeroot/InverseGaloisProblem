/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.DivisionResidueBase
import InverseGalois.CFT.Local.AdicLocalField
import InverseGalois.CFT.Local.PrimeResidueField
import InverseGalois.CFT.Local.RatResidueDegree
import InverseGalois.CFT.Units.CompletionFinite

/-!
# The number of residues of a completion whose residue field is the prime field

The Frobenius of a completion raises a root of unity to the power given by the number of residues
of the base field, so a description of the Frobenius as a cyclotomic operation needs that number.
When the residue field is no bigger than the prime field, the number is the residue characteristic
itself.

The argument is elementary once the residue ring is in hand.  The residues of a field are a finite
ring without zero divisors, and every one of them is the residue of a rational integer as soon as
every integer of the field is congruent to a rational integer.  A rational integer is congruent to
one of `p` of them, because the residue characteristic is congruent to zero, so there are at most
`p` residues; and the additive order of the residue of one is exactly `p`, so there are at least
that many.  A place of a number field whose residue degree over the rational prime below it is one
has both properties, so its completion has exactly `p` residues.

## Main results

* `InverseGalois.CFT.surjective_intCast_divisionResidue`: every residue is the residue of a
  rational integer.
* `InverseGalois.CFT.natCard_divisionResidue_eq_prime`: **a field whose integers are congruent to
  rational integers and whose residue characteristic is `p` has exactly `p` residues.**
* `InverseGalois.CFT.natCard_divisionResidue_adicCompletion_eq_prime`: **the completion of a number
  field at a place of residue degree one over `p` has exactly `p` residues.**
* `InverseGalois.CFT.natCard_divisionResidue_adicCompletion_rat`: **the completion of the rationals
  at a finite place has exactly as many residues as the rational prime the place contains.**

## Tags

local field, residue field, residue degree, residue characteristic, adic completion, class field
theory
-/

namespace InverseGalois.CFT

/-! ### The residues of a field whose integers are the rational integers -/

section Generic

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] {p : ℕ}

/-- **Every residue is the residue of a rational integer**, as soon as every integer of the field
is congruent to a rational integer. -/
theorem surjective_intCast_divisionResidue
    (hsurj : ∀ x : K, ‖x‖ ≤ 1 → ∃ b : ℤ, ‖x - (b : K)‖ < 1) :
    Function.Surjective (Int.cast : ℤ → DivisionResidue K K) := by
  intro q
  obtain ⟨x, rfl⟩ := (divisionResidueCon K K).mk'_surjective q
  have hx : ‖(x : K)‖ ≤ 1 := by
    have := mem_divisionIntegers.1 x.2
    rwa [divisionNorm_base] at this
  obtain ⟨b, hb⟩ := hsurj (x : K) hx
  refine ⟨b, ?_⟩
  have hcast : ((b : ℤ) : DivisionResidue K K)
      = (((b : ℤ) : divisionIntegers K K) : DivisionResidue K K) :=
    (map_intCast (divisionResidueCon K K).mk' b).symm
  rw [hcast, RingCon.coe_mk']
  refine divisionResidue_eq_iff.2 ?_
  have hb' : ((((b : ℤ) : divisionIntegers K K) : K)) = ((b : ℤ) : K) := by push_cast; ring
  rw [divisionNorm_base, hb', ← norm_neg, neg_sub]
  exact hb

/-- **A field whose integers are congruent to rational integers and whose residue characteristic
is `p` has exactly `p` residues.**  Reducing a rational integer modulo `p` leaves at most `p`
residues, and the residue of one already has additive order `p`. -/
theorem natCard_divisionResidue_eq_prime (hp : p.Prime)
    (hsurj : ∀ x : K, ‖x‖ ≤ 1 → ∃ b : ℤ, ‖x - (b : K)‖ < 1) (hpn : ‖(p : K)‖ < 1) :
    Nat.card (DivisionResidue K K) = p := by
  -- the residue characteristic is congruent to zero
  have hp0 : ((p : ℕ) : DivisionResidue K K) = 0 := by
    have hcast : ((p : ℕ) : DivisionResidue K K)
        = (((p : ℕ) : divisionIntegers K K) : DivisionResidue K K) :=
      (map_natCast (divisionResidueCon K K).mk' p).symm
    have hp' : ((((p : ℕ) : divisionIntegers K K) : K)) = ((p : ℕ) : K) := by push_cast; ring
    rw [hcast, divisionResidue_eq_zero_iff, divisionNorm_base, hp']
    exact hpn
  -- so a rational integer is congruent to one of `p` of them
  have hle : Nat.card (DivisionResidue K K) ≤ p := by
    have hpz : ((p : ℤ)) ≠ 0 := Int.natCast_ne_zero.2 hp.ne_zero
    have hsurj' : Function.Surjective (fun i : Fin p => ((i : ℕ) : DivisionResidue K K)) := by
      intro y
      obtain ⟨b, rfl⟩ := surjective_intCast_divisionResidue hsurj y
      have hnn : (0 : ℤ) ≤ b % (p : ℤ) := Int.emod_nonneg b hpz
      have hlt : b % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos b (by exact_mod_cast hp.pos)
      refine ⟨⟨(b % (p : ℤ)).toNat, by omega⟩, ?_⟩
      show (((b % (p : ℤ)).toNat : ℕ) : DivisionResidue K K) = ((b : ℤ) : DivisionResidue K K)
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn, Int.emod_def]
      push_cast
      rw [hp0]
      ring
    calc Nat.card (DivisionResidue K K) ≤ Nat.card (Fin p) :=
          Nat.card_le_card_of_surjective _ hsurj'
      _ = p := by simp
  -- and the residue of one has additive order exactly `p`
  have hord : addOrderOf (1 : DivisionResidue K K) = p := by
    have hdvd : addOrderOf (1 : DivisionResidue K K) ∣ p :=
      addOrderOf_dvd_of_nsmul_eq_zero (by simpa using hp0)
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) one_ne_zero
    · exact h
  have hdvdcard : p ∣ Nat.card (DivisionResidue K K) := hord ▸ addOrderOf_dvd_natCard _
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvdcard)

end Generic

/-! ### The completion of a number field at a place of residue degree one -/

section Adic

open IsDedekindDomain NumberField

variable {K : Type} [Field K] [NumberField K] {p : ℕ}

/-- **The completion of a number field at a place of residue degree one over `p` has exactly `p`
residues.**  Residue degree one says that every integer of the completion is congruent to a
rational integer, and the rational prime below the place has valuation less than one there. -/
theorem natCard_divisionResidue_adicCompletion_eq_prime (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 K)) [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (hdeg : (Ideal.span {(p : ℤ)}).inertiaDeg v.asIdeal = 1) :
    Nat.card (DivisionResidue (v.adicCompletion K) (v.adicCompletion K)) = p := by
  refine natCard_divisionResidue_eq_prime hp (fun x hx => ?_) ?_
  · have hle : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := Valued.toNormedField.norm_le_one_iff
    obtain ⟨b, hb⟩ := exists_intCast_sub_lt_one_of_inertiaDeg_eq_one hp v hdeg (hle.1 hx)
    have hlt : ‖x - (b : v.adicCompletion K)‖ < 1
        ↔ Valued.v (x - (b : v.adicCompletion K)) < 1 := Valued.toNormedField.norm_lt_one_iff
    exact ⟨b, hlt.2 hb⟩
  · obtain ⟨e, he⟩ := exists_hasResidueChar_of_liesOver hp v
    have hepos := he.pos
    have hlt : ‖((p : ℕ) : v.adicCompletion K)‖ < 1
        ↔ Valued.v ((p : ℕ) : v.adicCompletion K) < 1 := Valued.toNormedField.norm_lt_one_iff
    refine hlt.2 ?_
    rw [he.val_p]
    simpa using WithZero.exp_lt_exp.mpr (show (-(e : ℤ)) < 0 by omega)

/-- **The completion of the rationals at a finite place has exactly as many residues as the rational
prime the place contains.**  Every finite place of the rationals has residue degree one over the
prime it contains. -/
theorem natCard_divisionResidue_adicCompletion_rat {q : ℕ} (hq : q.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Nat.card (DivisionResidue (v.adicCompletion ℚ) (v.adicCompletion ℚ)) = q := by
  haveI := liesOver_span_of_natCast_mem hq v hv
  exact natCard_divisionResidue_adicCompletion_eq_prime hq v (inertiaDeg_rat_eq_one hq v)

end Adic

end InverseGalois.CFT
