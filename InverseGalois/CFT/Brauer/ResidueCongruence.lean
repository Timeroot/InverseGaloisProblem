/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.ResidueCardDegree
import InverseGalois.CFT.Local.NatValuation
import InverseGalois.CFT.Local.PrimeResidue

/-!
# Congruences modulo a place, read in the completion

The local computation of an invariant produces a statement about the completion of a number field
at a finite place: a power of the coefficient differs from a power of a root of unity by something
of valuation less than one.  Comparing the places above one rational prime with that prime itself
is instead a computation in residue fields, where the coefficient is an algebraic integer and the
root of unity is represented by a natural number.

The bridge between the two is the observation that two integers of the number field have the same
reduction modulo a place exactly when their difference has valuation less than one in the
completion, because the valuation of an integer in the completion is its valuation in the number
field.  Together with the fact that a power of a difference of small valuation is again small, this
turns the local statement into a congruence between an algebraic integer raised to a power and a
natural number raised to the exponent naming the invariant.

The power in question is the complement, for the prescribed order, of the number of nonzero
residues, and the local computation writes that number as the number of residues of the completion
while the congruence writes it as the number of residues of the place.  Those two counts agree,
so the passage between the two forms of the statement is a rewriting.

## Main results

* `InverseGalois.CFT.mk_eq_mk_iff_valued_sub_lt_one`: **two integers of a number field agree modulo
  a place exactly when their difference is small in the completion there.**
* `InverseGalois.CFT.mk_pow_eq_mk_natCast_pow_of_valued`: **a power of an integer that is close to
  a power of a root of unity reduces modulo the place to the same power of the natural number
  representing that root.**
* `InverseGalois.CFT.mk_pow_eq_mk_natCast_pow_of_divisionResidue`: **the same, with the power
  written by the number of residues of the completion**, as the local computation produces it.

## Tags

number field, place, completion, residue field, congruence, valuation, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section ResidueCongruence

variable {K : Type} [Field K] [NumberField K]

/-- **Two integers of a number field agree modulo a place exactly when their difference is small in
the completion there**, because the valuation of an integer in the completion is its valuation in
the number field, and an integer lies in the place exactly when that valuation is less than one. -/
theorem mk_eq_mk_iff_valued_sub_lt_one (v : HeightOneSpectrum (𝓞 K)) (x y : 𝓞 K) :
    Ideal.Quotient.mk v.asIdeal x = Ideal.Quotient.mk v.asIdeal y ↔
      Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) x
        - algebraMap (𝓞 K) (v.adicCompletion K) y) < 1 := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub, valued_algebraMap_adicCompletion]
  exact (v.intValuation_lt_one_iff_mem _).symm

/-- **A power of an integer that is close to a power of a root of unity reduces modulo the place to
the same power of the natural number representing that root.**  A power of a difference of small
valuation is small, so the root of unity may be replaced by the natural number before the two
differences are added. -/
theorem mk_pow_eq_mk_natCast_pow_of_valued (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} {c m j : ℕ}
    {ζ : v.adicCompletion K} (hζ1 : Valued.v ζ ≤ 1)
    (hζres : Valued.v (ζ - ((c : ℕ) : v.adicCompletion K)) < 1)
    (hj : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) b ^ m - ζ ^ j) < 1) :
    Ideal.Quotient.mk v.asIdeal (b ^ m)
      = Ideal.Quotient.mk v.asIdeal (((c ^ j : ℕ) : 𝓞 K)) := by
  have hcz : Valued.v (ζ ^ j - ((c : ℕ) : v.adicCompletion K) ^ j) < 1 :=
    valued_sub_pow_lt_one hζ1 (valued_natCast_le_one c) hζres j
  rw [mk_eq_mk_iff_valued_sub_lt_one]
  have hsplit : algebraMap (𝓞 K) (v.adicCompletion K) (b ^ m)
      - algebraMap (𝓞 K) (v.adicCompletion K) ((c ^ j : ℕ) : 𝓞 K)
      = (algebraMap (𝓞 K) (v.adicCompletion K) b ^ m - ζ ^ j)
        + (ζ ^ j - ((c : ℕ) : v.adicCompletion K) ^ j) := by
    push_cast
    ring
  rw [hsplit]
  exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hj hcz)

/-- **A power of an integer that is close to a power of a root of unity reduces modulo the place to
the same power of the natural number representing that root**, with the power written by the number
of residues of the completion and the coefficient by its image in the number field, as the local
computation of an invariant produces them. -/
theorem mk_pow_eq_mk_natCast_pow_of_divisionResidue (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K}
    {c j N : ℕ} {ζ : v.adicCompletion K} (hζ1 : Valued.v ζ ≤ 1)
    (hζres : Valued.v (ζ - ((c : ℕ) : v.adicCompletion K)) < 1)
    (hj : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K b)
        ^ ((Nat.card (DivisionResidue (v.adicCompletion K) (v.adicCompletion K)) - 1) / N)
      - ζ ^ j) < 1) :
    Ideal.Quotient.mk v.asIdeal (b ^ ((Nat.card (𝓞 K ⧸ v.asIdeal) - 1) / N))
      = Ideal.Quotient.mk v.asIdeal (((c ^ j : ℕ) : 𝓞 K)) := by
  rw [natCard_divisionResidue_adicCompletion_eq_natCard_quotient,
    ← IsScalarTower.algebraMap_apply (𝓞 K) K (HeightOneSpectrum.adicCompletion K v) b] at hj
  exact mk_pow_eq_mk_natCast_pow_of_valued v hζ1 hζres hj

end ResidueCongruence

end InverseGalois.CFT
