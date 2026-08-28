/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicHerbrand
import InverseGalois.CFT.Local.TrivialIndex
import InverseGalois.CFT.Local.UnitIndex

/-!
# The index of the `n`-th powers in the units of a completion at a finite place

The general index formula for a complete discretely valued field says that the `n`-th powers have
index `n`, times the order of the residue field raised to the valuation of `n`, times the number of
`n`-th roots of unity.  At a finite place of a number field all three inputs are available: the
valuation is surjective, the residue characteristic exists, and the graded pieces are finite.

Reducing modulo the place identifies the residue field of the completion with the residue field of
the ring of integers, so the order of the residue field is the absolute norm of the place.  That
turns the middle factor into the reciprocal of the normalised absolute value of `n` at the place,
and the index formula becomes the statement that the index times the normalised absolute value of
`n` is `n` times the number of `n`-th roots of unity.

## Main definitions

* `InverseGalois.CFT.adicResidueEmbedding`: the residue field of the ring of integers at a place,
  mapped into the residue field of the completion there.

## Main results

* `InverseGalois.CFT.card_gradedAdd_adicCompletion_zero`: **the residue field of the completion has
  order the absolute norm of the place.**
* `InverseGalois.CFT.finitePlace_eq_zpow`: the normalised absolute value at a finite place, read off
  from the valuation.
* `InverseGalois.CFT.index_range_powMonoidHom_units_adicCompletion`: **the local index formula at a
  finite place**, the index of the `n`-th powers times the normalised absolute value of `n` being
  `n` times the number of `n`-th roots of unity.

## Tags

number field, finite place, local index, residue field, absolute norm, roots of unity
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped NNReal WithZero

/-! ### The value of the exponential under the real-valued comparison -/

/-- The real-valued comparison of the value group sends an exponential to a power. -/
theorem toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (a : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp a) = e ^ a := by
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero]
  congr 1

/-! ### The residue field of a completion -/

section AdicResidue

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- **The residue field of the ring of integers at a place, mapped into the residue field of the
completion there.** -/
noncomputable def adicResidueEmbedding (x : 𝓞 K ⧸ v.asIdeal) :
    gradedAdd (v.adicCompletion K) 0 :=
  Quotient.liftOn' x
    (fun b => (QuotientAddGroup.mk (adicResidueRep K v b) : gradedAdd (v.adicCompletion K) 0))
    fun _ _ h => adicResidueRep_eq_of_sub_mem K v (by simpa [Submodule.quotientRel_def] using h)

@[simp]
theorem adicResidueEmbedding_mk (b : 𝓞 K) :
    adicResidueEmbedding v (Ideal.Quotient.mk v.asIdeal b)
      = QuotientAddGroup.mk (adicResidueRep K v b) :=
  rfl

/-- Every class in the residue field of the completion comes from the ring of integers. -/
theorem adicResidueEmbedding_surjective : Function.Surjective (adicResidueEmbedding v) := by
  intro g
  induction g using QuotientAddGroup.induction_on with
  | H w =>
    obtain ⟨b, hb⟩ := exists_algebraMap_sub_le_exp_neg_one K v
      (by simpa using mem_valAddSubgroup.mp w.2)
    refine ⟨Ideal.Quotient.mk v.asIdeal b, ?_⟩
    rw [adicResidueEmbedding_mk]
    refine gradedAdd_mk_eq ?_
    have hrep : (adicResidueRep K v b : v.adicCompletion K)
        = algebraMap (𝓞 K) (v.adicCompletion K) b := rfl
    have hswap : Valued.v ((adicResidueRep K v b : v.adicCompletion K) - (w : v.adicCompletion K))
        = Valued.v ((w : v.adicCompletion K) - (adicResidueRep K v b : v.adicCompletion K)) :=
      Valuation.map_sub_swap _ _ _
    rw [hswap, hrep]
    simpa using hb

/-- Two elements of the ring of integers with the same class in the residue field of the completion
are congruent modulo the place. -/
theorem adicResidueEmbedding_injective : Function.Injective (adicResidueEmbedding v) := by
  refine Quotient.ind₂' fun b c h => ?_
  have h' : (QuotientAddGroup.mk (adicResidueRep K v b) : gradedAdd (v.adicCompletion K) 0)
      = QuotientAddGroup.mk (adicResidueRep K v c) := h
  rw [gradedAdd_mk_eq_iff] at h'
  have hsub : ((adicResidueRep K v b : v.adicCompletion K)
      - (adicResidueRep K v c : v.adicCompletion K))
      = ((algebraMap (𝓞 K) K (b - c) : K) : v.adicCompletion K) := by
    have hb : (adicResidueRep K v b : v.adicCompletion K)
        = ((algebraMap (𝓞 K) K b : K) : v.adicCompletion K) := rfl
    have hc : (adicResidueRep K v c : v.adicCompletion K)
        = ((algebraMap (𝓞 K) K c : K) : v.adicCompletion K) := rfl
    rw [hb, hc, map_sub]
    push_cast
    ring
  rw [hsub, HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v),
    HeightOneSpectrum.valuation_of_algebraMap] at h'
  refine Quotient.sound' ?_
  rw [Submodule.quotientRel_def]
  refine (v.intValuation_lt_one_iff_mem (b - c)).mp (lt_of_le_of_lt h' ?_)
  simpa using WithZero.exp_lt_exp.mpr (by omega : (-(0 + 1) : ℤ) < 0)

/-- **The residue field of the completion has order the absolute norm of the place.** -/
theorem card_gradedAdd_adicCompletion_zero :
    Nat.card (gradedAdd (v.adicCompletion K) 0) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Equiv.ofBijective _
    ⟨adicResidueEmbedding_injective v, adicResidueEmbedding_surjective v⟩)).symm

end AdicResidue

/-! ### The normalised absolute value at a finite place -/

section FinitePlaceValue

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The normalised absolute value at a finite place, read off from the valuation. -/
theorem finitePlace_eq_zpow {m : ℤ} {x : K} (hx : v.valuation K x = WithZero.exp m) :
    FinitePlace.mk v x = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_def,
    RingOfIntegers.HeightOneSpectrum.adicAbv_def, hx, toNNReal_exp]
  push_cast
  rfl

end FinitePlaceValue

/-! ### The local index formula -/

section AdicIndex

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- **The local index formula at a finite place.**  The index of the `n`-th powers in the units of
the completion, times the normalised absolute value of `n` at the place, is `n` times the number of
`n`-th roots of unity of the completion. -/
theorem index_range_powMonoidHom_units_adicCompletion {n : ℕ} (hn : n ≠ 0) :
    ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index : ℝ)
        * FinitePlace.mk v ((n : ℕ) : K)
      = n * Nat.card ↥(rootsOfUnity n (v.adicCompletion K)) := by
  obtain ⟨p, e, hres⟩ := exists_hasResidueChar_adicCompletion v
  have hval : Valued.v ((n : ℕ) : v.adicCompletion K)
      = WithZero.exp (-((e * padicValNat p n : ℕ) : ℤ)) := by
    rw [hres.valued_natCast hn]
    push_cast
    ring_nf
  have hcast : ((n : ℕ) : v.adicCompletion K) = (((n : ℕ) : K) : v.adicCompletion K) :=
    (map_natCast (UniformSpace.Completion.coeRingHom :
      WithVal (v.valuation K) →+* v.adicCompletion K) n).symm
  have hvalK : v.valuation K ((n : ℕ) : K) = WithZero.exp (-((e * padicValNat p n : ℕ) : ℤ)) := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v), ← hcast, hval]
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    have h1 := RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast lt_of_lt_of_le Nat.one_pos h1.le
  have hqne : ((Ideal.absNorm v.asIdeal : ℝ)) ^ (e * padicValNat p n) ≠ 0 := (pow_pos hq _).ne'
  rw [index_range_powMonoidHom_units (valued_adicCompletion_surjective v) hres hn hval,
    finitePlace_eq_zpow v hvalK, card_gradedAdd_adicCompletion_zero, zpow_neg, zpow_natCast]
  push_cast
  field_simp

end AdicIndex

end InverseGalois.CFT
