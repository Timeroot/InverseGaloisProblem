/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicResidue
import InverseGalois.CFT.Local.AdicUnits
import InverseGalois.CFT.Local.GradedFinite
import InverseGalois.CFT.Local.UnramifiedUnits

/-!
# The Herbrand quotient of the units of a completion of a number field

The completion of a number field at a finite place is a complete discretely valued field with a
finite residue field, and the decomposition group at that place acts on it faithfully by
isometries.  So the general computation of the Herbrand quotient of the units of a complete
discretely valued field applies: the units of the valuation ring have Herbrand quotient one and the
units of the field have Herbrand quotient the order of the decomposition group.

The hypotheses of the general computation are discharged here.  The residue characteristic is the
characteristic of the residue field, which is a prime lying in the place and therefore has
valuation less than one; the graded pieces of the additive filtration are all finite because the
residue field is; and an automorphism acting trivially on the completion already acts trivially on
the dense subfield.

## Main results

* `InverseGalois.CFT.exists_hasResidueChar`: a prime of valuation less than one is a residue
  characteristic.
* `InverseGalois.CFT.exists_hasResidueChar_adicCompletion`: **the completion of a number field at a
  finite place has a residue characteristic.**
* `InverseGalois.CFT.herbrand_adicUnits_eq_one`: **the units of the valuation ring of the
  completion have Herbrand quotient one.**
* `InverseGalois.CFT.herbrand_adicUnits_eq_card`: **the units of the completion have Herbrand
  quotient the order of the decomposition group.**
* `InverseGalois.CFT.subsingleton_tate_adicUnits`: **both Tate groups of the units of the valuation
  ring vanish** when the decomposition group fixes a uniformizer.

## Tags

number field, adic completion, decomposition group, Herbrand quotient, local units
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped WithZero

/-! ### Recognising the residue characteristic -/

section ResidueChar

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] {p : ℕ}

/-- **A prime of valuation less than one is a residue characteristic.**  Its valuation is a
negative power of the value of a uniformizer, and that exponent is the one wanted. -/
theorem exists_hasResidueChar (hp : p.Prime) (hne : Valued.v (p : A) ≠ 0)
    (hlt : Valued.v (p : A) < 1) : ∃ e : ℕ, HasResidueChar A p e := by
  have hexp : WithZero.exp (WithZero.log (Valued.v (p : A))) = Valued.v (p : A) :=
    WithZero.exp_log hne
  have hneg : WithZero.log (Valued.v (p : A)) < 0 := by
    rw [← WithZero.exp_lt_exp, hexp, WithZero.exp_zero]
    exact hlt
  refine ⟨(-WithZero.log (Valued.v (p : A))).toNat, hp, by omega, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, hexp]

end ResidueChar

/-! ### The residue characteristic of a completion -/

section Adic

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- **The completion of a number field at a finite place has a residue characteristic.**  The
characteristic of the residue field is a prime lying in the place, so its valuation is less than
one. -/
theorem exists_hasResidueChar_adicCompletion :
    ∃ p e : ℕ, HasResidueChar (v.adicCompletion K) p e := by
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI : IsDomain (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.isDomain _
  set p : ℕ := ringChar (𝓞 K ⧸ v.asIdeal) with hpdef
  haveI hchar : CharP (𝓞 K ⧸ v.asIdeal) p := ringChar.charP _
  have hp0 : p ≠ 0 := by
    intro h
    haveI : CharP (𝓞 K ⧸ v.asIdeal) 0 := h ▸ hchar
    haveI := CharP.charP_to_charZero (𝓞 K ⧸ v.asIdeal)
    exact not_finite (𝓞 K ⧸ v.asIdeal)
  have hp : p.Prime := CharP.char_prime_of_ne_zero (R := 𝓞 K ⧸ v.asIdeal) hp0
  have hmem : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  have hne0 : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hcast : ((p : ℕ) : v.adicCompletion K)
      = algebraMap (𝓞 K) (v.adicCompletion K) ((p : ℕ) : 𝓞 K) := by
    rw [map_natCast]
  have hval : Valued.v ((p : ℕ) : v.adicCompletion K) = v.intValuation ((p : ℕ) : 𝓞 K) := by
    rw [hcast, HeightOneSpectrum.valuedAdicCompletion_eq_valuation,
      HeightOneSpectrum.valuation_of_algebraMap]
  refine ⟨p, exists_hasResidueChar hp ?_ ?_⟩
  · rw [hval]
    exact v.intValuation_ne_zero _ hne0
  · rw [hval]
    exact (v.intValuation_lt_one_iff_mem _).mpr hmem

/-- Every graded piece of the additive filtration of the completion is finite. -/
instance instFiniteGradedAddAdicCompletion (j : ℤ) : Finite (gradedAdd (v.adicCompletion K) j) :=
  finite_gradedAdd_forall (exists_uniformizer_adicCompletion K v) j

/-! ### Faithfulness of the decomposition group -/

variable {k : Type*} [Field k] [Algebra k K]

/-- **The decomposition group acts faithfully on the completion**, because it acts faithfully on
the dense subfield. -/
instance instFaithfulSMulStabilizerAdicCompletion :
    FaithfulSMul ↥(stabilizer Gal(K/k) v) (v.adicCompletion K) where
  eq_of_smul_eq_smul {σ τ} h := by
    have hcoe : ∀ (ρ : ↥(stabilizer Gal(K/k) v)) (y : K),
        ρ • ((y : v.adicCompletion K)) = ((ρ.1 y : K) : v.adicCompletion K) := fun ρ y =>
      adicCompletionAut_coe v ρ.1 (mem_stabilizer_iff.mp ρ.2) y
    have hK : ∀ x : K, σ.1 x = τ.1 x := by
      intro x
      have hx := h ((x : v.adicCompletion K))
      rw [hcoe, hcoe] at hx
      exact UniformSpace.Completion.coe_injective (WithVal (v.valuation K)) hx
    exact Subtype.ext (AlgEquiv.ext hK)

/-! ### The Herbrand quotient -/

variable [Fintype ↥(stabilizer Gal(K/k) v)] {σ : ↥(stabilizer Gal(K/k) v)}
  (hgen : ∀ g : ↥(stabilizer Gal(K/k) v), g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d]
  (hσ : σ ^ d = 1) (hcard : Nat.card ↥(stabilizer Gal(K/k) v) = d)

include hgen hσ hcard

/-- Both Tate groups of the units of the valuation ring of the completion are finite. -/
theorem finite_tate_adicUnits :
    Finite (tateH0 (kerUnitValAut (valued_smul_adicCompletion v) σ) d)
      ∧ Finite (tateHm1 (kerUnitValAut (valued_smul_adicCompletion v) σ) d) :=
  have ⟨_, _, h⟩ := exists_hasResidueChar_adicCompletion v
  finite_tate_kerUnitValAut (valued_smul_adicCompletion v) h hgen hσ hcard

/-- **The units of the valuation ring of the completion have Herbrand quotient one.** -/
theorem herbrand_adicUnits_eq_one :
    herbrand (kerUnitValAut (valued_smul_adicCompletion v) σ) d = 1 :=
  have ⟨_, _, h⟩ := exists_hasResidueChar_adicCompletion v
  herbrand_kerUnitValAut_eq_one (valued_smul_adicCompletion v) h hgen hσ hcard

/-- Both Tate groups of the units of the completion are finite. -/
theorem finite_tate_adicUnitsField :
    Finite (tateH0 (smulUnitsAut (R := v.adicCompletion K) σ) d)
      ∧ Finite (tateHm1 (smulUnitsAut (R := v.adicCompletion K) σ) d) :=
  have ⟨_, _, h⟩ := exists_hasResidueChar_adicCompletion v
  finite_tate_smulUnitsAut (valued_smul_adicCompletion v)
    (isUnitValGen_one (valued_adicCompletion_surjective v)) h hgen hσ hcard

/-- **The units of the completion have Herbrand quotient the order of the decomposition group.** -/
theorem herbrand_adicUnits_eq_card :
    herbrand (smulUnitsAut (R := v.adicCompletion K) σ) d = d :=
  have ⟨_, _, h⟩ := exists_hasResidueChar_adicCompletion v
  herbrand_smulUnitsAut_eq_card (valued_smul_adicCompletion v)
    (isUnitValGen_one (valued_adicCompletion_surjective v)) h hgen hσ hcard

/-! ### The unramified case -/

/-- **Both Tate groups of the units of the valuation ring of the completion vanish** when the
decomposition group fixes a uniformizer, that is, when the place is unramified over the subfield
fixed by the decomposition group. -/
theorem subsingleton_tate_adicUnits (π : (v.adicCompletion K)ˣ)
    (hπfix : ∀ g : ↥(stabilizer Gal(K/k) v), g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
    (hπval : unitVal (Additive.ofMul π) = 1) :
    Subsingleton (tateH0 (kerUnitValAut (valued_smul_adicCompletion v) σ) d)
      ∧ Subsingleton (tateHm1 (kerUnitValAut (valued_smul_adicCompletion v) σ) d) :=
  have ⟨_, _, h⟩ := exists_hasResidueChar_adicCompletion v
  ⟨subsingleton_tateH0_kerUnitValAut (valued_smul_adicCompletion v) h hgen hσ hcard π hπfix hπval,
    subsingleton_tateHm1_kerUnitValAut (valued_smul_adicCompletion v) hgen hcard π hπfix hπval⟩

end Adic

end InverseGalois.CFT
