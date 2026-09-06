/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.AuxiliarySubfield

/-!
# A totally complex subfield of a cyclotomic field of prime conductor

The archimedean correction of a Brauer class is made by a cyclic algebra whose invariant at a real
place is the sign of its coefficient there, and that asks the splitting field to be *totally
complex* rather than totally real: a real place of the base must stay ramified in it.  The subfield
of prescribed degree of the cyclotomic field of prime conductor is again the field that provides
one, only now the degree has to be arranged so that complex conjugation does *not* fix it.

Complex conjugation of a CM field is an automorphism of order two, and a subfield it moves is
totally complex: an embedding of that subfield into the complex numbers extends to the whole field,
where it intertwines complex conjugation of the field with conjugation of the complex numbers, so a
real embedding of the subfield would force complex conjugation to fix it pointwise.  Complex
conjugation lies in the group fixing a subfield only if the order of that group, which is the
degree of the ambient field over the subfield, is even; so a subfield of odd codegree is moved, and
therefore totally complex.

Inside the cyclotomic field of prime conductor `q` this reads as an arithmetic condition on the
degree: the subfield of degree `d` has codegree `(q - 1) / d`, so it is totally complex exactly when
that quotient is odd.  For `d = 2` this is the familiar statement that the quadratic subfield of
`ℚ(ζ_q)` is imaginary precisely when `q` is congruent to `3` modulo `4`.

## Main results

* `InverseGalois.CFT.isTotallyComplex_of_exists_complexConj_ne`: an intermediate field of a CM
  field that complex conjugation does not fix pointwise is totally complex.
* `InverseGalois.CFT.isTotallyComplex_of_odd_finrank`: **an intermediate field of a CM field over
  which the ambient field has odd degree is totally complex.**
* `InverseGalois.CFT.exists_intermediateField_subcyclotomic_imaginary`: **a totally complex subfield
  of prescribed degree of the cyclotomic field of a prime conductor**, totally ramified at that
  conductor, in which a rational prime splits completely exactly when it is a power residue and
  whose decomposition group at a prime above a rational prime is read off from a power residue
  condition of matching exponent.

## Tags

cyclotomic field, CM field, complex conjugation, totally complex, imaginary quadratic field,
totally ramified, power residue
-/

set_option synthInstance.maxHeartbeats 1000000

open Module NumberField InverseGalois.NumberTheory

open scoped ComplexConjugate Pointwise

namespace InverseGalois.CFT

/-! ### Total complexity from complex conjugation -/

section CM

variable (C : Type*) [Field C] [NumberField C] [IsCMField C]

/-- Complex conjugation of a CM field is not the identity, read as an automorphism over the
rationals. -/
theorem ratComplexConj_ne_one : ratComplexConj C ≠ 1 := by
  intro h
  refine IsCMField.complexConj_ne_one C (AlgEquiv.ext fun x => ?_)
  simpa using congrArg (fun σ : Gal(C/ℚ) => σ x) h

/-- **An intermediate field of a CM field that complex conjugation does not fix pointwise is
totally complex.**  An embedding of the intermediate field into the complex numbers extends to an
embedding of the whole field, which carries complex conjugation of the field to conjugation of the
complex numbers; were the embedding real, every element of the intermediate field would then have
the same image as its conjugate, and hence be fixed. -/
theorem isTotallyComplex_of_exists_complexConj_ne (F : IntermediateField ℚ C)
    (h : ∃ x : ↥F, IsCMField.complexConj C (x : C) ≠ (x : C)) : IsTotallyComplex ↥F := by
  obtain ⟨x, hx⟩ := h
  refine ⟨fun v => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hv
  haveI : Algebra.IsAlgebraic ↥F C := Algebra.IsAlgebraic.of_finite ↥F C
  have hreal : conj (v.embedding x) = v.embedding x :=
    RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hv)) x
  have hlift : ComplexEmbedding.lift C v.embedding (x : C) = v.embedding x :=
    ComplexEmbedding.lift_algebraMap_apply C v.embedding x
  refine hx ((ComplexEmbedding.lift C v.embedding).injective ?_)
  rw [IsCMField.complexEmbedding_complexConj C _ (x : C), hlift, hreal]

/-- **An intermediate field of a CM field over which the ambient field has odd degree is totally
complex.**  The group fixing the intermediate field has odd order, so it cannot contain complex
conjugation, an element of order two; some element of the intermediate field is therefore moved by
complex conjugation. -/
theorem isTotallyComplex_of_odd_finrank [IsGalois ℚ C] (F : IntermediateField ℚ C)
    (hodd : Odd (finrank ↥F C)) : IsTotallyComplex ↥F := by
  refine isTotallyComplex_of_exists_complexConj_ne C F ?_
  by_contra hcon
  push_neg at hcon
  have hmem : ratComplexConj C ∈ F.fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff F _).mpr fun y hy => hcon ⟨y, hy⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (⟨ratComplexConj C, hmem⟩ : ↥F.fixingSubgroup) = 2 := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun hc => ?_
    · push_cast
      exact ratComplexConj_sq C
    · exact ratComplexConj_ne_one C (by simpa using Subtype.ext_iff.mp hc)
  have hdvd : 2 ∣ Nat.card ↥F.fixingSubgroup := hord ▸ orderOf_dvd_natCard _
  rw [IsGalois.card_fixingSubgroup_eq_finrank F] at hdvd
  rw [Nat.odd_iff] at hodd
  omega

end CM

/-! ### The cyclotomic case -/

section Cyclotomic

/-- An intermediate field of a cyclotomic field of conductor `q > 2` is totally complex as soon as
the cyclotomic field has odd degree over it. -/
theorem isTotallyComplex_of_odd_finrank_cyclotomic (q : ℕ) (C : Type*) [Field C] [NumberField C]
    [IsCyclotomicExtension {q} ℚ C] (hq2 : 2 < q) (F : IntermediateField ℚ C)
    (hodd : Odd (finrank ↥F C)) : IsTotallyComplex ↥F := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : IsCMField C := IsCyclotomicExtension.Rat.isCMField C (S := {q}) ⟨q, rfl, hq2⟩
  haveI : IsGalois ℚ C := IsCyclotomicExtension.isGalois {q} ℚ C
  exact isTotallyComplex_of_odd_finrank C F hodd

end Cyclotomic

/-! ### The subfield -/

section Subfield

variable (q : ℕ) [hq : Fact q.Prime]

/-- **A totally complex subfield of prescribed degree of the cyclotomic field of a prime
conductor**, totally ramified at that conductor and unramified elsewhere, in which a rational prime
other than the conductor splits completely exactly when it is a power residue of the matching
exponent, and whose decomposition group at a prime above such a rational prime has order dividing a
number exactly when the correspondingly larger power residue condition holds.  The complementary
degree is asked to be odd, which is what keeps complex conjugation off the subfield. -/
theorem exists_intermediateField_subcyclotomic_imaginary (hq2 : 2 < q) {d : ℕ} (hd : d ≠ 0)
    (hdvd : d ∣ q - 1) (hodd : Odd ((q - 1) / d))
    (E : Type) [Field E] [NumberField E] [IsCyclotomicExtension {q} ℚ E] :
    ∃ F : IntermediateField ℚ E, finrank ℚ ↥F = d ∧ IsGalois ℚ ↥F ∧ IsCyclic Gal(↥F/ℚ) ∧
      IsTotallyComplex ↥F ∧
      (∀ p : ℕ, p.Prime → p ≠ q → (SplitsCompletely ↥F p ↔ (p : ZMod q) ^ ((q - 1) / d) = 1)) ∧
      (∀ (p : ℕ), p.Prime → p ≠ q → ∀ (P : Ideal (𝓞 ↥F)) (_ : P.IsPrime)
        (_ : P.LiesOver (Ideal.span {(p : ℤ)})) (m : ℕ),
          (Nat.card ↥(MulAction.stabilizer Gal(↥F/ℚ) P) ∣ m ↔
            (p : ZMod q) ^ (m * ((q - 1) / d)) = 1)) ∧
      ∀ (Q : Ideal (𝓞 ↥F)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q : ℤ)})),
        Ideal.inertia Gal(↥F/ℚ) Q = ⊤ := by
  haveI : IsCyclotomicExtension {q ^ 1} ℚ E := by rw [pow_one]; infer_instance
  haveI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {q} ℚ E
  obtain ⟨F, hrank, hgal, hcyc, hsplit, hdeg, -⟩ :=
    exists_intermediateField_finrank_eq_and_splitsCompletely q hd hdvd E
  haveI := hgal
  refine ⟨F, hrank, hgal, hcyc, ?_, hsplit, hdeg, ?_⟩
  · refine isTotallyComplex_of_odd_finrank_cyclotomic q E hq2 F ?_
    have hmul : finrank ℚ ↥F * finrank ↥F E = finrank ℚ E := finrank_mul_finrank ℚ ↥F E
    rw [hrank, finrank_cyclotomic_of_prime q E] at hmul
    rwa [show finrank ↥F E = (q - 1) / d by
      rw [← hmul, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd)]]
  · intro Q hQp hQo
    haveI := hQp
    haveI := hQo
    have hQ0 : Q ≠ ⊥ := ne_bot_of_liesOver_natCast hq.out inferInstance
    haveI : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ0 inferInstance
    obtain ⟨P, hPmax, hPover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) Q
    haveI := hPmax
    haveI := hPover
    haveI : P.IsPrime := hPmax.isPrime
    haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := Ideal.LiesOver.trans P Q (Ideal.span {(q : ℤ)})
    have hunder : P.under (𝓞 ↥F) = Q := (Ideal.LiesOver.over (p := Q)).symm
    rw [← hunder]
    exact inertia_eq_top_of_inertia_eq_top F hq.out P (inertia_eq_top_cyclotomic_primePow q 1 E P)

end Subfield

end InverseGalois.CFT
