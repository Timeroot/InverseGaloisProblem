/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.TotallyRamified

/-!
# A totally real cyclic subfield of a cyclotomic field of prime conductor

The second inequality of class field theory is proved by comparing a cyclic extension with an
auxiliary cyclic extension of the rationals which ramifies at a single prime.  The comparison at
the archimedean places is only available when the auxiliary extension is totally real, so the
degree of the auxiliary extension has to be arranged to divide *half* of the degree of the
cyclotomic field that contains it.

A cyclotomic field of prime conductor `q > 2` is a CM field, so it carries a distinguished complex
conjugation, an automorphism of order two over the maximal real subfield.  Read as an automorphism
over the rationals it is an involution of a cyclic Galois group, and an involution of a finite
cyclic group lies in every subgroup of even index dividing the order.  Consequently an intermediate
field whose degree is half the degree of the cyclotomic field, or a divisor of it, is fixed by
complex conjugation and therefore totally real.

Combining this with the subfield of prescribed degree that is totally ramified at `q` and
unramified elsewhere gives the auxiliary field required: for every degree `n` and every bound `B`
there is a prime `q > B` and a cyclic, totally real extension of the rationals of degree `n` which
is totally ramified at `q` and unramified everywhere else.

## Main results

* `InverseGalois.CFT.Subgroup.mem_of_sq_eq_one_of_isCyclic`: an element of order dividing two in a
  finite cyclic group lies in every subgroup whose index is at most half the order.
* `InverseGalois.CFT.ratComplexConj`: complex conjugation of a CM field as an automorphism over the
  rationals.
* `InverseGalois.CFT.isTotallyReal_of_two_mul_finrank_dvd`: an intermediate field of a CM field with
  cyclic Galois group over the rationals is totally real as soon as twice its degree divides the
  degree of the ambient field.
* `InverseGalois.CFT.exists_cyclic_totallyRamified_totallyReal_of_dvd`: **a totally real cyclic
  extension of the rationals of prescribed degree inside the cyclotomic field of a given prime
  conductor**, totally ramified at that prime and unramified elsewhere, whenever twice the degree
  divides the prime minus one.
* `InverseGalois.CFT.exists_prime_cyclic_totallyRamified_totallyReal`: **a totally real cyclic
  extension of the rationals of prescribed degree, totally ramified at a single large prime and
  unramified elsewhere.**

## Tags

cyclotomic field, CM field, complex conjugation, totally real, cyclic extension, ramification
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### An involution in a cyclic group -/

/-- An element of order dividing two in a finite cyclic group lies in every subgroup whose index
is at most half the order of the group.  Writing the element as a power `g ^ j` of a generator,
the order of the group divides `2 * j`, hence so does twice the index, and therefore the index
divides `j`; the index power of a generator lies in the subgroup. -/
theorem Subgroup.mem_of_sq_eq_one_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {H : Subgroup G} (hdvd : 2 * H.index ∣ Nat.card G) {c : G} (hc : c ^ 2 = 1) : c ∈ H := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨j, rfl⟩ := _root_.Subgroup.mem_zpowers_iff.mp (hg c)
  have h1 : g ^ (2 * j) = 1 := by
    rw [mul_comm, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hc
  have h2 : (Nat.card G : ℤ) ∣ 2 * j := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h1
  have h3 : (2 : ℤ) * (H.index : ℤ) ∣ 2 * j := by
    refine dvd_trans ?_ h2
    exact_mod_cast Int.natCast_dvd_natCast.mpr hdvd
  obtain ⟨s, hs⟩ := (mul_dvd_mul_iff_left (a := (2 : ℤ)) two_ne_zero).mp h3
  haveI : H.Normal := Subgroup.normal_of_isCyclic H
  rw [hs, zpow_mul, zpow_natCast]
  exact H.zpow_mem (_root_.Subgroup.pow_index_mem H g) s

/-! ### Complex conjugation as a rational automorphism -/

section CM

variable (C : Type*) [Field C] [NumberField C] [IsCMField C]

/-- Complex conjugation of a CM field, read as an automorphism over the rationals. -/
noncomputable def ratComplexConj : Gal(C/ℚ) :=
  (IsCMField.complexConj C).restrictScalars ℚ

@[simp]
theorem ratComplexConj_apply (x : C) : ratComplexConj C x = IsCMField.complexConj C x := rfl

/-- Complex conjugation is an involution. -/
theorem ratComplexConj_sq : ratComplexConj C ^ 2 = 1 := by
  ext x
  simp [pow_two]

/-- An element fixed by complex conjugation lies in the maximal real subfield. -/
theorem mem_maximalRealSubfield_of_ratComplexConj_eq {x : C} (h : ratComplexConj C x = x) :
    x ∈ maximalRealSubfield C :=
  (IsCMField.complexConj_eq_self_iff C x).mp h

omit [IsCMField C] in
/-- The index of the group fixing an intermediate field is the degree of that field. -/
theorem index_fixingSubgroup_eq_finrank [IsGalois ℚ C] (F : IntermediateField ℚ C) :
    F.fixingSubgroup.index = finrank ℚ ↥F := by
  have hpos : 0 < finrank ↥F C := finrank_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [← IsGalois.card_fixingSubgroup_eq_finrank F, _root_.Subgroup.index_mul_card,
    IsGalois.card_aut_eq_finrank ℚ C, ← finrank_mul_finrank ℚ ↥F C,
    IsGalois.card_fixingSubgroup_eq_finrank F]

/-- **An intermediate field of a CM field with cyclic Galois group over the rationals is totally
real as soon as twice its degree divides the degree of the ambient field.**  Complex conjugation is
then an involution of the cyclic Galois group lying in the subgroup that fixes the intermediate
field, so every element of that field is fixed by complex conjugation and hence real. -/
theorem isTotallyReal_of_two_mul_finrank_dvd [IsGalois ℚ C] [IsCyclic Gal(C/ℚ)]
    (F : IntermediateField ℚ C) (hdvd : 2 * finrank ℚ ↥F ∣ finrank ℚ C) : IsTotallyReal ↥F := by
  have hcard : 2 * F.fixingSubgroup.index ∣ Nat.card Gal(C/ℚ) := by
    rw [index_fixingSubgroup_eq_finrank C F, IsGalois.card_aut_eq_finrank ℚ C]
    exact hdvd
  have hmem : ratComplexConj C ∈ F.fixingSubgroup :=
    Subgroup.mem_of_sq_eq_one_of_isCyclic hcard (ratComplexConj_sq C)
  have hle : F.toSubfield ≤ maximalRealSubfield C := fun x hx =>
    mem_maximalRealSubfield_of_ratComplexConj_eq C
      ((IntermediateField.mem_fixingSubgroup_iff F _).mp hmem x hx)
  exact isTotallyReal_iff_le_maximalRealSubfield.mpr hle

end CM

/-! ### The cyclotomic case -/

section Cyclotomic

variable (q : ℕ) [hq : Fact q.Prime]

include hq in
/-- An intermediate field of a cyclotomic field of prime conductor `q > 2` is totally real as soon
as twice its degree divides the degree of the cyclotomic field. -/
theorem isTotallyReal_of_two_mul_finrank_dvd_cyclotomic (C : Type*) [Field C] [NumberField C]
    [IsCyclotomicExtension {q} ℚ C] (hq2 : 2 < q) (F : IntermediateField ℚ C)
    (hdvd : 2 * finrank ℚ ↥F ∣ finrank ℚ C) : IsTotallyReal ↥F := by
  haveI : IsCMField C := IsCyclotomicExtension.Rat.isCMField C (S := {q}) ⟨q, rfl, hq2⟩
  haveI : IsGalois ℚ C := IsCyclotomicExtension.isGalois {q} ℚ C
  haveI : IsCyclic Gal(C/ℚ) := isCyclic_gal_cyclotomic_of_prime q C
  exact isTotallyReal_of_two_mul_finrank_dvd C F hdvd

end Cyclotomic

/-! ### The assembled auxiliary field -/

/-- **A totally real cyclic extension of the rationals of prescribed degree inside the cyclotomic
field of a given prime conductor**, totally ramified at that prime and unramified elsewhere.  The
subfield of the prescribed degree is cyclic, totally ramified at the conductor and unramified
elsewhere, and it is totally real because twice its degree divides the degree of the cyclotomic
field. -/
theorem exists_cyclic_totallyRamified_totallyReal_of_dvd {n q : ℕ} (hn : n ≠ 0) (hqp : q.Prime)
    (hdvd : 2 * n ∣ q - 1) :
    n < q ∧
      ∃ (F : IntermediateField ℚ (CyclotomicField q ℚ)) (_ : NumberField ↥F),
        IsGalois ℚ ↥F ∧ IsCyclic Gal(↥F/ℚ) ∧ IsTotallyReal ↥F ∧ finrank ℚ ↥F = n ∧
        ramifiedSet ↥F ⊆ {q} ∧
        ∀ (Q : Ideal (𝓞 ↥F)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q : ℤ)})),
          Ideal.inertia Gal(↥F/ℚ) Q = ⊤ := by
  haveI : Fact q.Prime := ⟨hqp⟩
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have h2 : 2 ≤ q := hqp.two_le
  have hle : 2 * n ≤ q - 1 := Nat.le_of_dvd (by omega) hdvd
  have hnq : n < q := by omega
  have hq2 : 2 < q := by omega
  haveI : IsCyclotomicExtension {q ^ 1} ℚ (CyclotomicField q ℚ) := by rw [pow_one]; infer_instance
  have hrank : finrank ℚ (CyclotomicField q ℚ) = q - 1 := finrank_cyclotomic_of_prime q _
  obtain ⟨F, hNF, hgal, hcyc, hFrank, hram, hinert⟩ :=
    exists_cyclic_totallyRamified q 1 (Or.inr (by norm_num)) (CyclotomicField q ℚ)
      (ℓ := n) (by rw [pow_one, Nat.totient_prime hqp]; exact dvd_trans ⟨2, mul_comm 2 n⟩ hdvd)
  refine ⟨hnq, F, hNF, hgal, hcyc, ?_, hFrank, hram, hinert⟩
  exact isTotallyReal_of_two_mul_finrank_dvd_cyclotomic q (CyclotomicField q ℚ) hq2 F
    (by rw [hFrank, hrank]; exact hdvd)

/-- **A totally real cyclic extension of the rationals of prescribed degree, totally ramified at a
single large prime and unramified elsewhere.**  Dirichlet's theorem supplies a prime `q` congruent
to one modulo twice the degree; the subfield of the cyclotomic field of conductor `q` of that
degree is cyclic, totally ramified at `q` and unramified elsewhere, and it is totally real because
twice its degree divides `q - 1`. -/
theorem exists_prime_cyclic_totallyRamified_totallyReal {n : ℕ} (hn : n ≠ 0) (B : ℕ) :
    ∃ q : ℕ, B < q ∧ n < q ∧ q.Prime ∧
      ∃ (F : IntermediateField ℚ (CyclotomicField q ℚ)) (_ : NumberField ↥F),
        IsGalois ℚ ↥F ∧ IsCyclic Gal(↥F/ℚ) ∧ IsTotallyReal ↥F ∧ finrank ℚ ↥F = n ∧
        ramifiedSet ↥F ⊆ {q} ∧
        ∀ (Q : Ideal (𝓞 ↥F)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q : ℤ)})),
          Ideal.inertia Gal(↥F/ℚ) Q = ⊤ := by
  obtain ⟨q, hqB, hqp, -, hdvd⟩ := Nat.exists_prime_gt_and_pow_dvd_sub_one (m := 2 * n)
    (Nat.mul_ne_zero two_ne_zero hn) (max B n)
  obtain ⟨hnq, hF⟩ := exists_cyclic_totallyRamified_totallyReal_of_dvd hn hqp hdvd
  exact ⟨q, lt_of_le_of_lt (le_max_left B n) hqB, hnq, hqp, hF⟩

end InverseGalois.CFT
