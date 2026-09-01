/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.DivisorSubfield
import InverseGalois.CFT.Cyclotomic.TotallyRealSubfield

/-!
# The auxiliary subfield of a cyclotomic field of prime conductor

The reciprocity law for a cyclic algebra split by a subfield of a cyclotomic field asks a great
deal of that subfield at once: it must be totally real, so that the archimedean invariants vanish;
it must be totally ramified at the conductor, so that the invariant there is a power residue
symbol; and its splitting law must be readable as a power residue condition, so that an auxiliary
prime can be chosen to make a prescribed rational prime miss it.

All three come from the same subfield, the one of prescribed degree inside the cyclotomic field of
prime conductor.  Its splitting law is a power residue condition because the Frobenius of the
cyclotomic field is the automorphism naming the prime; it ramifies only at the conductor and is
totally ramified there because restriction maps inertia onto inertia; and it is totally real
because the cyclotomic field is a CM field whose complex conjugation lies in every subgroup of even
index, so a degree dividing half the degree of the cyclotomic field suffices.

The other datum the reciprocity law consumes is a generator of the Galois group, named by a
primitive root modulo the conductor.  The units modulo a prime are cyclic, and the residue of a
generator is such a primitive root.

## Main results

* `InverseGalois.CFT.exists_nat_primitiveRoot_of_prime`: **a natural number whose powers exhaust
  the nonzero residues modulo a prime**, in the form of a coprime number whose order is the whole
  group of units.
* `InverseGalois.CFT.exists_intermediateField_subcyclotomic`: **a totally real subfield of
  prescribed degree of the cyclotomic field of a prime conductor**, totally ramified at that
  conductor, in which a rational prime splits completely exactly when it is a power residue.

## Tags

cyclotomic field, primitive root, totally real, totally ramified, power residue, auxiliary prime
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### A primitive root modulo a prime -/

section PrimitiveRoot

/-- **A natural number whose powers exhaust the nonzero residues modulo a prime.**  The units
modulo a prime form a cyclic group; the residue of a generator is such a number, and the order of
that generator is the number of units, so a power of the number is one exactly when the exponent is
a multiple of the prime minus one. -/
theorem exists_nat_primitiveRoot_of_prime {q : ℕ} (hq : q.Prime) :
    ∃ g : ℕ, Nat.Coprime g q ∧ ∀ k : ℕ, q ∣ g ^ k - 1 → (q - 1) ∣ k := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  refine ⟨(u : ZMod q).val, ?_, ?_⟩
  · have hne : (((u : ZMod q).val : ℕ) : ZMod q) ≠ 0 := by
      rw [ZMod.natCast_val, ZMod.cast_id]
      exact u.ne_zero
    refine Nat.Coprime.symm (hq.coprime_iff_not_dvd.mpr fun hdvd => hne ?_)
    exact (ZMod.natCast_eq_zero_iff _ q).mpr hdvd
  · intro k hk
    have hcast : (((u : ZMod q).val : ℕ) : ZMod q) = (u : ZMod q) := by
      rw [ZMod.natCast_val, ZMod.cast_id]
    have hval0 : (u : ZMod q).val ≠ 0 := by
      intro h
      rw [h] at hcast
      exact u.ne_zero (by simpa using hcast.symm)
    have hpos : 1 ≤ (u : ZMod q).val ^ k :=
      Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hval0)
    have hone : ((u : ZMod q).val : ZMod q) ^ k = 1 := by
      have := (ZMod.natCast_eq_zero_iff _ q).mpr hk
      rw [Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at this
      exact this
    have huk : u ^ k = 1 := by
      rw [← Units.val_eq_one, Units.val_pow_eq_pow_val, ← hcast, hone]
    have hord : orderOf u = q - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card,
        ZMod.card_units_eq_totient, Nat.totient_prime hq]
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one huk

end PrimitiveRoot

/-! ### The subfield -/

section Subfield

variable (q : ℕ) [hq : Fact q.Prime]

/-- **A totally real subfield of prescribed degree of the cyclotomic field of a prime conductor**,
totally ramified at that conductor and unramified elsewhere, in which a rational prime other than
the conductor splits completely exactly when it is a power residue of the matching exponent.  The
degree is asked to divide half of the degree of the cyclotomic field, which is what buys total
reality. -/
theorem exists_intermediateField_subcyclotomic {d : ℕ} (hd : d ≠ 0) (hdvd : 2 * d ∣ q - 1)
    (E : Type) [Field E] [NumberField E] [IsCyclotomicExtension {q} ℚ E] :
    ∃ F : IntermediateField ℚ E, finrank ℚ ↥F = d ∧ IsGalois ℚ ↥F ∧ IsCyclic Gal(↥F/ℚ) ∧
      IsTotallyReal ↥F ∧
      (∀ p : ℕ, p.Prime → p ≠ q → (SplitsCompletely ↥F p ↔ (p : ZMod q) ^ ((q - 1) / d) = 1)) ∧
      ∀ (Q : Ideal (𝓞 ↥F)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q : ℤ)})),
        Ideal.inertia Gal(↥F/ℚ) Q = ⊤ := by
  haveI : IsCyclotomicExtension {q ^ 1} ℚ E := by rw [pow_one]; infer_instance
  haveI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {q} ℚ E
  have hq2 : 2 ≤ q := hq.out.two_le
  have hle : 2 * d ≤ q - 1 := Nat.le_of_dvd (by omega) hdvd
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  have hq3 : 2 < q := by omega
  have hdvd' : d ∣ q - 1 := dvd_trans ⟨2, mul_comm 2 d⟩ hdvd
  obtain ⟨F, hrank, hgal, hcyc, hsplit, -⟩ :=
    exists_intermediateField_finrank_eq_and_splitsCompletely q hd hdvd' E
  haveI := hgal
  refine ⟨F, hrank, hgal, hcyc, ?_, hsplit, ?_⟩
  · refine isTotallyReal_of_two_mul_finrank_dvd_cyclotomic q E hq3 F ?_
    rw [hrank, finrank_cyclotomic_of_prime q E]
    exact hdvd
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
