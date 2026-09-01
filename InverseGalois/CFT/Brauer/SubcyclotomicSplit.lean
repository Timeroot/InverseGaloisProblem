/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicNorm
import InverseGalois.CFT.Brauer.OddArchimedean
import InverseGalois.CFT.Brauer.RelativeCyclic
import InverseGalois.CFT.Brauer.SplitLocalDegree
import InverseGalois.CFT.Brauer.SubcyclotomicReciprocity
import InverseGalois.CFT.Cyclotomic.AuxiliarySubfield
import InverseGalois.CFT.Local.RatResidueDegree

/-!
# Reciprocity for a class split by a subfield of a cyclotomic field

A cyclic extension of the rationals splits a Brauer class exactly when its local degree kills the
local invariant at every finite place and its real places split the class.  A class which the
reals already split meets the archimedean conditions automatically, and for an extension of prime
degree the local degree at a rational prime is that degree unless the prime splits completely.  So
such a class killed by a prime is split by a cyclic extension of that degree as soon as none of the
rational primes carrying a nontrivial invariant splits completely in it.

Every class split by a cyclic extension is a cyclic algebra, and the total invariant of a cyclic
algebra split by a totally real subfield of the cyclotomic field of an odd prime conductor, totally
ramified there, vanishes.  Reciprocity therefore holds for every class of prime order split by the
reals whose bad primes can be made to miss the splitting law of such a subfield — and that law is a
power residue condition modulo the conductor.

## Main results

* `InverseGalois.CFT.mem_relative_of_forall_not_splitsCompletely`: **a Brauer class of the
  rationals of prime order which the reals split is split by a cyclic extension of that degree in
  which no prime carrying a nontrivial invariant splits completely.**
* `InverseGalois.CFT.totalInvariant_eq_one_of_mem_relative_subcyclotomic`: **the total invariant of
  a Brauer class of the rationals split by a totally real subfield of the cyclotomic field of an
  odd prime conductor, totally ramified there, vanishes.**
* `InverseGalois.CFT.totalInvariant_eq_one_of_forall_pow_ne_one`: **reciprocity for a class of
  prime order split by the reals all of whose bad primes are non-residues modulo an auxiliary
  prime.**
* `InverseGalois.CFT.mem_relative_of_forall_not_dvd_primePow` and
  `InverseGalois.CFT.totalInvariant_eq_one_of_forall_pow_ne_one_primePow`: the same two statements
  at a prime-power order, where the local degree is read off from the order of the decomposition
  group instead of from splitting completely.

## Tags

Brauer group, local invariant, reciprocity, cyclotomic field, power residue symbol, auxiliary
prime, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module MulAction NumberField InverseGalois.NumberTheory

open scoped Pointwise

/-! ### The rational prime below a finite place -/

section Below

/-- Every finite place of a number field lies above the place of the rationals attached to a
rational prime. -/
theorem exists_prime_primeUnder_eq_ratPlace {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) :
    ∃ (p : ℕ) (hp : p.Prime), primeUnder (𝓞 ℚ) w = ratPlace p hp ∧
      w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hp : (Rat.HeightOneSpectrum.natGenerator (primeUnder (𝓞 ℚ) w)).Prime :=
    Rat.HeightOneSpectrum.prime_natGenerator _
  have heq : primeUnder (𝓞 ℚ) w
      = ratPlace (Rat.HeightOneSpectrum.natGenerator (primeUnder (𝓞 ℚ) w)) hp :=
    heightOneSpectrum_rat_eq_of_natCast_mem hp (natCast_natGenerator_mem _)
      (natCast_mem_ratPlace _ hp)
  exact ⟨_, hp, heq, liesOver_span_of_primeUnder_eq_ratPlace hp w heq⟩

end Below

/-! ### Splitting a class of prime power order -/

section Split

/-- **A Brauer class of the rationals of odd prime order is split by a cyclic extension of that
degree in which no prime carrying a nontrivial invariant splits completely.**  At a place above
such a prime the local degree is the whole degree, which kills an invariant of that order; at every
other finite place the invariant is already trivial; and the real places split the class as soon as
the reals do. -/
theorem mem_relative_of_forall_not_splitsCompletely {N : ℕ} (hN : N.Prime)
    {x : BrauerGroup.{0, 0} ℚ} (hxreal : x ∈ BrauerGroup.relative ℚ ℝ) (hx : x ^ N = 1)
    (F : Type) [Field F] [NumberField F]
    [IsGalois ℚ F] [IsCyclic Gal(F/ℚ)] (hcard : Nat.card Gal(F/ℚ) = N)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), placeInvariant ℚ (ratPlace p hp) x ≠ 1 →
      ¬ SplitsCompletely F p) :
    x ∈ BrauerGroup.relative ℚ F := by
  rw [mem_relative_iff_forall_pow_placeInvariant]
  refine ⟨fun w => ?_, fun U hU => mem_relative_completion_of_mem_relative_real hxreal hU⟩
  by_cases hinv : placeInvariant ℚ (primeUnder (𝓞 ℚ) w) x = 1
  · rw [hinv, one_pow]
  · obtain ⟨p, hp, hpw, hlies⟩ := exists_prime_primeUnder_eq_ratPlace w
    haveI := hlies
    obtain ⟨m, hm⟩ := prime_dvd_finrank_adicCompletion_of_not_splitsCompletely F hN hcard hp w
      (hbad p hp (by rwa [hpw] at hinv))
    have hpow : placeInvariant ℚ (primeUnder (𝓞 ℚ) w) x ^ N = 1 := by
      rw [← map_pow, hx, map_one]
    rw [hm, pow_mul, hpow, one_pow]

/-- **A Brauer class of the rationals killed by an odd prime power is split by a cyclic extension
of that degree whose decomposition group at every place carrying a nontrivial invariant is the
whole group.**  The order of that decomposition group is a power of the prime dividing the degree,
so failing to divide the next smaller power makes it the whole degree, which kills an invariant of
order dividing the degree; the real places split the class as soon as the reals do. -/
theorem mem_relative_of_forall_not_dvd_primePow {ℓ e : ℕ} (hℓ : ℓ.Prime)
    {x : BrauerGroup.{0, 0} ℚ} (hxreal : x ∈ BrauerGroup.relative ℚ ℝ) (hx : x ^ ℓ ^ e = 1)
    (F : Type) [Field F] [NumberField F]
    [IsGalois ℚ F] [IsCyclic Gal(F/ℚ)] (hcard : Nat.card Gal(F/ℚ) = ℓ ^ e)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), placeInvariant ℚ (ratPlace p hp) x ≠ 1 →
      ∀ (P : Ideal (𝓞 F)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)})),
        ¬ Nat.card ↥(stabilizer Gal(F/ℚ) P) ∣ ℓ ^ (e - 1)) :
    x ∈ BrauerGroup.relative ℚ F := by
  rw [mem_relative_iff_forall_pow_placeInvariant]
  refine ⟨fun w => ?_, fun U hU => mem_relative_completion_of_mem_relative_real hxreal hU⟩
  by_cases hinv : placeInvariant ℚ (primeUnder (𝓞 ℚ) w) x = 1
  · rw [hinv, one_pow]
  · obtain ⟨p, hp, hpw, hlies⟩ := exists_prime_primeUnder_eq_ratPlace w
    haveI := hlies
    haveI : w.asIdeal.IsPrime := w.isPrime
    obtain ⟨m, hm⟩ := primePow_dvd_finrank_adicCompletion_of_not_dvd F hℓ hcard w
      (hbad p hp (by rwa [hpw] at hinv) w.asIdeal ‹_› ‹_›)
    have hpow : placeInvariant ℚ (primeUnder (𝓞 ℚ) w) x ^ ℓ ^ e = 1 := by
      rw [← map_pow, hx, map_one]
    rw [hm, pow_mul, hpow, one_pow]

end Split

/-! ### Reciprocity for a split class -/

section Reciprocity

/-- **The total invariant of a Brauer class of the rationals split by a totally real subfield of
the cyclotomic field of an odd prime conductor, totally ramified there, vanishes** when the degree
of that subfield is a radical exponent and twice it divides the predecessor of the conductor.  Such
a class is a cyclic algebra over that subfield, and the invariants of a cyclic algebra over it
cancel. -/
theorem totalInvariant_eq_one_of_mem_relative_subcyclotomic (q : ℕ) [hq : Fact q.Prime]
    (hodd : Odd q) (L F : Type) [Field L] [NumberField L] [IsCyclotomicExtension {q} ℚ L]
    [IsGalois ℚ L] [Field F] [NumberField F] [Algebra F L] [IsScalarTower ℚ F L] [IsGalois ℚ F]
    [IsTotallyReal F] {N : ℕ} [NeZero N]
    (hcard : Nat.card Gal(F/ℚ) = N)
    (hinertia : ∀ (Q : Ideal (𝓞 F)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q : ℤ)})),
      Ideal.inertia Gal(F/ℚ) Q = ⊤) (h2N : 2 * N ∣ q - 1)
    {x : BrauerGroup.{0, 0} ℚ} (hx : x ∈ BrauerGroup.relative ℚ F) :
    totalInvariant ℚ x = 1 := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  obtain ⟨g, hg, hgord⟩ := exists_nat_primitiveRoot_of_prime hq.out
  have hgen := forall_mem_zpowers_cyclotomicPowerAut q L hq.out hg hgord
  obtain ⟨a, ha⟩ :=
    exists_cyclicBrauerHom_eq (forall_mem_zpowers_restrictNormal (L := F) hgen) x hx
  rw [← ha]
  exact totalInvariant_cyclicBrauerHom_subcyclotomic q L F hodd hcard hinertia hg hgord
    hgen h2N a

/-- **Reciprocity for a Brauer class of the rationals of odd prime order all of whose bad primes
are non-residues modulo an auxiliary prime.**  The subfield of prescribed degree of the cyclotomic
field of the auxiliary prime is totally real and totally ramified at that prime, and a rational
prime splits completely in it exactly when it is a power residue; the bad primes therefore fail to
split completely, so the class is split by that subfield. -/
theorem totalInvariant_eq_one_of_forall_pow_ne_one {N : ℕ} (hN : N.Prime)
    {x : BrauerGroup.{0, 0} ℚ} (hxreal : x ∈ BrauerGroup.relative ℚ ℝ) (hx : x ^ N = 1) {q : ℕ}
    (hq : q.Prime) (hdvd : 2 * N ∣ q - 1)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), placeInvariant ℚ (ratPlace p hp) x ≠ 1 →
      p ≠ q ∧ ((p : ℕ) : ZMod q) ^ ((q - 1) / N) ≠ 1) :
    totalInvariant ℚ x = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hqodd : Odd q := by
    rcases hq.eq_two_or_odd' with rfl | h
    · have h2 := Nat.le_of_dvd (by norm_num) hdvd
      have h3 := hN.two_le
      omega
    · exact h
  obtain ⟨F, hrank, hgal, hcyc, hreal, hsplit, -, hinertia⟩ :=
    exists_intermediateField_subcyclotomic q hN.ne_zero hdvd (CyclotomicField q ℚ)
  haveI := hgal
  haveI := hcyc
  haveI := hreal
  haveI : IsGalois ℚ (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.isGalois {q} ℚ (CyclotomicField q ℚ)
  have hcard : Nat.card Gal(↥F/ℚ) = N := by
    rw [IsGalois.card_aut_eq_finrank ℚ ↥F, hrank]
  refine totalInvariant_eq_one_of_mem_relative_subcyclotomic q hqodd (CyclotomicField q ℚ) ↥F
    hcard hinertia hdvd ?_
  refine mem_relative_of_forall_not_splitsCompletely hN hxreal hx ↥F hcard fun p hp hinv hsc => ?_
  obtain ⟨hpq, hres⟩ := hbad p hp hinv
  exact hres ((hsplit p hp hpq).mp hsc)

/-- **Reciprocity for a Brauer class of the rationals of odd prime-power order all of whose bad
primes are non-residues of the prime exponent modulo an auxiliary prime.**  The subfield of degree
the prime power of the cyclotomic field of the auxiliary prime is totally real and totally ramified
there, and the order of its decomposition group at a prime above a rational prime is read off from
a power residue condition; a prime that is not an `ℓ`-th power residue therefore has the whole
group as decomposition group, so the class is split by that subfield. -/
theorem totalInvariant_eq_one_of_forall_pow_ne_one_primePow {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (he : e ≠ 0) {x : BrauerGroup.{0, 0} ℚ} (hxreal : x ∈ BrauerGroup.relative ℚ ℝ)
    (hx : x ^ ℓ ^ e = 1) {q : ℕ} (hq : q.Prime) (hdvd : 2 * ℓ ^ e ∣ q - 1)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), placeInvariant ℚ (ratPlace p hp) x ≠ 1 →
      p ≠ q ∧ ((p : ℕ) : ZMod q) ^ ((q - 1) / ℓ) ≠ 1) :
    totalInvariant ℚ x = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero (ℓ ^ e) := ⟨pow_ne_zero e hℓ.ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hone : 1 ≤ ℓ ^ e := Nat.one_le_pow e ℓ hℓ.pos
  have hqodd : Odd q := by
    rcases hq.eq_two_or_odd' with rfl | h
    · have h2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    · exact h
  have hNdvd : ℓ ^ e ∣ q - 1 := dvd_trans ⟨2, mul_comm 2 (ℓ ^ e)⟩ hdvd
  have hsplitpow : ℓ ^ e = ℓ * ℓ ^ (e - 1) := by
    conv_lhs => rw [show e = 1 + (e - 1) by omega]
    rw [pow_add, pow_one]
  have harith : ℓ ^ (e - 1) * ((q - 1) / ℓ ^ e) = (q - 1) / ℓ := by
    obtain ⟨k, hk⟩ := hNdvd
    rw [hk, Nat.mul_div_cancel_left _ (pow_pos hℓ.pos e), hsplitpow, mul_assoc,
      Nat.mul_div_cancel_left _ hℓ.pos]
  haveI : IsGalois ℚ (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.isGalois {q} ℚ (CyclotomicField q ℚ)
  obtain ⟨F, hrank, hgal, hcyc, hreal, -, hdeg, hinertia⟩ :=
    exists_intermediateField_subcyclotomic q (pow_ne_zero e hℓ.ne_zero) hdvd (CyclotomicField q ℚ)
  haveI := hgal
  haveI := hcyc
  haveI := hreal
  have hcard : Nat.card Gal(↥F/ℚ) = ℓ ^ e := by
    rw [IsGalois.card_aut_eq_finrank ℚ ↥F, hrank]
  refine totalInvariant_eq_one_of_mem_relative_subcyclotomic q hqodd (CyclotomicField q ℚ) ↥F
    hcard hinertia hdvd ?_
  refine mem_relative_of_forall_not_dvd_primePow hℓ hxreal hx ↥F hcard ?_
  intro p hp hinv P hP hPo
  obtain ⟨hpq, hres⟩ := hbad p hp hinv
  rw [hdeg p hp hpq P hP hPo (ℓ ^ (e - 1)), harith]
  exact hres

end Reciprocity

end InverseGalois.CFT
