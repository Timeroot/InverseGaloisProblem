import Mathlib
import InverseGalois.CFT.Cyclotomic.CyclicSubfield
import InverseGalois.CFT.Cyclotomic.Ramified
import InverseGalois.CFT.Unramified

/-!
# Cyclic extensions of `ℚ` ramified at a single prime

The Scholz–Reichardt construction of solvable extensions of `ℚ` is driven by a supply of *building
blocks*: cyclic extensions `F / ℚ` of a prescribed prime-power degree `ℓ ^ N` whose ramification is
concentrated at one auxiliary prime `q`, with `q` as large as one likes and `q ≡ 1 [MOD ℓ ^ N]`.
This file assembles such a block out of the cyclic-subfield construction of
`InverseGalois.CFT.Cyclotomic.CyclicSubfield` and the cyclotomic ramification bookkeeping of
`InverseGalois.CFT.Cyclotomic.Ramified`.

The extension is cut out of the cyclotomic field `ℚ(ζ_q)` of prime conductor `q`.  Since `ℚ(ζ_q)`
is ramified only at `q`, so is every subfield, and Minkowski's theorem forces the subfield — being
of degree `ℓ ^ N > 1` — to be ramified somewhere; the two facts together pin the ramification
locus down to exactly `{q}`.

## Main results

* `InverseGalois.CFT.isUnramifiedAt_of_not_mem`: a number field `F` mapping into `ℚ(ζ_q)`, for `q`
  prime, is unramified over `ℤ` at every nonzero prime of `𝓞 F` that does not contain `q`.
* `InverseGalois.CFT.mem_of_not_isUnramifiedAt`: the contrapositive form, that a ramified nonzero
  prime of such an `F` contains `q`.
* `InverseGalois.CFT.ramificationIdxIn_cyclotomic_prime`: the prime `q` is totally ramified in
  `ℚ(ζ_q)`, with ramification index `q - 1`.
* `InverseGalois.CFT.not_isUnramifiedAt_cyclotomic_prime`: consequently, for `q > 2` the prime of
  `𝓞 ℚ(ζ_q)` above `q` is ramified over `ℤ`.
* `InverseGalois.CFT.exists_ne_bot_isPrime_not_isUnramifiedAt`: Minkowski's theorem in the form
  that a number field of degree greater than one is ramified at some *nonzero* prime.
* `InverseGalois.CFT.exists_cyclic_ramified_at_one_prime`: the packaged building block, a cyclic
  extension of `ℚ` of degree `ℓ ^ N` unramified away from a large prime `q ≡ 1 [MOD ℓ ^ N]`.
* `InverseGalois.CFT.exists_cyclic_ramified_exactly_at_one_prime`: the same block for `N ≠ 0`,
  recording in addition that it really is ramified at `q`.
-/

open scoped NumberField

open Module

namespace InverseGalois.CFT

/-! ### Subfields of a cyclotomic field of prime conductor -/

/-- Let `q` be a prime and let `F` be a number field admitting a map into the cyclotomic field
`ℚ(ζ_q)`.  Then `F` is unramified over `ℤ` at every nonzero prime of `𝓞 F` not containing `q`. -/
theorem isUnramifiedAt_of_not_mem (q : ℕ) [hq : Fact q.Prime] {F : Type*} [Field F] [NumberField F]
    [Algebra F (CyclotomicField q ℚ)] (Q : Ideal (𝓞 F)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (h : (q : 𝓞 F) ∉ Q) : Algebra.IsUnramifiedAt ℤ Q := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  refine isUnramifiedAt_of_forall_prime_not_dvd_of_algebra q (CyclotomicField q ℚ) Q hQ ?_
  intro r hr hrQ hrdvd
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hr hq.out).1 hrdvd
  exact h hrQ

/-- In the situation of `isUnramifiedAt_of_not_mem`, a nonzero prime of `𝓞 F` that is ramified
over `ℤ` must contain the prime `q`. -/
theorem mem_of_not_isUnramifiedAt (q : ℕ) [Fact q.Prime] {F : Type*} [Field F] [NumberField F]
    [Algebra F (CyclotomicField q ℚ)] (Q : Ideal (𝓞 F)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (h : ¬ Algebra.IsUnramifiedAt ℤ Q) : (q : 𝓞 F) ∈ Q := by
  by_contra hmem
  exact h (isUnramifiedAt_of_not_mem q Q hQ hmem)

/-! ### Total ramification of the conductor -/

/-- A prime `q` is totally ramified in the cyclotomic field `ℚ(ζ_q)`: its ramification index there
is `q - 1 = [ℚ(ζ_q) : ℚ]`. -/
theorem ramificationIdxIn_cyclotomic_prime (q : ℕ) [hq : Fact q.Prime] :
    (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 (CyclotomicField q ℚ)) = q - 1 := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime q (CyclotomicField q ℚ)

/-- For a prime `q > 2`, the prime of `𝓞 ℚ(ζ_q)` lying above `q` is ramified over `ℤ`, since its
ramification index is `q - 1 > 1`. -/
theorem not_isUnramifiedAt_cyclotomic_prime (q : ℕ) [hq : Fact q.Prime] (hq2 : 2 < q)
    (P : Ideal (𝓞 (CyclotomicField q ℚ))) [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] : ¬ Algebra.IsUnramifiedAt ℤ P := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  have hunder : Ideal.span {(q : ℤ)} = P.under ℤ := Ideal.LiesOver.over
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (ne_bot_of_liesOver_span q P), ← hunder,
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime q (CyclotomicField q ℚ) P]
  omega

/-! ### Minkowski's theorem, at a nonzero prime -/

/-- **Minkowski's theorem**, sharpened to produce a *nonzero* prime: a number field of degree
greater than one over `ℚ` is ramified at some nonzero prime of its ring of integers. -/
theorem exists_ne_bot_isPrime_not_isUnramifiedAt (L : Type*) [Field L] [NumberField L]
    (h : 1 < finrank ℚ L) :
    ∃ P : Ideal (𝓞 L), ∃ _ : P.IsPrime, P ≠ ⊥ ∧ ¬ Algebra.IsUnramifiedAt ℤ P := by
  by_contra hcon
  push_neg at hcon
  have hdiff : differentIdeal ℤ (𝓞 L) = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ hne
    haveI : P.IsPrime := hPmax.isPrime
    have hPne : P ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField hPmax
        (NumberField.RingOfIntegers.not_isField (K := L))
    exact (not_dvd_differentIdeal_iff (A := ℤ) (B := 𝓞 L) (P := P)).mpr
      (hcon P inferInstance hPne) (Ideal.dvd_iff_le.mpr hPle)
  have hdiscr : (NumberField.discr L).natAbs = 1 := by
    have hd := NumberField.absNorm_differentIdeal L (𝓞 L)
    rw [hdiff] at hd
    simpa using hd.symm
  have h2 : (2 : ℤ) < |NumberField.discr L| := NumberField.abs_discr_gt_two h
  rw [Int.abs_eq_natAbs, hdiscr] at h2
  norm_num at h2

/-! ### The Scholz–Reichardt building block -/

/-- **The Scholz–Reichardt building block.**  Let `ℓ` be a prime and `N B : ℕ`.  There is a prime
`q > B` with `q ≡ 1 [MOD ℓ ^ N]` and a cyclic Galois extension `F / ℚ` of degree `ℓ ^ N`, sitting
inside `ℚ(ζ_q)`, which is unramified over `ℤ` at every nonzero prime of `𝓞 F` not containing
`q`. -/
theorem exists_cyclic_ramified_at_one_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (N B : ℕ) :
    ∃ q : ℕ, B < q ∧ q.Prime ∧ q ≡ 1 [MOD ℓ ^ N] ∧
      ∃ F : IntermediateField ℚ (CyclotomicField q ℚ), ∃ _ : NumberField F,
        IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) ∧ finrank ℚ F = ℓ ^ N ∧
        ∀ (Q : Ideal (𝓞 F)) [Q.IsPrime], Q ≠ ⊥ → (q : 𝓞 F) ∉ Q →
          Algebra.IsUnramifiedAt ℤ Q := by
  obtain ⟨q, hqB, hqp, hq1, F, hgal, hcyc, hrank, hNF⟩ :=
    exists_prime_and_cyclic_intermediateField hℓ N B
  haveI : Fact q.Prime := ⟨hqp⟩
  haveI := hNF
  refine ⟨q, hqB, hqp, hq1, F, hNF, hgal, hcyc, hrank, ?_⟩
  intro Q _ hQ hqQ
  exact isUnramifiedAt_of_not_mem q Q hQ hqQ

/-- **The Scholz–Reichardt building block, with its ramification locus pinned down.**  For a prime
`ℓ`, a nonzero exponent `N` and a bound `B`, there is a prime `q > B` with `q ≡ 1 [MOD ℓ ^ N]` and
a cyclic Galois extension `F / ℚ` of degree `ℓ ^ N` inside `ℚ(ζ_q)` which is unramified at every
nonzero prime of `𝓞 F` not containing `q`, and is ramified at some nonzero prime containing `q`.
That is, `F / ℚ` is ramified at exactly the one prime `q`. -/
theorem exists_cyclic_ramified_exactly_at_one_prime {ℓ : ℕ} (hℓ : ℓ.Prime) {N : ℕ} (hN : N ≠ 0)
    (B : ℕ) :
    ∃ q : ℕ, B < q ∧ q.Prime ∧ q ≡ 1 [MOD ℓ ^ N] ∧
      ∃ F : IntermediateField ℚ (CyclotomicField q ℚ), ∃ _ : NumberField F,
        IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) ∧ finrank ℚ F = ℓ ^ N ∧
        (∀ (Q : Ideal (𝓞 F)) [Q.IsPrime], Q ≠ ⊥ → (q : 𝓞 F) ∉ Q →
          Algebra.IsUnramifiedAt ℤ Q) ∧
        ∃ Q : Ideal (𝓞 F), ∃ _ : Q.IsPrime, Q ≠ ⊥ ∧ (q : 𝓞 F) ∈ Q ∧
          ¬ Algebra.IsUnramifiedAt ℤ Q := by
  obtain ⟨q, hqB, hqp, hq1, F, hgal, hcyc, hrank, hNF⟩ :=
    exists_prime_and_cyclic_intermediateField hℓ N B
  haveI : Fact q.Prime := ⟨hqp⟩
  haveI := hNF
  have hlt : 1 < finrank ℚ F := by
    rw [hrank]
    exact Nat.one_lt_pow hN hℓ.one_lt
  obtain ⟨Q, hQp, hQbot, hQram⟩ := exists_ne_bot_isPrime_not_isUnramifiedAt (F : Type _) hlt
  refine ⟨q, hqB, hqp, hq1, F, hNF, hgal, hcyc, hrank, ?_, Q, hQp, hQbot, ?_, hQram⟩
  · intro P _ hP hqP
    exact isUnramifiedAt_of_not_mem q P hP hqP
  · exact mem_of_not_isUnramifiedAt q Q hQbot hQram

end InverseGalois.CFT
