import Mathlib
import InverseGalois.CFT.Cyclotomic.OnePrimeRamified
import InverseGalois.CFT.Cyclotomic.PrimeSelection
import InverseGalois.CFT.Level

/-!
# The Scholz–Reichardt building block

The inductive step of the Scholz–Reichardt construction needs, at each stage, an auxiliary cyclic
extension `F / ℚ` of degree a prescribed prime power `ℓ ^ N` subject to three demands at once:

* the single prime `q` it ramifies at is congruent to one modulo `ℓ ^ N`, so that `F` has level `N`
  in the sense of `InverseGalois.CFT.IsLevel`;
* `q` splits completely in a field `E` fixed in advance, so that `F` is linearly disjoint from `E`
  and the ramification of `E` and of `F` stay out of each other's way;
* `q` exceeds any prescribed bound, which is how the first two demands are met simultaneously for
  every stage of the induction.

This file supplies exactly that block.  The extension is cut out of the cyclotomic field `ℚ(ζ_q)`
by the Galois correspondence, `q` is produced by the effective form of Dirichlet's theorem
refined by the splitting condition, and the level statement follows because the only rational
prime ramified in a subfield of `ℚ(ζ_q)` is `q` itself.

## Main results

* `InverseGalois.CFT.eq_of_natCast_mem`: a rational prime `p` whose prime of `𝓞 F` contains another
  rational prime `q` equals `q`.
* `InverseGalois.CFT.isLevel_of_unramified_outside`: a number field unramified away from a single
  prime `q ≡ 1 [MOD ℓ ^ N]` has level `N` at `ℓ`.
* `InverseGalois.CFT.exists_cyclic_intermediateField_of_dvd`: for `q` prime and `d ∣ q - 1`, the
  cyclotomic field `ℚ(ζ_q)` contains a cyclic extension of `ℚ` of degree `d`, unramified away
  from `q`.
* `InverseGalois.CFT.exists_splitsCompletely_cyclic_of_isLevel`: the assembled building block.
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### Recognising the ramified prime -/

/-- If a prime of `𝓞 F` lying over the rational prime `p` contains the rational prime `q`, then
`p = q`. -/
theorem eq_of_natCast_mem {F : Type*} [Field F] [NumberField F] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) {P : Ideal (𝓞 F)} (hover : P.LiesOver (Ideal.span {(p : ℤ)}))
    (hmem : (q : 𝓞 F) ∈ P) : p = q := by
  have hZ : (q : ℤ) ∈ P.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap]
    simpa using hmem
  rw [← hover.over, Ideal.mem_span_singleton] at hZ
  exact (Nat.prime_dvd_prime_iff_eq hp hq).1 (Int.ofNat_dvd.mp (by exact_mod_cast hZ))

/-- A prime of `𝓞 F` lying over a rational prime is nonzero. -/
theorem ne_bot_of_liesOver_natCast {F : Type*} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime)
    {P : Ideal (𝓞 F)} (hover : P.LiesOver (Ideal.span {(p : ℤ)})) : P ≠ ⊥ := by
  intro h
  have hspan : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  refine hspan ?_
  rw [hover.over, h, Ideal.under,
    Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 F))]

/-- **A number field ramified only at one prime `q ≡ 1 [MOD ℓ ^ N]` has level `N`.**  This is the
form in which the level hypothesis of the Scholz–Reichardt induction is verified for the auxiliary
extensions. -/
theorem isLevel_of_unramified_outside {F : Type*} [Field F] [NumberField F] {q ℓ N : ℕ}
    (hq : q.Prime) (hqmod : q ≡ 1 [MOD ℓ ^ N])
    (hunr : ∀ (Q : Ideal (𝓞 F)) [Q.IsPrime], Q ≠ ⊥ → (q : 𝓞 F) ∉ Q →
      Algebra.IsUnramifiedAt ℤ Q) :
    IsLevel ℓ N F := by
  rintro p ⟨hp, P, ⟨hPprime, hPover⟩, hPe⟩
  haveI := hPprime
  haveI := hPover
  have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_natCast hp hPover
  have hram : ¬ Algebra.IsUnramifiedAt ℤ P := by
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP0, ← hPover.over]
    exact hPe
  have hmem : (q : 𝓞 F) ∈ P := by
    by_contra hmem
    exact hram (hunr P hP0 hmem)
  rw [eq_of_natCast_mem hp hq hPover hmem]
  exact hqmod

/-! ### The cyclic subfield attached to a prime -/

/-- For a prime `q` and a divisor `d` of `q - 1`, the cyclotomic field `ℚ(ζ_q)` contains a cyclic
Galois extension of `ℚ` of degree `d`, and that extension is unramified over `ℤ` at every nonzero
prime not containing `q`. -/
theorem exists_cyclic_intermediateField_of_dvd {q d : ℕ} (hq : q.Prime) (hd : d ∣ q - 1) :
    ∃ F : IntermediateField ℚ (CyclotomicField q ℚ),
      IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) ∧ finrank ℚ F = d ∧
      ∀ (Q : Ideal (𝓞 F)) [Q.IsPrime], Q ≠ ⊥ → (q : 𝓞 F) ∉ Q →
        Algebra.IsUnramifiedAt ℤ Q := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : IsGalois ℚ (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.isGalois {q} ℚ (CyclotomicField q ℚ)
  haveI : IsCyclic Gal(CyclotomicField q ℚ/ℚ) :=
    isCyclic_gal_cyclotomic_of_prime q (CyclotomicField q ℚ)
  obtain ⟨F, hgal, hcyc, hrank⟩ :=
    IsCyclic.exists_intermediateField_finrank_eq ℚ (CyclotomicField q ℚ) (d := d)
      (by rwa [finrank_cyclotomic_of_prime q (CyclotomicField q ℚ)])
  refine ⟨F, hgal, hcyc, hrank, ?_⟩
  intro Q _ hQ hqQ
  exact isUnramifiedAt_of_not_mem q Q hQ hqQ

/-! ### The assembled block -/

/-- **The Scholz–Reichardt building block.**  Let `E` be a Galois number field, `ℓ` a prime, and
`N B : ℕ`.  There is a prime `q > B` congruent to one modulo `ℓ ^ N` which splits completely in
`E`, together with a cyclic Galois extension `F / ℚ` of degree `ℓ ^ N` ramified only at `q`; in
particular `F` has level `N` at `ℓ`. -/
theorem exists_splitsCompletely_cyclic_of_isLevel (E : Type*) [Field E] [NumberField E]
    [IsGalois ℚ E] {ℓ : ℕ} (hℓ : ℓ.Prime) (N B : ℕ) :
    ∃ q : ℕ, B < q ∧ q.Prime ∧ q ≡ 1 [MOD ℓ ^ N] ∧ SplitsCompletely E q ∧
      ∃ F : IntermediateField ℚ (CyclotomicField q ℚ),
        IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) ∧ finrank ℚ F = ℓ ^ N ∧ IsLevel ℓ N F ∧
        ∀ (Q : Ideal (𝓞 F)) [Q.IsPrime], Q ≠ ⊥ → (q : 𝓞 F) ∉ Q →
          Algebra.IsUnramifiedAt ℤ Q := by
  obtain ⟨q, hqB, hqp, hqmod, hsplit⟩ :=
    exists_prime_splitsCompletely_and_modEq E (ℓ ^ N) (pow_ne_zero N hℓ.ne_zero) B
  have hdvd : ℓ ^ N ∣ q - 1 := (Nat.modEq_iff_dvd' hqp.one_lt.le).1 hqmod.symm
  obtain ⟨F, hgal, hcyc, hrank, hunr⟩ := exists_cyclic_intermediateField_of_dvd hqp hdvd
  exact ⟨q, hqB, hqp, hqmod, hsplit, F, hgal, hcyc, hrank,
    isLevel_of_unramified_outside hqp hqmod hunr, hunr⟩

end InverseGalois.CFT
