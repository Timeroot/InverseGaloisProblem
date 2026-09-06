/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.Splitting
import InverseGalois.CFT.CyclotomicCompositum
import InverseGalois.CFT.Scholz.AuxPrimeChoice
import InverseGalois.CFT.Scholz.PrimeIndependence
import InverseGalois.CFT.Scholz.RadicalDegree
import InverseGalois.NumberTheory.SplitDensityFamily

/-!
# One auxiliary prime for arbitrarily many prescribed non-residues

Asking a single prime to make two prescribed primes power non-residues costs two reciprocal
enlargement factors, and two halves already exhaust the budget of the density argument.  Asking it
of arbitrarily many prescribed primes at once therefore looks hopeless at the exponent `ℓ`.  It
becomes easy at a higher exponent: a radical of exponent `ℓ ^ M` enlarges the cyclotomic field of
conductor `ℓ ^ d` by the full factor `ℓ ^ M`, whatever `M ≤ d`, so the union bound only has to beat
`ℓ ^ M`, and the number of prescribed primes is fixed while `M` is not.

The enlargement is full because for an odd prime the polynomial `X ^ (ℓ ^ M)` minus a constant is
irreducible as soon as the constant has no `ℓ`-th root — no condition at the higher exponent is
needed — and a rational prime has no `ℓ`-th root in a nilpotent extension of the rationals
containing the `ℓ`-th roots of unity.  Reading the resulting failure to split through the power
residue criterion turns it into the required simultaneous non-residue statement.

## Main results

* `InverseGalois.CFT.exists_prime_splitsCompletely_not_radicalField_family_of_le_finrank`: the
  density argument for a whole family of radical fields, run from a common lower bound for the
  degrees of the composita.
* `InverseGalois.CFT.le_finrank_sup_radicalField_primePow`: **a radical of odd prime-power exponent
  multiplies the degree of a field of matching roots of unity by that exponent**, as soon as the
  radicand has no root of prime exponent there.
* `InverseGalois.CFT.exists_prime_two_mul_dvd_sub_one_forall_pow_ne_one`: **a prime congruent to one
  modulo twice a prescribed power of an odd prime, modulo which every member of a prescribed set of
  fewer primes than the exponent allows is a power non-residue.**

## Tags

Chebotarev density, radical extension, power residue, auxiliary prime, cyclotomic field
-/

open Module Polynomial NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### The density argument for a family of radical fields -/

section Density

/-- **A family of rational numbers whose radical fields all enlarge a Galois extension by a common
factor admits infinitely many primes splitting completely in that extension but in none of the
radical fields**, provided the family has fewer members than the enlargement factor.  The
reciprocals of the degrees of the composita then add up to less than the reciprocal of the degree of
the extension, which is what the comparison of densities needs. -/
theorem exists_prime_splitsCompletely_not_radicalField_family_of_le_finrank {ι : Type*}
    (I : Finset ι) {ℓ n : ℕ} {A : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A]
    [IsGalois ℚ ↥A] {m : ι → ℚ} (hn : n ≠ 0)
    (h : ∀ i ∈ I, n * finrank ℚ ↥A ≤ finrank ℚ ↥(A ⊔ radicalField ℓ ({m i} : Finset ℚ)))
    (hlt : (I.card : ℝ) / (n : ℝ) < 1) (T : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ SplitsCompletely ↥A q ∧
      ∀ i ∈ I, ¬ SplitsCompletely ↥(radicalField ℓ ({m i} : Finset ℚ)) q := by
  classical
  have hApos : (0 : ℝ) < (finrank ℚ ↥A : ℝ) := by
    have := Module.finrank_pos (R := ℚ) (M := ↥A)
    positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hAne : (finrank ℚ ↥A : ℝ) ≠ 0 := ne_of_gt hApos
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hstep : ∀ i ∈ I, 1 / (finrank ℚ ↥(A ⊔ radicalField ℓ ({m i} : Finset ℚ)) : ℝ)
      ≤ 1 / ((n : ℝ) * (finrank ℚ ↥A : ℝ)) := fun i hi =>
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast h i hi)
  have hsum : ∑ i ∈ I, 1 / (finrank ℚ ↥(A ⊔ radicalField ℓ ({m i} : Finset ℚ)) : ℝ)
      ≤ (I.card : ℝ) * (1 / ((n : ℝ) * (finrank ℚ ↥A : ℝ))) := by
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul I _ _ hstep
  have hrewrite : (I.card : ℝ) * (1 / ((n : ℝ) * (finrank ℚ ↥A : ℝ)))
      = ((I.card : ℝ) / (n : ℝ)) / (finrank ℚ ↥A : ℝ) := by
    field_simp
  have hlt' : ∑ i ∈ I, 1 / (finrank ℚ ↥(A ⊔ radicalField ℓ ({m i} : Finset ℚ)) : ℝ)
      < 1 / (finrank ℚ ↥A : ℝ) := by
    refine lt_of_le_of_lt hsum ?_
    rw [hrewrite]
    exact (div_lt_div_iff_of_pos_right hApos).mpr hlt
  have hinf := infinite_setOf_splitsCompletely_not_splitsCompletely_family I ↥A
    (fun i => ↥(A ⊔ radicalField ℓ ({m i} : Finset ℚ))) hlt'
  obtain ⟨q, ⟨⟨hqp, hqA, hqB⟩, hqT⟩⟩ := (hinf.diff T.finite_toSet).nonempty
  refine ⟨q, hqp, fun hc => hqT (Finset.mem_coe.mpr hc), hqA, fun i hi hc => hqB i hi ?_⟩
  exact splitsCompletely_sup A (radicalField ℓ ({m i} : Finset ℚ)) hqp hqA hc

end Density

/-! ### The degree of a radical of odd prime-power exponent -/

section PrimePowerDegree

variable {ℓ M : ℕ} {A : IntermediateField ℚ (AlgebraicClosure ℚ)} {m : ℚ}

/-- **Over an intermediate field of the algebraic closure, `X` raised to a power of an odd prime,
minus a rational number having no root of prime exponent there, is irreducible.** -/
theorem irreducible_X_pow_primePow_sub_C_of_forall_pow_ne (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hm : ∀ u ∈ A, u ^ ℓ ≠ algebraMap ℚ (AlgebraicClosure ℚ) m) :
    Irreducible ((X : (↥A)[X]) ^ ℓ ^ M - C (algebraMap ℚ ↥A m)) := by
  refine X_pow_sub_C_irreducible_of_prime_pow hℓ hℓ2 M fun b hb =>
    hm (b : AlgebraicClosure ℚ) b.2 ?_
  rw [← algebraMap_intermediateField_eq A m, ← hb, map_pow]
  rfl

/-- **The compositum of a field containing the roots of unity of odd prime-power order with the
radical field of that order of a rational number having no root of prime exponent there has degree
the full multiple of the degree of the field.**  The corresponding radical polynomial is
irreducible, so one root of it already generates an extension of that degree. -/
theorem le_finrank_sup_radicalField_primePow (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    {η : AlgebraicClosure ℚ} (hη : IsPrimitiveRoot η (ℓ ^ M)) (hηA : η ∈ A) (hm0 : m ≠ 0)
    (hm : ∀ u ∈ A, u ^ ℓ ≠ algebraMap ℚ (AlgebraicClosure ℚ) m) :
    ℓ ^ M * finrank ℚ ↥A ≤ finrank ℚ ↥(A ⊔ radicalField (ℓ ^ M) ({m} : Finset ℚ)) := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap ℚ (AlgebraicClosure ℚ) m) (pow_pos hℓ.pos M)
  refine le_finrank_sup_radicalField_singleton (pow_ne_zero M hℓ.ne_zero) hη hηA hm0 hα ?_
  exact (finrank_adjoin_of_irreducible (pow_ne_zero M hℓ.ne_zero)
    (irreducible_X_pow_primePow_sub_C_of_forall_pow_ne hℓ hℓ2 hm) hα).ge

end PrimePowerDegree

/-! ### The auxiliary prime for a whole set of prescribed primes -/

section AuxPrime

/-- **A prime congruent to one modulo twice a prescribed power of an odd prime, modulo which every
member of a prescribed set of primes is a power non-residue at a chosen lower exponent.**  The only
constraint is that the set have fewer members than that lower exponent allows: over the cyclotomic
field of the higher conductor the radical field of a rational prime at the lower exponent multiplies
the degree by that exponent, since a rational prime has no root of prime exponent in an abelian
extension of the rationals, so the union bound behind the density argument still leaves room. -/
theorem exists_prime_two_mul_dvd_sub_one_forall_pow_ne_one {ℓ d M : ℕ} (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hd : d ≠ 0) (hMd : M ≤ d) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hcard : P.card < ℓ ^ M) (T : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ 2 * ℓ ^ d ∣ q - 1 ∧
      ∀ p ∈ P, p ≠ q ∧ ((p : ℕ) : ZMod q) ^ ((q - 1) / ℓ ^ M) ≠ 1 := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero (ℓ ^ d) := ⟨pow_ne_zero d hℓ.ne_zero⟩
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hℓodd
    omega
  have hℓ3 : 2 < ℓ := lt_of_le_of_ne hℓ.two_le (Ne.symm hℓ2)
  have hle : ℓ ≤ ℓ ^ d := Nat.le_self_pow hd ℓ
  have hnil : Group.IsNilpotent Gal(↥(cycSubfield (ℓ ^ d))/ℚ) :=
    nilpotent_of_mulEquiv
      (IsCyclotomicExtension.Rat.galEquivZMod (ℓ ^ d) ↥(cycSubfield (ℓ ^ d))).symm
  have hmem : cycRoot (ℓ ^ d) ∈ cycSubfield (ℓ ^ d) := IntermediateField.subset_adjoin ℚ _ rfl
  have hprod1 : ℓ ^ d = ℓ ^ (d - 1) * ℓ := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    rw [pow_succ]
  have hζ : IsPrimitiveRoot (cycRoot (ℓ ^ d) ^ ℓ ^ (d - 1)) ℓ :=
    IsPrimitiveRoot.pow (Nat.pos_of_ne_zero (pow_ne_zero d hℓ.ne_zero)) (cycRoot_spec (ℓ ^ d))
      hprod1
  have hζA : cycRoot (ℓ ^ d) ^ ℓ ^ (d - 1) ∈ cycSubfield (ℓ ^ d) := pow_mem hmem _
  have hprodM : ℓ ^ d = ℓ ^ (d - M) * ℓ ^ M := by
    rw [← pow_add]
    congr 1
    omega
  have hη : IsPrimitiveRoot (cycRoot (ℓ ^ d) ^ ℓ ^ (d - M)) (ℓ ^ M) :=
    IsPrimitiveRoot.pow (Nat.pos_of_ne_zero (pow_ne_zero d hℓ.ne_zero)) (cycRoot_spec (ℓ ^ d))
      hprodM
  have hηA : cycRoot (ℓ ^ d) ^ ℓ ^ (d - M) ∈ cycSubfield (ℓ ^ d) := pow_mem hmem _
  have hv : ∀ p : ℕ, p.Prime → ∀ y : ℚ, y ^ ℓ ≠ ((p : ℕ) : ℚ) := by
    intro p hp y
    have h := pow_ne_prod_pow (ℓ := ℓ) (S := ({p} : Finset ℕ)) (a := fun _ => 1) (p₀ := p)
      (fun r hr => by rwa [Finset.mem_singleton.mp hr]) (Finset.mem_singleton_self p)
      (fun hdv => hℓ.one_lt.ne' (Nat.dvd_one.mp hdv)) y
    simpa using h
  have hdeg : ∀ p ∈ P, ℓ ^ M * finrank ℚ ↥(cycSubfield (ℓ ^ d))
      ≤ finrank ℚ ↥(cycSubfield (ℓ ^ d) ⊔ radicalField (ℓ ^ M) ({((p : ℕ) : ℚ)} : Finset ℚ)) := by
    intro p hp
    have hpp := hP p hp
    exact le_finrank_sup_radicalField_primePow hℓ hℓ2 hη hηA
      (Nat.cast_ne_zero.mpr hpp.ne_zero)
      fun u hu => pow_ne_of_isNilpotent hℓodd hnil hζ hζA (hv p hpp) hu
  have hltcard : ((P.card : ℕ) : ℝ) / ((ℓ ^ M : ℕ) : ℝ) < 1 := by
    rw [div_lt_one (by exact_mod_cast pow_pos hℓ.pos M)]
    exact_mod_cast hcard
  obtain ⟨q, hqp, hqT, hqA, hqR⟩ :=
    exists_prime_splitsCompletely_not_radicalField_family_of_le_finrank
      (A := cycSubfield (ℓ ^ d)) (ℓ := ℓ ^ M) (m := fun p : ℕ => ((p : ℕ) : ℚ)) P
      (pow_ne_zero M hℓ.ne_zero) hdeg hltcard (insert ℓ (P ∪ T))
  have hqℓ : q ≠ ℓ := by
    rintro rfl
    exact hqT (Finset.mem_insert_self _ _)
  have hdvd : ℓ ^ d ∣ q - 1 := by
    haveI : Fact q.Prime := ⟨hqp⟩
    have hnd : ¬ q ∣ ℓ ^ d := fun hc =>
      hqℓ ((Nat.prime_dvd_prime_iff_eq hqp hℓ).mp (hqp.dvd_of_dvd_pow hc))
    exact (Nat.modEq_iff_dvd' hqp.one_le).mp
      (modEq_of_splitsCompletely (ℓ ^ d) ↥(cycSubfield (ℓ ^ d)) q hnd hqA).symm
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h1 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hpar : 2 ∣ q - 1 := by
    obtain ⟨c, hc⟩ := hqp.odd_of_ne_two hq2
    omega
  have hcop : Nat.Coprime 2 (ℓ ^ d) :=
    ((Nat.coprime_primes Nat.prime_two hℓ).mpr (by omega)).pow_right d
  have hdvdM : ℓ ^ M ∣ q - 1 := dvd_trans (pow_dvd_pow ℓ hMd) hdvd
  refine ⟨q, hqp, fun hc => hqT (Finset.mem_insert_of_mem (Finset.mem_union_right P hc)),
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpar hdvd, fun p hpP => ⟨?_, fun hpow => hqR p hpP ?_⟩⟩
  · rintro rfl
    exact hqT (Finset.mem_insert_of_mem (Finset.mem_union_left T hpP))
  · have hpp := hP p hpP
    have hpq : p ≠ q := by
      rintro rfl
      exact hqT (Finset.mem_insert_of_mem (Finset.mem_union_left T hpP))
    have hcast : (((p : ℕ) : ℤ) : ℚ) = ((p : ℕ) : ℚ) := by
      push_cast
      ring
    rw [← hcast]
    refine splitsCompletely_radicalField_of_dvd (pow_ne_zero M hℓ.ne_zero) hqp hdvdM ?_ ?_
    · intro hdv
      rw [Int.natCast_dvd_natCast] at hdv
      exact hpq ((Nat.prime_dvd_prime_iff_eq hqp hpp).mp hdv).symm
    · exact_mod_cast hpow

end AuxPrime

end InverseGalois.CFT
