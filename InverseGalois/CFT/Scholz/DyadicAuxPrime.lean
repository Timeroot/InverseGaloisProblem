/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.SquareRoots
import InverseGalois.CFT.Scholz.AuxPrimePair
import InverseGalois.CFT.Scholz.DyadicRadical
import InverseGalois.CFT.Scholz.QuarticRadical

/-!
# Auxiliary primes with two prescribed fourth-power non-residues

The choice of an auxiliary prime for the prime two cannot be made with square residues.  A prime
congruent to one modulo a high power of two is congruent to one modulo eight, so two is a square
modulo it; asking for a prime modulo which two prescribed primes are both non-squares would be
asking for the impossible.  The remedy is to raise the exponent: what the reduction needs is a
prime congruent to one modulo a high power of two modulo which two prescribed primes are both
non-*fourth*-powers, and that is available.

The density argument is the same as for an odd exponent, run with the radical fields of fourth
roots.  Over the cyclotomic field of a two-power conductor at least four, a fourth root of an odd
prime generates a quartic extension — the fourth-power polynomial is irreducible because the prime
has no square root there, only two being ramified — while a fourth root of two generates at least a
quadratic extension, because no abelian extension of the rationals contains one.  Two reciprocal
quarters, or a reciprocal half and a reciprocal quarter, fall short of one; only two reciprocal
halves do not, and that case is avoided by asking the question at two and three instead.

## Main results

* `InverseGalois.CFT.exists_prime_splitsCompletely_not_radicalField₂_of_le_finrank`: the density
  argument for two radical fields, run from lower bounds on the degrees of the composita.
* `InverseGalois.CFT.four_mul_finrank_le_finrank_sup_radicalField_four` and
  `InverseGalois.CFT.two_mul_finrank_le_finrank_sup_radicalField_four`: the two degree bounds.
* `InverseGalois.CFT.exists_prime_dvd_sub_one_pow_four_ne_one`: **a prime congruent to one modulo a
  prescribed power of two modulo which two prescribed primes, not both two, are both fourth-power
  non-residues.**

## Tags

Chebotarev density, radical extension, power residue, auxiliary prime, quartic residue
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### The density argument from lower bounds on the degrees -/

section Density

variable {ℓ : ℕ} {A : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A] [IsGalois ℚ ↥A]

/-- **Two rational numbers whose radical fields enlarge a Galois extension enough admit infinitely
many primes splitting completely in that extension but in neither radical field.**  All the density
bound needs is that the reciprocals of the two enlargement factors add up to less than one. -/
theorem exists_prime_splitsCompletely_not_radicalField₂_of_le_finrank {n₁ n₂ : ℕ} {m₁ m₂ : ℚ}
    (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (h₁ : n₁ * finrank ℚ ↥A ≤ finrank ℚ ↥(A ⊔ radicalField ℓ ({m₁} : Finset ℚ)))
    (h₂ : n₂ * finrank ℚ ↥A ≤ finrank ℚ ↥(A ⊔ radicalField ℓ ({m₂} : Finset ℚ)))
    (hlt : 1 / (n₁ : ℝ) + 1 / (n₂ : ℝ) < 1) (T : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ SplitsCompletely ↥A q ∧
      ¬ SplitsCompletely ↥(radicalField ℓ ({m₁} : Finset ℚ)) q ∧
      ¬ SplitsCompletely ↥(radicalField ℓ ({m₂} : Finset ℚ)) q := by
  classical
  set R₁ : IntermediateField ℚ (AlgebraicClosure ℚ) := radicalField ℓ ({m₁} : Finset ℚ) with hR₁
  set R₂ : IntermediateField ℚ (AlgebraicClosure ℚ) := radicalField ℓ ({m₂} : Finset ℚ) with hR₂
  have hApos : (0 : ℝ) < (finrank ℚ ↥A : ℝ) := by
    have := Module.finrank_pos (R := ℚ) (M := ↥A)
    positivity
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn₂
  have hb₁ : 1 / (finrank ℚ ↥(A ⊔ R₁) : ℝ) ≤ 1 / ((n₁ : ℝ) * (finrank ℚ ↥A : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast h₁)
  have hb₂ : 1 / (finrank ℚ ↥(A ⊔ R₂) : ℝ) ≤ 1 / ((n₂ : ℝ) * (finrank ℚ ↥A : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast h₂)
  have hsplit : 1 / ((n₁ : ℝ) * (finrank ℚ ↥A : ℝ)) + 1 / ((n₂ : ℝ) * (finrank ℚ ↥A : ℝ))
      = (1 / (n₁ : ℝ) + 1 / (n₂ : ℝ)) / (finrank ℚ ↥A : ℝ) := by
    field_simp
  have hlt' : 1 / (finrank ℚ ↥(A ⊔ R₁) : ℝ) + 1 / (finrank ℚ ↥(A ⊔ R₂) : ℝ)
      < 1 / (finrank ℚ ↥A : ℝ) := by
    refine lt_of_le_of_lt (add_le_add hb₁ hb₂) ?_
    rw [hsplit]
    exact (div_lt_div_iff_of_pos_right hApos).mpr hlt
  have hinf := infinite_setOf_splitsCompletely_not_splitsCompletely₂ ↥A ↥(A ⊔ R₁) ↥(A ⊔ R₂) hlt'
  obtain ⟨q, ⟨⟨hqp, hqA, hq₁, hq₂⟩, hqT⟩⟩ := (hinf.diff T.finite_toSet).nonempty
  exact ⟨q, hqp, fun h => hqT (Finset.mem_coe.mpr h), hqA,
    fun h => hq₁ (splitsCompletely_sup A R₁ hqp hqA h),
    fun h => hq₂ (splitsCompletely_sup A R₂ hqp hqA h)⟩

end Density

/-! ### The degree of a fourth radical -/

section QuarticDegree

variable {A : IntermediateField ℚ (AlgebraicClosure ℚ)} {i : AlgebraicClosure ℚ}

/-- **The compositum of a field containing the fourth roots of unity with the field of fourth roots
of a rational number without a square root there has degree four times the degree of the field.**
The fourth-power polynomial is irreducible over the field. -/
theorem four_mul_finrank_le_finrank_sup_radicalField_four (hi : IsPrimitiveRoot i 4) (hiA : i ∈ A)
    {m : ℚ} (hm0 : m ≠ 0) (hm : ∀ u ∈ A, u ^ 2 ≠ algebraMap ℚ (AlgebraicClosure ℚ) m) :
    4 * finrank ℚ ↥A ≤ finrank ℚ ↥(A ⊔ radicalField 4 ({m} : Finset ℚ)) := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap ℚ (AlgebraicClosure ℚ) m) (by norm_num : 0 < 4)
  refine le_finrank_sup_radicalField_singleton (by norm_num) hi hiA hm0 hα ?_
  exact (finrank_adjoin_of_irreducible (by norm_num)
    (irreducible_X_pow_four_sub_C_of_forall_sq_ne hiA
      (sq_eq_neg_one_of_isPrimitiveRoot_four hi) hm) hα).ge

/-- **The compositum of a field containing the fourth roots of unity with the field of fourth roots
of a rational number without a fourth root there has degree at least twice the degree of the
field.** -/
theorem two_mul_finrank_le_finrank_sup_radicalField_four (hi : IsPrimitiveRoot i 4) (hiA : i ∈ A)
    {m : ℚ} (hm0 : m ≠ 0) (hm : ∀ u ∈ A, u ^ 4 ≠ algebraMap ℚ (AlgebraicClosure ℚ) m) :
    2 * finrank ℚ ↥A ≤ finrank ℚ ↥(A ⊔ radicalField 4 ({m} : Finset ℚ)) := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap ℚ (AlgebraicClosure ℚ) m) (by norm_num : 0 < 4)
  exact le_finrank_sup_radicalField_singleton (by norm_num) hi hiA hm0 hα
    (two_le_finrank_adjoin_of_notMem fun h => hm α h hα)

end QuarticDegree

/-! ### Radicals over a cyclotomic field of two-power conductor -/

section Cyclotomic

variable {e : ℕ}

/-- **An odd prime has no square root in a cyclotomic field of two-power conductor**, only two
being ramified there while the prime would have to be. -/
theorem forall_mem_cycSubfield_sq_ne_of_odd_prime [NeZero ((2 : ℕ) ^ e)] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ∀ u ∈ cycSubfield (2 ^ e), u ^ 2 ≠ algebraMap ℚ (AlgebraicClosure ℚ) ((p : ℕ) : ℚ) := by
  intro u hu hsq
  have hy : (⟨u, hu⟩ : ↥(cycSubfield (2 ^ e))) ^ 2 = (((p : ℕ) : ℤ) : ↥(cycSubfield (2 ^ e))) := by
    apply Subtype.ext
    push_cast
    rw [hsq]
    simp
  have hnd : ¬ (((p : ℕ) : ℤ) ^ 2 ∣ ((p : ℕ) : ℤ)) := by
    intro h
    rw [show (((p : ℕ) : ℤ) ^ 2) = ((p ^ 2 : ℕ) : ℤ) by push_cast; ring,
      Int.natCast_dvd_natCast] at h
    have hle := Nat.le_of_dvd hp.pos h
    have h2 := hp.two_le
    nlinarith
  have hmem := mem_ramifiedSet_of_sq_eq_intCast hy hp dvd_rfl hnd
  exact hp2 (Set.mem_singleton_iff.mp (ramifiedSet_cycSubfield_two_pow_subset e hmem))

/-- **Two has no fourth root in a cyclotomic field of two-power conductor**, that field being
abelian over the rationals while neither two nor minus two nor minus one is a rational square. -/
theorem forall_mem_cycSubfield_pow_four_ne_two [NeZero ((2 : ℕ) ^ e)] :
    ∀ u ∈ cycSubfield (2 ^ e), u ^ 4 ≠ algebraMap ℚ (AlgebraicClosure ℚ) (2 : ℚ) := by
  have hcomm : ∀ σ τ : Gal(↥(cycSubfield (2 ^ e))/ℚ), σ * τ = τ * σ := by
    intro σ τ
    have hmul := IsCyclotomicExtension.Rat.galEquivZMod (2 ^ e) ↥(cycSubfield (2 ^ e))
    apply hmul.injective
    rw [map_mul, map_mul, mul_comm]
  exact forall_mem_pow_four_ne_of_mul_comm hcomm rat_sq_ne_two
    (rat_sq_ne_of_neg (by norm_num)) (rat_sq_ne_of_neg (by norm_num))

/-- The fourth root of unity inside a cyclotomic field of two-power conductor at least four. -/
theorem exists_isPrimitiveRoot_four_mem_cycSubfield [NeZero ((2 : ℕ) ^ e)] (he : 2 ≤ e) :
    ∃ i : AlgebraicClosure ℚ, IsPrimitiveRoot i 4 ∧ i ∈ cycSubfield (2 ^ e) := by
  have hprod : (2 : ℕ) ^ e = 2 ^ (e - 2) * 4 := by
    conv_lhs => rw [show e = (e - 2) + 2 by omega]
    rw [pow_add]
    norm_num
  refine ⟨cycRoot ((2 : ℕ) ^ e) ^ (2 : ℕ) ^ (e - 2), ?_, pow_mem ?_ _⟩
  · exact IsPrimitiveRoot.pow (Nat.pos_of_ne_zero (NeZero.ne _)) (cycRoot_spec (2 ^ e)) hprod
  · exact IntermediateField.subset_adjoin ℚ _ rfl

/-- **The enlargement a fourth radical of a prime makes over a cyclotomic field of two-power
conductor**: a factor of four for an odd prime, and at least a factor of two for the prime two. -/
theorem le_finrank_sup_radicalField_four_prime [NeZero ((2 : ℕ) ^ e)] {p : ℕ}
    (hp : p.Prime) {i : AlgebraicClosure ℚ} (hi : IsPrimitiveRoot i 4)
    (hiA : i ∈ cycSubfield (2 ^ e)) :
    (if p = 2 then 2 else 4) * finrank ℚ ↥(cycSubfield (2 ^ e))
      ≤ finrank ℚ ↥(cycSubfield (2 ^ e) ⊔ radicalField 4 ({((p : ℕ) : ℚ)} : Finset ℚ)) := by
  have hp0 : ((p : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  by_cases h2 : p = 2
  · subst h2
    rw [if_pos rfl]
    exact two_mul_finrank_le_finrank_sup_radicalField_four hi hiA (by norm_num)
      (by simpa using forall_mem_cycSubfield_pow_four_ne_two (e := e))
  · rw [if_neg h2]
    exact four_mul_finrank_le_finrank_sup_radicalField_four hi hiA hp0
      (forall_mem_cycSubfield_sq_ne_of_odd_prime hp h2)

end Cyclotomic

/-! ### The auxiliary prime -/

section AuxPrime

/-- **A prime congruent to one modulo a prescribed power of two modulo which two prescribed primes,
not both two, are both fourth-power non-residues.**  The cyclotomic field of that two-power
conductor is enlarged by a factor four by the fourth root of an odd prime and by a factor at least
two by the fourth root of two, so unless both prescribed primes are two the density bound leaves
infinitely many primes splitting completely in the cyclotomic field but in neither radical field. -/
theorem exists_prime_dvd_sub_one_pow_four_ne_one {e : ℕ} (he : 2 ≤ e) {p₁ p₂ : ℕ} (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (hne : ¬ (p₁ = 2 ∧ p₂ = 2)) (T : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ 2 ^ e ∣ q - 1 ∧
      ((p₁ : ℕ) : ZMod q) ^ ((q - 1) / 4) ≠ 1 ∧ ((p₂ : ℕ) : ZMod q) ^ ((q - 1) / 4) ≠ 1 := by
  classical
  haveI : NeZero ((2 : ℕ) ^ e) := ⟨pow_ne_zero e (by norm_num)⟩
  obtain ⟨i, hi, hiA⟩ := exists_isPrimitiveRoot_four_mem_cycSubfield (e := e) he
  have hn₁ : (if p₁ = 2 then 2 else 4 : ℕ) ≠ 0 := by split <;> norm_num
  have hn₂ : (if p₂ = 2 then 2 else 4 : ℕ) ≠ 0 := by split <;> norm_num
  have hlt : 1 / ((if p₁ = 2 then 2 else 4 : ℕ) : ℝ) + 1 / ((if p₂ = 2 then 2 else 4 : ℕ) : ℝ)
      < 1 := by
    rcases Decidable.em (p₁ = 2) with h1 | h1 <;> rcases Decidable.em (p₂ = 2) with h2 | h2
    · exact absurd ⟨h1, h2⟩ hne
    · rw [if_pos h1, if_neg h2]; norm_num
    · rw [if_neg h1, if_pos h2]; norm_num
    · rw [if_neg h1, if_neg h2]; norm_num
  obtain ⟨q, hqp, hqT, hqA, hq₁, hq₂⟩ :=
    exists_prime_splitsCompletely_not_radicalField₂_of_le_finrank (A := cycSubfield (2 ^ e))
      (ℓ := 4) (m₁ := ((p₁ : ℕ) : ℚ)) (m₂ := ((p₂ : ℕ) : ℚ)) hn₁ hn₂
      (le_finrank_sup_radicalField_four_prime hp₁ hi hiA)
      (le_finrank_sup_radicalField_four_prime hp₂ hi hiA) hlt
      (insert 2 (insert p₁ (insert p₂ T)))
  have hq2 : q ≠ 2 := fun h => hqT (h ▸ Finset.mem_insert_self _ _)
  have hdvd : 2 ^ e ∣ q - 1 := by
    haveI : Fact q.Prime := ⟨hqp⟩
    have hnd : ¬ q ∣ (2 : ℕ) ^ e := fun h =>
      hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow h))
    exact (Nat.modEq_iff_dvd' hqp.one_le).mp
      (modEq_of_splitsCompletely ((2 : ℕ) ^ e) ↥(cycSubfield (2 ^ e)) q hnd hqA).symm
  have h4 : (4 : ℕ) ∣ q - 1 := dvd_trans (by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 he) hdvd
  have hcast : ∀ p : ℕ, ((p : ℤ) : ℚ) = ((p : ℕ) : ℚ) := fun p => by push_cast; ring
  have hqp₁ : ¬ ((q : ℤ) ∣ ((p₁ : ℕ) : ℤ)) := by
    intro h
    rw [Int.natCast_dvd_natCast] at h
    exact hqT (Finset.mem_insert_of_mem (((Nat.prime_dvd_prime_iff_eq hqp hp₁).mp h) ▸
      Finset.mem_insert_self _ _))
  have hqp₂ : ¬ ((q : ℤ) ∣ ((p₂ : ℕ) : ℤ)) := by
    intro h
    rw [Int.natCast_dvd_natCast] at h
    exact hqT (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (((Nat.prime_dvd_prime_iff_eq hqp hp₂).mp h) ▸ Finset.mem_insert_self _ _)))
  refine ⟨q, hqp, fun h => hqT (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem h))), hdvd, fun h => hq₁ ?_, fun h => hq₂ ?_⟩
  · rw [← hcast p₁]
    exact splitsCompletely_radicalField_of_dvd (by norm_num) hqp h4 hqp₁ (by exact_mod_cast h)
  · rw [← hcast p₂]
    exact splitsCompletely_radicalField_of_dvd (by norm_num) hqp h4 hqp₂ (by exact_mod_cast h)

end AuxPrime

end InverseGalois.CFT
