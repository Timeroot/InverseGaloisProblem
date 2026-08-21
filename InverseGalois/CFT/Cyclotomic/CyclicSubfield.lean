import Mathlib

/-!
# Cyclic subfields of prime conductor cyclotomic fields

The Scholz–Reichardt construction of solvable Galois extensions of `ℚ` repeatedly needs an
auxiliary cyclic extension of `ℚ` of a prescribed prime-power degree whose ramification is
controlled by a single large prime.  This file supplies exactly that: for a prime `ℓ` and
naturals `N` and `B` there is a prime `q > B` with `q ≡ 1 [MOD ℓ ^ N]` such that the cyclotomic
field `ℚ(ζ_q)` contains a cyclic extension of `ℚ` of degree `ℓ ^ N`.

The mechanism is the Galois correspondence: for `q` prime the group `Gal(ℚ(ζ_q)/ℚ)` is cyclic of
order `q - 1`, and Dirichlet's theorem on primes in arithmetic progressions produces a prime `q`
with `ℓ ^ N ∣ q - 1`.  A cyclic group has a subgroup of every index dividing its order, and the
fixed field of such a subgroup is the extension we want.

## Main results

* `Subgroup.exists_index_eq_of_isCyclic`: a finite cyclic group has a subgroup of any prescribed
  index dividing its order.
* `IsCyclic.exists_intermediateField_finrank_eq`: for a finite Galois extension `K / k` with cyclic
  Galois group and `d ∣ [K : k]`, there is an intermediate field that is cyclic of degree `d`
  over `k`.
* `isCyclic_gal_cyclotomic_of_prime` and `finrank_cyclotomic_of_prime`: for `q` prime the group
  `Gal(ℚ(ζ_q)/ℚ)` is cyclic and `[ℚ(ζ_q) : ℚ] = q - 1`.
* `Nat.exists_prime_gt_and_pow_dvd_sub_one`: Dirichlet's theorem in the form
  `∃ q > B, q.Prime ∧ q ≡ 1 [MOD m] ∧ m ∣ q - 1`.
* `exists_cyclic_intermediateField_of_prime_conductor` and
  `exists_prime_and_cyclic_intermediateField`: the assembled statement, the second one specialised
  to `K = CyclotomicField q ℚ` so that no field has to be supplied by the caller.
-/

open Module

namespace InverseGalois.CFT

/-! ### The group-theoretic core -/

/-- A finite cyclic group has a subgroup of any index dividing its order. -/
theorem Subgroup.exists_index_eq_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G] {d : ℕ}
    (hd : d ∣ Nat.card G) : ∃ H : Subgroup G, H.index = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  have hpos : 0 < Nat.card G := Nat.card_pos
  obtain ⟨k, hk⟩ := hd
  have hd0 : d ≠ 0 := by rintro rfl; simp [hk] at hpos
  have hk0 : k ≠ 0 := by rintro rfl; simp [hk] at hpos
  refine ⟨_root_.Subgroup.zpowers (g ^ d), ?_⟩
  have hcard : Nat.card (_root_.Subgroup.zpowers (g ^ d)) = k := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hd0 (hord ▸ ⟨k, hk⟩), hord, hk,
      Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hd0)]
  have hmul := (_root_.Subgroup.zpowers (g ^ d)).card_mul_index
  rw [hcard, hk] at hmul
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk0)
    (by rw [hmul, Nat.mul_comm])

/-- Every subgroup of a cyclic group is normal, since a cyclic group is commutative. -/
theorem Subgroup.normal_of_isCyclic {G : Type*} [Group G] [IsCyclic G] (H : Subgroup G) :
    H.Normal :=
  ⟨fun n hn g => by
    rw [IsCyclic.commutative.comm g n, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩

/-! ### The field-theoretic core -/

/-- If `K / k` is a finite Galois extension with cyclic Galois group and `d` divides `[K : k]`,
then `K` contains an intermediate field that is cyclic of degree `d` over `k`. -/
theorem IsCyclic.exists_intermediateField_finrank_eq (k K : Type*) [Field k] [Field K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [IsCyclic Gal(K/k)] {d : ℕ}
    (hd : d ∣ finrank k K) :
    ∃ F : IntermediateField k K, IsGalois k F ∧ IsCyclic Gal(F/k) ∧ finrank k F = d := by
  have hcard : Nat.card Gal(K/k) = finrank k K := IsGalois.card_aut_eq_finrank k K
  obtain ⟨H, hH⟩ := Subgroup.exists_index_eq_of_isCyclic (G := Gal(K/k)) (hcard ▸ hd)
  haveI : H.Normal := Subgroup.normal_of_isCyclic H
  haveI : IsCyclic (Gal(K/k) ⧸ H) :=
    isCyclic_of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  refine ⟨IntermediateField.fixedField H, inferInstance, ?_, ?_⟩
  · exact isCyclic_of_surjective (IsGalois.normalAutEquivQuotient H)
      (IsGalois.normalAutEquivQuotient H).surjective
  · have htower : finrank k (IntermediateField.fixedField H) *
        finrank (IntermediateField.fixedField H) K = finrank k K :=
      finrank_mul_finrank k (IntermediateField.fixedField H) K
    rw [IntermediateField.finrank_fixedField_eq_card H, ← hcard, ← H.card_mul_index, hH,
      Nat.mul_comm (Nat.card H)] at htower
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos htower

/-! ### The cyclotomic input -/

section Cyclotomic

variable (q : ℕ) [hq : Fact q.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {q} ℚ K]

include hq in
/-- For a prime `q`, the Galois group of the `q`-th cyclotomic field over `ℚ` is cyclic. -/
theorem isCyclic_gal_cyclotomic_of_prime : IsCyclic Gal(K/ℚ) := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI := ZMod.isCyclic_units_prime hq.out
  exact isCyclic_of_surjective (IsCyclotomicExtension.Rat.galEquivZMod q K).symm
    (IsCyclotomicExtension.Rat.galEquivZMod q K).symm.surjective

include hq in
/-- For a prime `q`, the `q`-th cyclotomic field has degree `q - 1` over `ℚ`. -/
theorem finrank_cyclotomic_of_prime : finrank ℚ K = q - 1 := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  rw [IsCyclotomicExtension.finrank K
    (Polynomial.cyclotomic.irreducible_rat hq.out.pos), Nat.totient_prime hq.out]

end Cyclotomic

/-! ### The arithmetic input -/

/-- Dirichlet's theorem on primes in arithmetic progressions, in the shape needed below: for a
nonzero modulus `m` and any bound `B` there is a prime `q > B` congruent to `1` modulo `m`, and
then `m` divides `q - 1`. -/
theorem Nat.exists_prime_gt_and_pow_dvd_sub_one {m : ℕ} (hm : m ≠ 0) (B : ℕ) :
    ∃ q : ℕ, B < q ∧ q.Prime ∧ q ≡ 1 [MOD m] ∧ m ∣ q - 1 := by
  obtain ⟨q, hqB, hqp, hq1⟩ := _root_.Nat.forall_exists_prime_gt_and_modEq B hm
    (_root_.Nat.coprime_one_left m)
  exact ⟨q, hqB, hqp, hq1, ((_root_.Nat.modEq_iff_dvd' hqp.one_lt.le).1 hq1.symm)⟩

/-! ### The assembled theorem -/

/-- Let `ℓ` be a prime and `N B : ℕ`.  There is a prime `q > B` with `q ≡ 1 [MOD ℓ ^ N]` such
that any field `K` with `[IsCyclotomicExtension {q} ℚ K]` contains an intermediate field that is
a cyclic extension of `ℚ` of degree `ℓ ^ N`. -/
theorem exists_cyclic_intermediateField_of_prime_conductor.{u} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (N B : ℕ) :
    ∃ q : ℕ, B < q ∧ q.Prime ∧ q ≡ 1 [MOD ℓ ^ N] ∧
      ∀ (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {q} ℚ K],
        ∃ F : IntermediateField ℚ K,
          IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) ∧ finrank ℚ F = ℓ ^ N := by
  obtain ⟨q, hqB, hqp, hq1, hdvd⟩ :=
    Nat.exists_prime_gt_and_pow_dvd_sub_one (pow_ne_zero N hℓ.ne_zero) B
  refine ⟨q, hqB, hqp, hq1, ?_⟩
  intro K _ _ _
  haveI : Fact q.Prime := ⟨hqp⟩
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {q} ℚ K
  haveI : IsCyclic Gal(K/ℚ) := isCyclic_gal_cyclotomic_of_prime q K
  exact IsCyclic.exists_intermediateField_finrank_eq ℚ K
    (by rwa [finrank_cyclotomic_of_prime q K])

/-- Let `ℓ` be a prime and `N B : ℕ`.  There is a prime `q > B` with `q ≡ 1 [MOD ℓ ^ N]` and an
intermediate field `F` of `CyclotomicField q ℚ` over `ℚ` which is a cyclic Galois extension of `ℚ`
of degree `ℓ ^ N`. -/
theorem exists_prime_and_cyclic_intermediateField {ℓ : ℕ} (hℓ : ℓ.Prime) (N B : ℕ) :
    ∃ q : ℕ, B < q ∧ q.Prime ∧ q ≡ 1 [MOD ℓ ^ N] ∧
      ∃ F : IntermediateField ℚ (CyclotomicField q ℚ),
        IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) ∧ finrank ℚ F = ℓ ^ N ∧ NumberField F := by
  obtain ⟨q, hqB, hqp, hq1, hK⟩ :=
    exists_cyclic_intermediateField_of_prime_conductor hℓ N B
  obtain ⟨F, hF1, hF2, hF3⟩ := hK (CyclotomicField q ℚ)
  exact ⟨q, hqB, hqp, hq1, F, hF1, hF2, hF3, inferInstance⟩

end InverseGalois.CFT
