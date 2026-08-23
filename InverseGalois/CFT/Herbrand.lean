import Mathlib

/-!
# The Herbrand quotient of a finite module over a cyclic group

Let `M` be an abelian group equipped with an additive automorphism `σ`, and let `n` be a natural
number with `σ ^ n = 1`, so that `σ` generates a cyclic group of order dividing `n` acting on `M`.
The two basic operators attached to this situation are `x ↦ σ x - x` and the norm
`x ↦ ∑ i < n, σ ^ i x`.  Each kills the image of the other, so one gets two subquotients of `M`,
namely the fixed points modulo the norms and the norm-zero elements modulo the differences.  The
Herbrand theorem says that for finite `M` these two subquotients have the same size; equivalently,
the Herbrand quotient of a finite module is `1`.

This file develops that statement in an action-free formulation, phrased directly in terms of the
kernels and ranges of two additive endomorphisms of `M`.

## Main results

* `sigmaSubOne`, `normHom`: the two operators, as additive monoid homomorphisms `M →+ M`.
* `range_normHom_le_ker_sigmaSubOne`, `range_sigmaSubOne_le_ker_normHom`: the two inclusions
  making the pair of operators into a two-periodic complex.
* `card_ker_mul_card_range`: for finite `M`, the kernel and the range of any endomorphism have
  cardinalities multiplying to `Nat.card M`.
* `card_ker_sigmaSubOne_mul_card_ker_normHom`: the resulting numerical identity.
* `index_eq_index`: the Herbrand theorem, that the two subquotients have equal index, together
  with its explicit quotient form `card_quotient_eq_card_quotient`.
* `norm_surjective_onto_fixed_iff`: the norm hits every fixed point if and only if every element
  of norm zero is a difference `σ y - y`.
-/

namespace InverseGalois.CFT

variable {M : Type*} [AddCommGroup M]

/-- The operator `x ↦ σ x - x` attached to an additive automorphism `σ` of `M`. -/
def sigmaSubOne (σ : M ≃+ M) : M →+ M := (σ : M →+ M) - AddMonoidHom.id M

/-- The defining formula for `sigmaSubOne`. -/
@[simp]
theorem sigmaSubOne_apply (σ : M ≃+ M) (x : M) : sigmaSubOne σ x = σ x - x := rfl

/-- The norm operator `x ↦ ∑ i < n, σ ^ i x` attached to an additive automorphism `σ` of `M`. -/
noncomputable def normHom (σ : M ≃+ M) (n : ℕ) : M →+ M :=
  ∑ i ∈ Finset.range n, ((σ ^ i : M ≃+ M) : M →+ M)

/-- The defining formula for `normHom`. -/
theorem normHom_apply (σ : M ≃+ M) (n : ℕ) (x : M) :
    normHom σ n x = ∑ i ∈ Finset.range n, (σ ^ i) x := by
  simp [normHom, AddMonoidHom.finset_sum_apply]

/-- Applying a successor power of `σ` means applying `σ` last. -/
theorem pow_succ_apply (σ : M ≃+ M) (i : ℕ) (x : M) : (σ ^ (i + 1)) x = σ ((σ ^ i) x) := by
  rw [pow_succ']
  rfl

/-- Applying a successor power of `σ` means applying `σ` first. -/
theorem pow_succ_apply' (σ : M ≃+ M) (i : ℕ) (x : M) : (σ ^ (i + 1)) x = (σ ^ i) (σ x) := by
  rw [pow_succ]
  rfl

/-- The kernel of `sigmaSubOne σ` is the set of points fixed by `σ`. -/
theorem mem_ker_sigmaSubOne_iff (σ : M ≃+ M) (x : M) :
    x ∈ (sigmaSubOne σ).ker ↔ σ x = x := by
  rw [AddMonoidHom.mem_ker, sigmaSubOne_apply, sub_eq_zero]

/-- When `σ ^ n = 1`, shifting the exponent by one does not change a sum of the first `n` powers
of `σ` evaluated at a point: the two sums telescope to the same value. -/
theorem sum_pow_succ_apply (σ : M ≃+ M) {n : ℕ} (hσ : σ ^ n = 1) (x : M) :
    ∑ i ∈ Finset.range n, (σ ^ (i + 1)) x = ∑ i ∈ Finset.range n, (σ ^ i) x := by
  have h := Finset.sum_range_sub (fun i => (σ ^ i) x) n
  rw [Finset.sum_sub_distrib, hσ] at h
  simpa [sub_eq_zero] using h

/-- Norms are fixed by `σ`, when `σ ^ n = 1`. -/
theorem range_normHom_le_ker_sigmaSubOne (σ : M ≃+ M) {n : ℕ} (hσ : σ ^ n = 1) :
    (normHom σ n).range ≤ (sigmaSubOne σ).ker := by
  rintro _ ⟨x, rfl⟩
  rw [mem_ker_sigmaSubOne_iff, normHom_apply, map_sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => (pow_succ_apply σ i x).symm) ?_
  exact sum_pow_succ_apply σ hσ x

/-- Differences `σ x - x` have norm zero, when `σ ^ n = 1`. -/
theorem range_sigmaSubOne_le_ker_normHom (σ : M ≃+ M) {n : ℕ} (hσ : σ ^ n = 1) :
    (sigmaSubOne σ).range ≤ (normHom σ n).ker := by
  rintro _ ⟨x, rfl⟩
  rw [AddMonoidHom.mem_ker, sigmaSubOne_apply, normHom_apply]
  have h : ∀ i ∈ Finset.range n, (σ ^ i) (σ x - x) = (σ ^ (i + 1)) x - (σ ^ i) x := by
    intro i _
    rw [map_sub, pow_succ_apply']
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, sum_pow_succ_apply σ hσ, sub_self]

/-- The first isomorphism theorem in counting form: for a finite abelian group `M`, the kernel and
the range of an endomorphism have cardinalities whose product is `Nat.card M`. -/
theorem card_ker_mul_card_range (f : M →+ M) [Finite M] :
    Nat.card f.ker * Nat.card f.range = Nat.card M := by
  have h : Nat.card f.range = Nat.card (M ⧸ f.ker) :=
    (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv).symm
  rw [h, ← AddSubgroup.index_eq_card, AddSubgroup.card_mul_index]

/-- Viewing a subgroup inside a larger subgroup containing it does not change its cardinality. -/
theorem card_addSubgroupOf_of_le {H K : AddSubgroup M} (h : H ≤ K) :
    Nat.card (H.addSubgroupOf K) = Nat.card H :=
  Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe h).toEquiv

/-- The counting identity for the operator `x ↦ σ x - x`. -/
theorem card_ker_mul_card_range_sigmaSubOne (σ : M ≃+ M) [Finite M] :
    Nat.card (sigmaSubOne σ).ker * Nat.card (sigmaSubOne σ).range = Nat.card M :=
  card_ker_mul_card_range _

/-- The counting identity for the norm operator. -/
theorem card_ker_mul_card_range_normHom (σ : M ≃+ M) (n : ℕ) [Finite M] :
    Nat.card (normHom σ n).ker * Nat.card (normHom σ n).range = Nat.card M :=
  card_ker_mul_card_range _

/-- The numerical form of the Herbrand theorem: for a finite module, the two kernel-times-range
products agree, both being the cardinality of the module. -/
theorem card_ker_sigmaSubOne_mul_card_ker_normHom (σ : M ≃+ M) (n : ℕ) [Finite M] :
    Nat.card (sigmaSubOne σ).ker * Nat.card (sigmaSubOne σ).range
      = Nat.card (normHom σ n).ker * Nat.card (normHom σ n).range :=
  (card_ker_mul_card_range_sigmaSubOne σ).trans (card_ker_mul_card_range_normHom σ n).symm

/-- The Herbrand theorem: for a finite module over the cyclic group generated by `σ`, the index of
the norms inside the fixed points equals the index of the differences inside the norm-zero
elements.  Equivalently, the Herbrand quotient of a finite module is trivial. -/
theorem index_eq_index (σ : M ≃+ M) {n : ℕ} (hσ : σ ^ n = 1) [Finite M] :
    ((normHom σ n).range.addSubgroupOf (sigmaSubOne σ).ker).index
      = ((sigmaSubOne σ).range.addSubgroupOf (normHom σ n).ker).index := by
  have h1 := AddSubgroup.card_mul_index ((normHom σ n).range.addSubgroupOf (sigmaSubOne σ).ker)
  have h2 := AddSubgroup.card_mul_index ((sigmaSubOne σ).range.addSubgroupOf (normHom σ n).ker)
  rw [card_addSubgroupOf_of_le (range_normHom_le_ker_sigmaSubOne σ hσ)] at h1
  rw [card_addSubgroupOf_of_le (range_sigmaSubOne_le_ker_normHom σ hσ)] at h2
  have key : Nat.card (normHom σ n).range * Nat.card (sigmaSubOne σ).range *
      ((normHom σ n).range.addSubgroupOf (sigmaSubOne σ).ker).index
      = Nat.card (normHom σ n).range * Nat.card (sigmaSubOne σ).range *
        ((sigmaSubOne σ).range.addSubgroupOf (normHom σ n).ker).index := by
    calc Nat.card (normHom σ n).range * Nat.card (sigmaSubOne σ).range *
          ((normHom σ n).range.addSubgroupOf (sigmaSubOne σ).ker).index
        = Nat.card (sigmaSubOne σ).ker * Nat.card (sigmaSubOne σ).range := by
          rw [← h1]; ring
      _ = Nat.card (normHom σ n).ker * Nat.card (normHom σ n).range :=
          card_ker_sigmaSubOne_mul_card_ker_normHom σ n
      _ = Nat.card (normHom σ n).range * Nat.card (sigmaSubOne σ).range *
            ((sigmaSubOne σ).range.addSubgroupOf (normHom σ n).ker).index := by
          rw [← h2]; ring
  have hpos : 0 < Nat.card (normHom σ n).range * Nat.card (sigmaSubOne σ).range :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos key

/-- The Herbrand theorem in explicit quotient form: the fixed points modulo the norms and the
norm-zero elements modulo the differences are finite groups of the same size. -/
theorem card_quotient_eq_card_quotient (σ : M ≃+ M) {n : ℕ} (hσ : σ ^ n = 1) [Finite M] :
    Nat.card ((sigmaSubOne σ).ker ⧸ (normHom σ n).range.addSubgroupOf (sigmaSubOne σ).ker)
      = Nat.card ((normHom σ n).ker ⧸ (sigmaSubOne σ).range.addSubgroupOf (normHom σ n).ker) := by
  rw [← AddSubgroup.index_eq_card, ← AddSubgroup.index_eq_card, index_eq_index σ hσ]

/-- For a finite module over the cyclic group generated by `σ`, the norm is surjective onto the
fixed points if and only if every element of norm zero is a difference `σ y - y`: the vanishing of
one of the two subquotients forces the vanishing of the other. -/
theorem norm_surjective_onto_fixed_iff (σ : M ≃+ M) {n : ℕ} (hσ : σ ^ n = 1) [Finite M] :
    (∀ x, σ x = x → ∃ y, normHom σ n y = x) ↔ ∀ x, normHom σ n x = 0 → ∃ y, x = σ y - y := by
  have e1 : ((normHom σ n).range.addSubgroupOf (sigmaSubOne σ).ker).index = 1 ↔
      (sigmaSubOne σ).ker ≤ (normHom σ n).range := AddSubgroup.relIndex_eq_one
  have e2 : ((sigmaSubOne σ).range.addSubgroupOf (normHom σ n).ker).index = 1 ↔
      (normHom σ n).ker ≤ (sigmaSubOne σ).range := AddSubgroup.relIndex_eq_one
  have h1 : (∀ x, σ x = x → ∃ y, normHom σ n y = x) ↔
      (sigmaSubOne σ).ker ≤ (normHom σ n).range := by
    constructor
    · intro h x hx
      exact h x ((mem_ker_sigmaSubOne_iff σ x).mp hx)
    · intro h x hx
      exact h ((mem_ker_sigmaSubOne_iff σ x).mpr hx)
  have h2 : (∀ x, normHom σ n x = 0 → ∃ y, x = σ y - y) ↔
      (normHom σ n).ker ≤ (sigmaSubOne σ).range := by
    constructor
    · intro h x hx
      obtain ⟨y, hy⟩ := h x hx
      exact ⟨y, hy.symm⟩
    · intro h x hx
      obtain ⟨y, hy⟩ := h hx
      exact ⟨y, hy.symm⟩
  rw [h1, h2, ← e1, ← e2, index_eq_index σ hσ]

end InverseGalois.CFT
