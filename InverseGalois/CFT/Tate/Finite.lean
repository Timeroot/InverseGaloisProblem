/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Basic

/-!
# The Tate groups of a finitely generated module are finite

Both Tate groups of a module over a cyclic group of order `n` are annihilated by `n`.  For `Ĥ⁰`
this is immediate: the norm of a fixed point is its multiple by `n`, so every class is killed by
`n`.  For `Ĥ⁻¹` it comes from the telescoping identity `σ ^ i x - x = (σ - 1) (∑ j < i, σ ^ j x)`,
which exhibits `n • x` as a difference whenever the norm of `x` vanishes.

A finitely generated abelian group annihilated by a nonzero integer is finite, and both Tate groups
of a finitely generated module are finitely generated, being quotients of subgroups of it.  So the
Herbrand quotient of a finitely generated module over a nontrivial cyclic group is defined without
any further hypothesis, and the finiteness assumptions carried by the results on Herbrand quotients
are discharged for every lattice.

## Main results

* `InverseGalois.CFT.normHom_of_fixed`: the norm of a fixed point is its multiple by `n`.
* `InverseGalois.CFT.sigmaSubOne_normHom`: the telescoping identity for the partial norms.
* `InverseGalois.CFT.nsmul_tateH0_eq_zero`, `InverseGalois.CFT.nsmul_tateHm1_eq_zero`: **the order
  of the group annihilates both Tate groups.**
* `InverseGalois.CFT.finite_tateH0`, `InverseGalois.CFT.finite_tateHm1`: **both Tate groups of a
  finitely generated module over a nontrivial cyclic group are finite.**

## Tags

Tate cohomology, Herbrand quotient, finitely generated, lattice
-/

namespace InverseGalois.CFT

variable {A : Type*} [AddCommGroup A] {σ : A ≃+ A} {n : ℕ}

/-! ### The order annihilates the Tate groups -/

/-- A fixed point of an automorphism is fixed by all of its powers. -/
theorem pow_apply_of_fixed {x : A} (hx : σ x = x) (i : ℕ) : (σ ^ i) x = x := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pow_succ_apply, ih, hx]

/-- **The norm of a fixed point is its multiple by the order.** -/
theorem normHom_of_fixed (σ : A ≃+ A) (n : ℕ) {x : A} (hx : σ x = x) :
    normHom σ n x = n • x := by
  rw [normHom_apply]
  rw [Finset.sum_congr rfl fun i _ => pow_apply_of_fixed hx i, Finset.sum_const,
    Finset.card_range]

/-- **The telescoping identity for the partial norms**: the difference operator applied to the sum
of the first `i` translates is the `i`-th translate minus the point. -/
theorem sigmaSubOne_normHom (σ : A ≃+ A) (i : ℕ) (x : A) :
    sigmaSubOne σ (normHom σ i x) = (σ ^ i) x - x := by
  have hshift : ∀ j : ℕ, σ ((σ ^ j) x) = (σ ^ (j + 1)) x := fun j => (pow_succ_apply σ j x).symm
  have h : ∑ j ∈ Finset.range i, (σ ^ (j + 1)) x + x
      = ∑ j ∈ Finset.range i, (σ ^ j) x + (σ ^ i) x := by
    have hsum := Finset.sum_range_succ' (fun j => (σ ^ j) x) i
    rw [Finset.sum_range_succ] at hsum
    simpa using hsum.symm
  rw [sigmaSubOne_apply, normHom_apply, map_sum, Finset.sum_congr rfl fun j _ => hshift j,
    sub_eq_sub_iff_add_eq_add, h, add_comm]

/-- The order of the group annihilates the class of a fixed point. -/
theorem nsmul_mem_range_normHom {x : A} (hx : σ x = x) :
    n • x ∈ (normHom σ n).range :=
  ⟨x, normHom_of_fixed σ n hx⟩

/-- The order of the group carries an element of norm zero into the differences. -/
theorem nsmul_mem_range_sigmaSubOne {x : A} (hx : normHom σ n x = 0) :
    n • x ∈ (sigmaSubOne σ).range := by
  refine ⟨-∑ i ∈ Finset.range n, normHom σ i x, ?_⟩
  rw [map_neg, map_sum, Finset.sum_congr rfl fun i _ => sigmaSubOne_normHom σ i x,
    Finset.sum_sub_distrib, ← normHom_apply, hx, Finset.sum_const, Finset.card_range, zero_sub,
    neg_neg]

variable (σ n)

/-- **The order of the group annihilates `Ĥ⁰`.** -/
theorem nsmul_tateH0_eq_zero (c : tateH0 σ n) : n • c = 0 := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [← QuotientAddGroup.mk'_apply, ← map_nsmul, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  simpa using nsmul_mem_range_normHom ((mem_ker_sigmaSubOne_iff σ x).mp hx)

/-- **The order of the group annihilates `Ĥ⁻¹`.** -/
theorem nsmul_tateHm1_eq_zero (c : tateHm1 σ n) : n • c = 0 := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [← QuotientAddGroup.mk'_apply, ← map_nsmul, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  simpa using nsmul_mem_range_sigmaSubOne hx

/-! ### Finiteness -/

variable [Module.Finite ℤ A]

/-- Both Tate groups are quotients of subgroups of the module, so they are finitely generated. -/
theorem finite_of_nsmul_eq_zero {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] (hn : n ≠ 0)
    (h : ∀ c : M, n • c = 0) : Finite M := by
  refine Module.finite_of_fg_torsion M fun c => ?_
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.2 hn)⟩, ?_⟩
  change (n : ℤ) • c = 0
  rw [natCast_zsmul]
  exact h c

/-- **The Tate group `Ĥ⁰` of a finitely generated module over a nontrivial cyclic group is
finite.** -/
theorem finite_tateH0 (hn : n ≠ 0) : Finite (tateH0 σ n) := by
  haveI : Module.Finite ℤ (sigmaSubOne σ).ker :=
    Module.Finite.of_injective (AddSubgroup.subtype _).toIntLinearMap Subtype.val_injective
  haveI : Module.Finite ℤ (tateH0 σ n) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' _).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  exact finite_of_nsmul_eq_zero n hn (nsmul_tateH0_eq_zero σ n)

/-- **The Tate group `Ĥ⁻¹` of a finitely generated module over a nontrivial cyclic group is
finite.** -/
theorem finite_tateHm1 (hn : n ≠ 0) : Finite (tateHm1 σ n) := by
  haveI : Module.Finite ℤ (normHom σ n).ker :=
    Module.Finite.of_injective (AddSubgroup.subtype _).toIntLinearMap Subtype.val_injective
  haveI : Module.Finite ℤ (tateHm1 σ n) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' _).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  exact finite_of_nsmul_eq_zero n hn (nsmul_tateHm1_eq_zero σ n)

/-- The Tate group `Ĥ⁰` of a lattice is finite. -/
instance instFiniteTateH0 [NeZero n] : Finite (tateH0 σ n) := finite_tateH0 σ n (NeZero.ne n)

/-- The Tate group `Ĥ⁻¹` of a lattice is finite. -/
instance instFiniteTateHm1 [NeZero n] : Finite (tateHm1 σ n) := finite_tateHm1 σ n (NeZero.ne n)

end InverseGalois.CFT
