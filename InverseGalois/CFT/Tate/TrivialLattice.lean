/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Commensurable
import InverseGalois.CFT.Tate.Finite
import InverseGalois.CFT.Tate.Pi
import InverseGalois.CFT.Tate.Restrict
import InverseGalois.CFT.Tate.Trivial

/-!
# The Herbrand quotient of a lattice with trivial action

The Herbrand quotient of the integers with a trivial action is `n`, and the quotient of a finite
product is the product of the quotients, so a free lattice of finite rank has quotient `n` raised
to the rank.  Since the quotient only depends on the isomorphism class of a module with an
automorphism, the same holds for any module with a finite basis, and since commensurable lattices
have the same quotient it holds for any subgroup of a free lattice of finite rank containing a
multiple of everything.

Read through the definition of the quotient, this is the classical index computation for a
finitely generated abelian group: the index of the `n`-th multiples, divided by the order of the
`n`-torsion, is `n` raised to the rank.

## Main results

* `InverseGalois.CFT.herbrand_one_pi`: the Herbrand quotient of a finite product of copies of the
  integers with trivial action is `n` raised to the number of factors.
* `InverseGalois.CFT.herbrand_one_of_basis`: **a module with a finite basis has Herbrand quotient
  `n` raised to the size of the basis.**
* `InverseGalois.CFT.herbrand_one_free`: the same, phrased through the rank.
* `InverseGalois.CFT.herbrand_one_addSubgroup_of_nsmul_mem`: **a subgroup of a free lattice of
  finite rank containing a multiple of everything has the Herbrand quotient of the whole lattice.**
* `InverseGalois.CFT.card_tateHm1_one`: for a trivial action the lower Tate group is the
  `n`-torsion.
* `InverseGalois.CFT.card_tateH0_one_additive`: **for a trivial action on a multiplicative group
  the upper Tate group is the quotient by the `n`-th powers.**

## Tags

Tate cohomology, Herbrand quotient, trivial action, lattice, rank
-/

namespace InverseGalois.CFT

/-! ### A finite product of copies of the integers -/

section Pi

variable {ι : Type*} [Fintype ι] (n : ℕ)

omit [Fintype ι] in
/-- A product of trivial actions is trivial. -/
theorem piAut_one : piAut (fun _ : ι => (1 : ℤ ≃+ ℤ)) = 1 :=
  AddEquiv.ext fun _ => funext fun _ => rfl

/-- **The Herbrand quotient of a finite product of copies of the integers with trivial action** is
`n` raised to the number of factors. -/
theorem herbrand_one_pi (hn : n ≠ 0) :
    herbrand (1 : (ι → ℤ) ≃+ (ι → ℤ)) n = (n : ℚ) ^ Fintype.card ι := by
  rw [← piAut_one (ι := ι), herbrand_piAut]
  rw [Finset.prod_congr rfl fun i _ => herbrand_int n hn, Finset.prod_const, Finset.card_univ]

end Pi

/-! ### A module with a finite basis -/

section Basis

variable {ι M : Type*} [Fintype ι] [AddCommGroup M] (n : ℕ)

/-- **A module with a finite basis has Herbrand quotient `n` raised to the size of the basis**,
being isomorphic to a product of copies of the integers. -/
theorem herbrand_one_of_basis (b : Module.Basis ι ℤ M) (hn : n ≠ 0) :
    herbrand (1 : M ≃+ M) n = (n : ℚ) ^ Fintype.card ι := by
  rw [herbrand_congr (σB := 1) b.equivFun.toAddEquiv (fun _ => rfl) n, herbrand_one_pi n hn]

/-- **A free module of finite rank has Herbrand quotient `n` raised to its rank.** -/
theorem herbrand_one_free [Module.Free ℤ M] [Module.Finite ℤ M] (hn : n ≠ 0) :
    herbrand (1 : M ≃+ M) n = (n : ℚ) ^ Module.finrank ℤ M := by
  rw [herbrand_one_of_basis n (Module.Free.chooseBasis ℤ M) hn,
    Module.finrank_eq_card_chooseBasisIndex]

end Basis

/-! ### A subgroup of finite index in a free lattice -/

section Sub

variable {Y : Type*} [Fintype Y] {L : AddSubgroup (Y → ℤ)} (n : ℕ)

/-- **A subgroup of a free lattice of finite rank containing a multiple of everything has the
Herbrand quotient of the whole lattice**, the two being commensurable. -/
theorem herbrand_one_addSubgroup_of_nsmul_mem {N : ℕ} (hN : N ≠ 0)
    (hNL : ∀ x : Y → ℤ, N • x ∈ L) (hn : n ≠ 0) :
    herbrand (1 : L ≃+ L) n = (n : ℚ) ^ Fintype.card Y := by
  haveI : NeZero n := ⟨hn⟩
  have htop : ∀ x ∈ (⊤ : AddSubgroup (Y → ℤ)), (1 : (Y → ℤ) ≃+ (Y → ℤ)) x ∈
      (⊤ : AddSubgroup (Y → ℤ)) := fun _ _ => trivial
  have htop' : ∀ x ∈ (⊤ : AddSubgroup (Y → ℤ)), (1 : (Y → ℤ) ≃+ (Y → ℤ)).symm x ∈
      (⊤ : AddSubgroup (Y → ℤ)) := fun _ _ => trivial
  haveI : Module.Finite ℤ ↥L := module_finite_addSubgroup _
  haveI : Module.Finite ℤ ↥(⊤ : AddSubgroup (Y → ℤ)) := module_finite_addSubgroup _
  haveI : Module.Free ℤ ↥L := module_free_addSubgroup _
  haveI : Module.Free ℤ ↥(⊤ : AddSubgroup (Y → ℤ)) := module_free_addSubgroup _
  have hone : (1 : ↥L ≃+ ↥L) ^ n = 1 := one_pow n
  have hone' : (subgroupAut (1 : (Y → ℤ) ≃+ (Y → ℤ)) ⊤ htop htop') ^ n = 1 :=
    subgroupAut_pow_eq_one _ _ (one_pow n)
  have hcomm : herbrand (1 : ↥L ≃+ ↥L) n
      = herbrand (subgroupAut (1 : (Y → ℤ) ≃+ (Y → ℤ)) ⊤ htop htop') n :=
    herbrand_eq_of_commensurable (σV := (1 : (Y → ℤ) ≃+ (Y → ℤ))) hone hone' (fun _ => rfl)
      (fun _ => rfl) one_ne_zero hN (fun _ _ => trivial) (fun x _ => hNL x)
  rw [hcomm, herbrand_topAut, herbrand_one_pi n hn]

end Sub

/-! ### The lower Tate group of a trivial action -/

section Torsion

variable {A : Type*} [AddCommGroup A] (n : ℕ)

/-- **For a trivial action the lower Tate group is the `n`-torsion**: the differences `σ y - y` all
vanish, so nothing is divided out. -/
theorem card_tateHm1_one :
    Nat.card (tateHm1 (1 : A ≃+ A) n) = Nat.card ↥(normHom (1 : A ≃+ A) n).ker := by
  have hbot : (sigmaSubOne (1 : A ≃+ A)).range.addSubgroupOf (normHom (1 : A ≃+ A) n).ker = ⊥ := by
    rw [sigmaSubOne_one, AddMonoidHom.range_zero, AddSubgroup.bot_addSubgroupOf]
  exact Nat.card_congr ((QuotientAddGroup.quotientAddEquivOfEq hbot).trans
    QuotientAddGroup.quotientBot).toEquiv

end Torsion

/-! ### A multiplicative group -/

section Mul

variable {G : Type*} [CommGroup G] (n : ℕ)

/-- For a trivial action the norms are the `n`-th powers. -/
theorem range_normHom_one_additive :
    (normHom (1 : Additive G ≃+ Additive G) n).range
      = Subgroup.toAddSubgroup (powMonoidHom n : G →* G).range := by
  ext x
  rw [AddMonoidHom.mem_range, Additive.mem_toAddSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y.toMul, ?_⟩
    rw [powMonoidHom_apply, ← toMul_nsmul, normHom_one_apply]
  · rintro ⟨y, hy⟩
    refine ⟨Additive.ofMul y, ?_⟩
    rw [normHom_one_apply, ← ofMul_pow]
    exact congrArg Additive.ofMul ((powMonoidHom_apply n y).symm.trans hy)

/-- For a trivial action the elements of norm zero are the `n`-torsion. -/
theorem ker_normHom_one_additive :
    (normHom (1 : Additive G ≃+ Additive G) n).ker
      = Subgroup.toAddSubgroup (powMonoidHom n : G →* G).ker := by
  ext x
  rw [AddMonoidHom.mem_ker, Additive.mem_toAddSubgroup, MonoidHom.mem_ker, powMonoidHom_apply,
    normHom_one_apply, ← toMul_nsmul]
  exact Iff.rfl

/-- **For a trivial action on a multiplicative group the upper Tate group is the quotient by the
`n`-th powers**, so its order is the index of the subgroup of `n`-th powers. -/
theorem card_tateH0_one_additive :
    Nat.card (tateH0 (1 : Additive G ≃+ Additive G) n)
      = (powMonoidHom n : G →* G).range.index := by
  rw [card_tateH0_trivial, range_normHom_one_additive, Subgroup.index_toAddSubgroup]

/-- **For a trivial action on a multiplicative group the lower Tate group is the `n`-torsion.** -/
theorem card_tateHm1_one_additive :
    Nat.card (tateHm1 (1 : Additive G ≃+ Additive G) n)
      = Nat.card ↥(powMonoidHom n : G →* G).ker := by
  rw [card_tateHm1_one, ker_normHom_one_additive]
  exact Nat.card_congr
    ⟨fun x => ⟨x.1.toMul, x.2⟩, fun x => ⟨Additive.ofMul x.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩

end Mul

end InverseGalois.CFT
