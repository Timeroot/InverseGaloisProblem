/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Group-theoretic facts for the D₅ Galois computation

Three self-contained finite-group facts used in the D₅ resolvent argument:

* `A5_no_subgroup_order_20`: `A₅` has no subgroup of order 20.
* `perm_fin5_no_order_ten`: the symmetric group on five points has no element of order 10.
* `iso_dihedral_five_of_card_ten`: a non-cyclic group of order 10 is isomorphic to `D₅`.
-/

open scoped Classical

/-!
## Group theory: A₅ has no subgroup of order 20
-/

/-
`A₅` has sixty elements, in the unfolded `{x // sign x = 1}` shape that `simp` produces.
-/
private lemma card_even_perm_fin5 :
    Fintype.card { x : Equiv.Perm (Fin 5) // Equiv.Perm.sign x = 1 } = 60 := by
  have h := two_mul_card_alternatingGroup (α := Fin 5)
  rw [Fintype.card_perm, Fintype.card_fin, show Nat.factorial 5 = 120 from rfl] at h
  have h' : Fintype.card (alternatingGroup (Fin 5)) = 60 := by omega
  rw [← h']
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ ↦ Equiv.Perm.mem_alternatingGroup)

/-
A₅ has no subgroup of order 20 (index 3 in A₅ would give a nontrivial
homomorphism A₅ → S₃, impossible by simplicity since |S₃| < |A₅|).
-/
theorem A5_no_subgroup_order_20 :
    ∀ H : Subgroup (alternatingGroup (Fin 5)), Nat.card H ≠ 20 := by
      -- The homomorphism `A₅ → S₃` by left multiplication on `A₅ ⧸ H`.
      intros H hH
      have h_hom : ∃ f : alternatingGroup (Fin 5) →* Equiv.Perm (alternatingGroup (Fin 5) ⧸ H), f.ker ≠ ⊤ := by
        refine ⟨MulAction.toPermHom (alternatingGroup (Fin 5))
          ((alternatingGroup (Fin 5)) ⧸ H), ?_⟩
        intro h_top
        have h_act : ∀ g : alternatingGroup (Fin 5), ∀ x : alternatingGroup (Fin 5) ⧸ H, g • x = x := by
          simp_all [Subgroup.eq_top_iff']
          intro a ha x
          simpa using congr_arg (fun f ↦ f x) (h_top a ha)
        have h_mem : ∀ g : alternatingGroup (Fin 5), g ∈ H := by
          intro g
          specialize h_act g (QuotientGroup.mk 1)
          simp_all [QuotientGroup.eq]
        have := Subgroup.card_mul_index H
        simp_all [card_even_perm_fin5]
      -- Since `A₅` is simple, the kernel of `f` must be trivial.
      obtain ⟨f, hf⟩ := h_hom
      have h_ker_trivial : f.ker = ⊥ :=
        (inferInstance : (f.ker).Normal).eq_bot_or_eq_top.resolve_right hf
      -- Since `f` is injective, `A₅` is isomorphic to a subgroup of `S₃`.
      have h_le : Nat.card (alternatingGroup (Fin 5)) ≤ Nat.card (Equiv.Perm (alternatingGroup (Fin 5) ⧸ H)) :=
        Nat.card_le_card_of_injective _ ((MonoidHom.ker_eq_bot_iff _).mp h_ker_trivial)
      have h_perm_card : Nat.card (Equiv.Perm (alternatingGroup (Fin 5) ⧸ H)) = Nat.factorial 3 := by
        have h_quot : Nat.card (alternatingGroup (Fin 5) ⧸ H) = 3 := by
          have := Subgroup.card_eq_card_quotient_mul_card_subgroup H
          simp_all
          rw [card_even_perm_fin5] at this
          symm
          linarith
        rw [← h_quot]
        exact Nat.card_perm
      simp_all [Nat.factorial, card_even_perm_fin5]


/-
There is no element of order 10 in the symmetric group on five points
(a permutation of `Fin 5` has order the lcm of its cycle lengths, and no partition
of `5` has lcm `10`).
-/
lemma perm_fin5_no_order_ten (g : Equiv.Perm (Fin 5)) : orderOf g ≠ 10 := by
  simp_all [orderOf_eq_iff]
  revert g
  native_decide

/-
Any non-cyclic finite group of order 10 is isomorphic to the dihedral group `D₅`.

`G` has order `10 = 2·5`; its Sylow 5-subgroup is normal and cyclic of order 5,
and `G` has an involution acting on it.  When `G` is non-cyclic this action is the
inversion automorphism, which is exactly the defining relation of `DihedralGroup 5`.
-/
lemma iso_dihedral_five_of_card_ten {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 10) (hncyc : ¬ IsCyclic G) :
    Nonempty (G ≃* DihedralGroup 5) := by
  have := Fintype.ofFinite G
  simp_all [Nat.card_eq_fintype_card]
  obtain ⟨a, ha⟩ : ∃ a : G, orderOf a = 5 := by
    have := Fact.mk (by decide : Nat.Prime 5)
    apply exists_prime_orderOf_dvd_card 5
    rw [hcard]
    decide
  obtain ⟨b, hb⟩ : ∃ b : G, orderOf b = 2 := by
    apply exists_prime_orderOf_dvd_card 2
    rw [hcard]
    decide
  have h_normal : Subgroup.Normal (Subgroup.zpowers a) := by
    apply Subgroup.normal_of_index_eq_two
    have := Subgroup.index_mul_card (Subgroup.zpowers a)
    simp_all [Fintype.card_zpowers]
    linarith
  have h_conj : b * a * b⁻¹ = a⁻¹ := by
    -- Since `b * a * b⁻¹ ∈ ⟨a⟩`, we have `b * a * b⁻¹ = a ^ k` for some integer `k`.
    obtain ⟨k, hk⟩ : ∃ k : ℤ, b * a * b⁻¹ = a^k :=
      Subgroup.mem_zpowers_iff.mp (h_normal.conj_mem _ (Subgroup.mem_zpowers a) b) |> fun ⟨k, hk⟩ ↦ ⟨k, hk.symm⟩
    have hk_order : k ^ 2 ≡ 1 [ZMOD 5] := by
      have h_bab : a = b^2 * a * b⁻¹^2 := by
        simp [hb ▸ pow_orderOf_eq_one b]
      have h_apow : a = a^(k^2) := by
        convert h_bab using 1
        simp [sq, mul_assoc]
        simp [← mul_assoc, ← hk, zpow_mul]
      have h_asub : a^(k^2 - 1) = 1 := by
        rw [zpow_sub_one]
        norm_num [← h_apow]
      have := orderOf_dvd_iff_zpow_eq_one.mpr h_asub
      norm_num [ha] at this
      refine Int.ModEq.symm (Int.modEq_of_dvd ?_)
      simpa [← Int.natCast_dvd_natCast] using this
    have hk_cases : k ≡ 1 [ZMOD 5] ∨ k ≡ -1 [ZMOD 5] := by
      norm_num [Int.ModEq, Int.mul_emod, sq] at hk_order ⊢
      have := Int.emod_nonneg k (by decide : (5 : ℤ) ≠ 0)
      have := Int.emod_lt_of_pos k (by decide : (5 : ℤ) > 0)
      interval_cases k % 5 <;> trivial
    have hk_neg : k ≡ -1 [ZMOD 5] := by
      by_contra hk_pos
      have h_comm : Commute a b := by
        have hk_one : a^k = a := by
          rw [← Int.emod_add_mul_ediv k 5, hk_cases.resolve_right hk_pos]
          norm_num [zpow_add, zpow_mul, ha]
          norm_cast
          simp [← ha, pow_orderOf_eq_one]
        simp_all [mul_inv_eq_iff_eq_mul]
        exact (commute_iff_eq a b).mpr hk.symm
      have h_cyclic : IsCyclic G := by
        have h_ord : orderOf (a * b) = 10 := by
          rw [h_comm.orderOf_mul_eq_mul_orderOf_of_coprime] <;> simp [*, Nat.coprime_iff_gcd_eq_one]
        have h_gen : ∀ g : G, g ∈ Subgroup.zpowers (a * b) := by
          have h_card_ab : Fintype.card (Subgroup.zpowers (a * b)) = 10 := by
            rw [Fintype.card_zpowers, h_ord]
          have := Subgroup.card_mul_index (Subgroup.zpowers (a * b))
          simp_all
        exact ⟨a * b, h_gen⟩
      contradiction
    rw [hk, ← Int.emod_add_mul_ediv k 5, hk_neg]
    norm_num [zpow_add, zpow_mul]
    simp_all [orderOf_eq_iff]
    simp_all [zpow_ofNat, pow_succ]
    exact eq_inv_of_mul_eq_one_left ha.1 ▸ rfl
  -- Define the homomorphism `φ : D₅ → G` by `φ r = a` and `φ s = b`.
  obtain ⟨ϕ, hϕ⟩ : ∃ ϕ : DihedralGroup 5 →* G, ϕ (DihedralGroup.r 1) = a ∧ ϕ (DihedralGroup.sr 0) = b := by
    refine ⟨MonoidHom.mk' (fun x ↦ match x with
      | DihedralGroup.r i => a ^ i.val | DihedralGroup.sr i => b * a ^ i.val) ?_, ?_, ?_⟩
    all_goals norm_num [pow_succ, mul_assoc, orderOf_eq_iff] at *
    · intro x y
      rcases x with (_ | _) <;> rcases y with (_ | _) <;> simp [*, mul_assoc]
      · rename_i i j
        rw [← pow_add]
        rw [← Nat.mod_add_div (i.val + j.val) 5, pow_add, pow_mul]
        simp_all [pow_succ, mul_assoc]
        fin_cases i <;> fin_cases j <;> rfl
      · rename_i i j
        -- Using the relation `b * a * b⁻¹ = a⁻¹`, we can rewrite `b * a ^ k` as `a⁻¹ ^ k * b`.
        have h_conj_pow : ∀ k : ℕ, b * a ^ k = a⁻¹ ^ k * b := by
          intro k
          induction k <;> simp_all [pow_succ, mul_assoc]
          simp [← mul_assoc, ← h_conj, ‹_›]
        simp_all [← mul_assoc]
        rw [inv_eq_of_mul_eq_one_right]
        simp [← mul_assoc, ← pow_add]
        have hji : (j - i).val + i.val = j.val + 5 * (if j.val < i.val then 1 else 0) := by
          fin_cases i <;> fin_cases j <;> trivial
        rw [hji]
        simp [pow_add]
        intro _
        rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one]
        simp [ha.1]
      · rename_i i j
        rw [← pow_add]
        rw [← Nat.mod_add_div (i.val + j.val) 5]
        simp [pow_add, pow_mul]
        simp_all [show a ^ 5 = 1 by simp_all [pow_succ, mul_assoc]]
        fin_cases i <;> fin_cases j <;> rfl
      · rename_i i j
        -- Using the relation `b * a * b⁻¹ = a⁻¹`, we can simplify the expression.
        have h_conj_all : ∀ i : ℕ, b * a ^ i * b⁻¹ = a⁻¹ ^ i := by
          intro i
          induction i <;> simp_all [pow_succ, mul_assoc]
          simp [← mul_assoc, ← h_conj, ← ‹b * (a ^ _ * b⁻¹) = (a ^ _) ⁻¹›]
        have h_pow : a ^ (j - i).val = a⁻¹ ^ i.val * a ^ j.val := by
          have h_pow5 : a ^ (j - i).val = a ^ (5 - i.val + j.val) := by
            have h_mod : (j - i).val ≡ 5 - i.val + j.val [MOD 5] := by
              fin_cases i <;> fin_cases j <;> trivial
            rw [← Nat.mod_add_div ((j - i).val) 5, ← Nat.mod_add_div (5 - i.val + j.val) 5, h_mod]
            simp [pow_add, pow_mul]
            simp_all [pow_succ, mul_assoc]
          simp_all [pow_add]
          apply eq_inv_of_mul_eq_one_right
          rw [← pow_add, Nat.add_sub_of_le (show i.val ≤ 5 from i.val_lt.le)]
          simp_all [pow_succ, mul_assoc]
        simp_all [← mul_assoc, ← h_conj_all]
        rw [inv_eq_of_mul_eq_one_right hb.1]
    · simp [ZMod.val]
  -- Show that `φ` is surjective.
  have h_surj : Function.Surjective ϕ := by
    have h_dvd_ab : 5 ∣ Fintype.card (Subgroup.zpowers a) ∧ 2 ∣ Fintype.card (Subgroup.zpowers b) := by
      simp [Fintype.card_zpowers, ha, hb]
    have h_dvd : 5 ∣ Fintype.card (Subgroup.closure ({a, b} : Set G)) ∧
        2 ∣ Fintype.card (Subgroup.closure ({a, b} : Set G)) := by
      refine ⟨dvd_trans h_dvd_ab.1 ?_, dvd_trans h_dvd_ab.2 ?_⟩
      · simpa using Subgroup.card_dvd_of_le (show Subgroup.zpowers a ≤ Subgroup.closure { a, b } from
          Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _)))
      · simpa using Subgroup.card_dvd_of_le (show Subgroup.zpowers b ≤ Subgroup.closure { a, b } from
          Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    have h_card10 : Fintype.card (Subgroup.closure ({a, b} : Set G)) = 10 := by
      have := Subgroup.card_subgroup_dvd_card (Subgroup.closure { a, b })
      simp_all
      have := Nat.le_of_dvd (by decide) this
      interval_cases Fintype.card (Subgroup.closure { a, b }) <;> trivial
    have h_top : Subgroup.closure ({a, b} : Set G) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      simp_all [Nat.card_eq_fintype_card]
    intro g
    have hg : g ∈ Subgroup.closure ({a, b} : Set G) := by
      simp_all
    rw [Subgroup.mem_closure] at hg
    have hsub : ({a, b} : Set G) ⊆ ↑ϕ.range := by
      rintro x (rfl | rfl)
      · exact ⟨DihedralGroup.r 1, hϕ.1⟩
      · exact ⟨DihedralGroup.sr 0, hϕ.2⟩
    obtain ⟨x, rfl⟩ := hg ϕ.range hsub
    exact ⟨x, rfl⟩
  -- Since `φ` is surjective and `G` has order 10, `φ` must be injective.
  have h_bij : Function.Bijective ϕ := by
    rw [Fintype.bijective_iff_surjective_and_card]
    refine ⟨h_surj, ?_⟩
    simp [hcard, DihedralGroup.card]
  exact ⟨MulEquiv.symm (MulEquiv.ofBijective ϕ h_bij)⟩