/-
# Helper lemmas for the resolvent theory proof

This file provides group-theoretic lemmas needed for `card_gal_dvd_20_of_resolvent_root`.
-/
import Mathlib

set_option maxHeartbeats 1600000

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-!
## Group theory: S₅ has no subgroups of order 15, 30, or 40
-/

/-- No element of Perm(Fin 5) has order 15. -/
private lemma no_order_15_in_S5 : ∀ g : Equiv.Perm (Fin 5), orderOf g ≠ 15 := by
  intro g hg
  rw [orderOf_eq_iff] at hg
  · revert g
    native_decide
  · simp

/-
S₅ has no subgroup of order 15. A group of order 15 is cyclic (by Sylow theory),
    so it has an element of order 15, but no such element exists in S₅.
-/
theorem Perm_Fin5_no_subgroup_order_15 :
    ∀ H : Subgroup (Equiv.Perm (Fin 5)), Nat.card H ≠ 15 := by
  -- Assume H is a subgroup of S₅ with order 15. We need to show that this leads to a contradiction.
  intro H h_card
  obtain ⟨g, hg⟩ : ∃ g : H, orderOf g = 15 := by
    -- Since the cardinality of `H` is 15, which is `3 × 5`, by Sylow's theorems, `H` must have elements of order 3 and 5.
    obtain ⟨g3, hg3⟩ : ∃ g3 : H, orderOf g3 = 3 := by
      have : Fintype H := Fintype.ofFinite _
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      apply exists_prime_orderOf_dvd_card 3
      rw [Fintype.card_eq_nat_card, h_card]
      decide
    obtain ⟨g5, hg5⟩ : ∃ g5 : H, orderOf g5 = 5 := by
      have P : Sylow 5 H := Nonempty.some inferInstance
      have hP_card : Nat.card P = 5 := by
        rw [P.card_eq_multiplicity, h_card]
        native_decide
      obtain ⟨g, hg⟩ := (isCyclic_of_prime_card hP_card).exists_generator
      use g
      simpa [orderOf_eq_card_of_forall_mem_zpowers hg]
    -- Since `g3` and `g5` commute and their orders are coprime, their product `g3 * g5` has order `3 * 5 = 15`.
    have h_comm : g3 * g5 = g5 * g3 := by
      have h_comm : Subgroup.Normal (Subgroup.zpowers g3) ∧ Subgroup.Normal (Subgroup.zpowers g5) := by
        have h_sylow {p} (hp : Nat.Prime p) (hp_div : p ∣ Nat.card H) :
            Nat.card (Sylow p H) = 1 := by
          have _ := Fact.mk hp
          have h_sylow_1 : Nat.card (Sylow p H) ≡ 1 [MOD p] := card_sylow_modEq_one p ↥H
          have h_sylow_div : Nat.card (Sylow p H) ∣ Nat.card H := by
            rw [(Classical.arbitrary (Sylow p ↥H)).card_eq_card_quotient_normalizer]
            exact Subgroup.card_quotient_dvd_card _
          rcases p with (_ | _ | _ | _ | _ | _ | p) <;> simp_all +decide [Nat.ModEq]
          · have := Nat.le_of_dvd (by decide) h_sylow_div
            interval_cases Fintype.card (Sylow 3 H) <;> trivial
          · have := Nat.le_of_dvd (by decide) h_sylow_div
            interval_cases Fintype.card (Sylow 5 H) <;> trivial
          · have := Nat.le_of_dvd (by decide) hp_div
            interval_cases _ : p + 6 <;> simp_all +decide
        have h_sylow_normal : ∀ p : ℕ, Nat.Prime p → p ∣ Nat.card H →
            ∀ P : Sylow p H, Subgroup.Normal (P.toSubgroup) := by
          intros p hp hp_div P
          have h_unique : ∀ Q : Sylow p H, Q = P := by
            have := h_sylow hp hp_div
            rw [Nat.card_eq_one_iff_unique] at this
            exact fun Q ↦ this.1.elim Q P
          constructor
          intro n hn g
          exact h_unique (g • P) ▸ Subgroup.mem_map_of_mem _ hn
        have h_sylow_g3 : ∃ P : Sylow 3 H, Subgroup.zpowers g3 = P.toSubgroup := by
          have h_sylow_g3 : IsPGroup 3 (Subgroup.zpowers g3) := by
            intro x
            use 1
            obtain ⟨k, hk⟩ := x.2
            simp_all [← hg3]
            rw [← Subtype.coe_inj]
            simp [← hk]
          obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow h_sylow_g3
          have hP_card : Nat.card (Subgroup.zpowers g3) = Nat.card P.toSubgroup := by
            have := P.card_eq_multiplicity
            simp_all [Nat.Prime.dvd_iff_one_le_factorization]
            native_decide +revert
          use P
          exact SetLike.ext' (Set.eq_of_subset_of_ncard_le hP hP_card.ge)
        have h_sylow_g5 : ∃ P : Sylow 5 H, Subgroup.zpowers g5 = P.toSubgroup := by
          have h_sylow_g5 : IsPGroup 5 (Subgroup.zpowers g5) := by
            intro x
            use 1
            rcases x with ⟨x, hx⟩
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
            simp [← hg5]
          obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow h_sylow_g5
          have hP_card : Nat.card (Subgroup.zpowers g5) = Nat.card P.toSubgroup := by
            have hP_card : Nat.card P.toSubgroup = 5 := by
              convert P.card_eq_multiplicity
              rw [h_card]
              native_decide
            simp_all [Nat.card_eq_fintype_card]
          use P
          exact SetLike.ext' (Set.eq_of_subset_of_ncard_le hP hP_card.ge)
        constructor
        · obtain ⟨P, hP⟩ := h_sylow_g3
          have h3 : (3 : ℕ) ∣ Nat.card H := by
            rw [h_card]
            decide
          rw [hP]
          exact h_sylow_normal 3 Nat.prime_three h3 P
        · obtain ⟨P, hP⟩ := h_sylow_g5
          have h5 : (5 : ℕ) ∣ Nat.card H := by
            rw [h_card]
            decide
          rw [hP]
          exact h_sylow_normal 5 (by decide) h5 P
      have h_comm : g3 * g5 * g3⁻¹ * g5⁻¹ ∈ Subgroup.zpowers g3 ⊓ Subgroup.zpowers g5 := by
        constructor
        · have := h_comm.1.conj_mem _ (Subgroup.mem_zpowers g3) g5
          obtain ⟨k, hk⟩ := this
          use 1 - k
          simp_all [zpow_sub, mul_assoc]
        · have := h_comm.2.conj_mem _ (Subgroup.mem_zpowers g5) g3
          exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ (Subgroup.mem_zpowers g5))
      have h_comm : Subgroup.zpowers g3 ⊓ Subgroup.zpowers g5 = ⊥ := by
        have h_comm : Nat.card (Subgroup.zpowers g3) = 3 ∧ Nat.card (Subgroup.zpowers g5) = 5 := by
          simp [hg3, hg5]
        have h_comm : Nat.card (↥(Subgroup.zpowers g3 ⊓ Subgroup.zpowers g5)) ∣ Nat.gcd 3 5 := by
          have hle3 : Subgroup.zpowers g3 ⊓ Subgroup.zpowers g5 ≤ Subgroup.zpowers g3 := inf_le_left
          have hle5 : Subgroup.zpowers g3 ⊓ Subgroup.zpowers g5 ≤ Subgroup.zpowers g5 := inf_le_right
          apply Nat.dvd_gcd
          · simpa [h_comm] using Subgroup.card_dvd_of_le hle3
          · simpa [h_comm] using Subgroup.card_dvd_of_le hle5
        simp_all [Subgroup.eq_bot_iff_card]
      simp_all [mul_inv_eq_iff_eq_mul]
    use g3 * g5
    have h_order : ∀ {a b : H}, a * b = b * a →
        Nat.gcd (orderOf a) (orderOf b) = 1 → orderOf (a * b) = orderOf a * orderOf b :=
      Commute.orderOf_mul_eq_mul_orderOf_of_coprime
    rw [h_order h_comm] <;> norm_num [hg3, hg5]
  refine no_order_15_in_S5 g ?_
  simpa [orderOf_eq_iff] using hg

/-
Every normal subgroup of S₅ has order 1, 60, or 120.
    Proof: If N is normal in S₅, then N ∩ A₅ is normal in A₅.
    Since A₅ is simple, N ∩ A₅ = {1} or A₅.
    If A₅ ≤ N: N = A₅ (|N|=60) or N = S₅ (|N|=120).
    If N ∩ A₅ = {1}: |N| ≤ 2 (since [S₅:A₅]=2). If |N|=2, N has a central
    element of order 2, but center(S₅) = {1}. So |N|=1.
-/
lemma normal_subgroup_Perm_Fin5_trichotomy
    (N : Subgroup (Equiv.Perm (Fin 5))) (hN : N.Normal) :
    Nat.card N = 1 ∨ Nat.card N = 60 ∨ Nat.card N = 120 := by
  -- Consider the intersection of `N` with `A₅`.
  set M := N ⊓ alternatingGroup (Fin 5) with hM_def
  have hM_simple : M = ⊥ ∨ M = alternatingGroup (Fin 5) := by
    have hM_simple : ∀ H : Subgroup (alternatingGroup (Fin 5)), H.Normal → H = ⊥ ∨ H = ⊤ :=
      fun H a ↦ Subgroup.Normal.eq_bot_or_eq_top a
    convert hM_simple (M.subgroupOf (alternatingGroup (Fin 5))) _ using 1
    · simp [Subgroup.eq_bot_iff_forall]
      exact ⟨fun h x hx hx' ↦ h x hx', fun h x hx ↦ h x hx.2 hx⟩
    · simp [Subgroup.eq_top_iff']
      exact ⟨fun h a ha ↦ h.symm ▸ ha, fun h ↦ le_antisymm (inf_le_right) fun a ha ↦ h a ha⟩
    · infer_instance
  cases' hM_simple with h h
  · -- If `M` is trivial, then `N` has at most two elements.
    have hN_le_two : N ≤ Subgroup.center (Equiv.Perm (Fin 5)) := by
      intro g hg
      have h_comm : ∀ h : Equiv.Perm (Fin 5), h * g * h⁻¹ * g⁻¹ ∈ M := by
        intro h
        have h_comm : h * g * h⁻¹ * g⁻¹ ∈ N :=
          N.mul_mem (hN.conj_mem _ hg h) (N.inv_mem hg)
        cases Int.units_eq_one_or (Equiv.Perm.sign g) <;>
          cases Int.units_eq_one_or (Equiv.Perm.sign h) <;> simp_all [mul_assoc]
      simp_all [Subgroup.mem_center_iff]
      intro h
      replace hM_def := SetLike.ext_iff.mp hM_def (h * g * h⁻¹ * g⁻¹)
      simp_all [mul_inv_eq_iff_eq_mul]
    have hN_card : Nat.card N ≤ 2 := by
      refine le_trans (Subgroup.card_le_of_le hN_le_two) ?_
      rw [Nat.card_eq_fintype_card]
      native_decide
    have hN_card_cases : Nat.card N = 1 ∨ Nat.card N = 2 := by
      interval_cases _ : Nat.card N <;> simp_all +decide only [Nat.card_eq_zero]
      exact absurd (‹IsEmpty ↥N ∨ Infinite ↥N›.resolve_left (not_isEmpty_iff.mpr ⟨1, N.one_mem⟩))
        (not_infinite_iff_finite.mpr (Set.Finite.to_subtype (Set.toFinite _)))
    cases' hN_card_cases with h h
    · aesop
    · have hN_center : ∀ g : Equiv.Perm (Fin 5), g ∈ N → g = 1 := by
        have hN_center : ∀ g : Equiv.Perm (Fin 5), g ∈ Subgroup.center (Equiv.Perm (Fin 5)) → g = 1 := by
          native_decide +revert
        exact fun g hg ↦ hN_center g <| hN_le_two hg
      refine absurd h ?_
      rw [show N = ⊥ from eq_bot_iff.mpr hN_center]
      simp
  · -- If `M = A₅`, then `N` contains `A₅` and thus has index 1 or 2 in `S₅`.
    have hN_index : N.index = 1 ∨ N.index = 2 := by
      have hN_index : N.index ∣ 2 := by
        have hN_index : N.index ∣ (alternatingGroup (Fin 5)).index :=
          Subgroup.index_dvd_of_le (h ▸ inf_le_left)
        convert hN_index using 1
        simp
      rwa [Nat.dvd_prime Nat.prime_two] at hN_index
    have := Subgroup.index_mul_card N
    simp_all +decide
    cases hN_index <;> simp_all +decide [Fintype.card_perm]
    exact Or.inr <| Or.inl <| by
      norm_num [Nat.factorial] at this
      linarith

/-
S₅ has no subgroup of order 30.
    Proof by coset action: If |H| = 30, then [S₅:H] = 4. The left-multiplication
    action on S₅/H gives φ : S₅ → S₄. The kernel ker(φ) is normal in S₅ and
    contained in H. By the trichotomy of normal subgroups of S₅ (orders 1, 60, 120),
    ker(φ) must have order 1 (since |ker(φ)| ≤ |H| = 30). But then φ is injective,
    giving |S₅| = 120 ≤ |S₄| = 24, contradiction.
-/
theorem Perm_Fin5_no_subgroup_order_30 :
    ∀ H : Subgroup (Equiv.Perm (Fin 5)), Nat.card H ≠ 30 := by
  intro H hH_card
  have h_index : H.index = 4 := by
    have := Subgroup.index_mul_card H
    simp_all [Fintype.card_perm]
    exact mul_right_cancel₀ (by decide) this
  -- The action of `S₅` on the left cosets of `H` gives a homomorphism `φ : S₅ → S₄`.
  obtain ⟨ϕ, hϕ⟩ : ∃ ϕ : Equiv.Perm (Fin 5) →* Equiv.Perm (Equiv.Perm (Fin 5) ⧸ H), ϕ.ker ≤ H := by
    refine ⟨MulAction.toPermHom (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 5) ⧸ H), ?_⟩
    intro x hx
    simp_all [MonoidHom.mem_ker, Equiv.Perm.ext_iff]
    specialize hx (QuotientGroup.mk 1)
    simp_all [QuotientGroup.eq]
  -- Since `|S₅| = 120` and `|S₄| = 24`, the kernel of `φ` must be non-trivial.
  have h_kernel_nontrivial : Nat.card (ϕ.ker) ≠ 1 := by
    intro h_card_ker_one
    have h_inj : Function.Injective ϕ := by
      rw [Nat.card_eq_one_iff_unique] at h_card_ker_one
      exact (MonoidHom.ker_eq_bot_iff _).mp (eq_bot_iff.mpr fun x hx ↦ by
        have := h_card_ker_one.1.elim ⟨x, hx⟩ ⟨1, by simp⟩
        aesop)
    have h_card : Nat.card (Equiv.Perm (Equiv.Perm (Fin 5) ⧸ H)) = 24 := by
      simp_all [Subgroup.index]
      have h_card : Nat.card (Equiv.Perm (Equiv.Perm (Fin 5) ⧸ H)) =
          Nat.factorial (Nat.card (Equiv.Perm (Fin 5) ⧸ H)) := Nat.card_perm
      exact h_card.trans (h_index.symm ▸ rfl)
    have h_card : Nat.card (Equiv.Perm (Fin 5)) ≤ Nat.card (Equiv.Perm (Equiv.Perm (Fin 5) ⧸ H)) :=
      Nat.card_le_card_of_injective _ h_inj
    simp_all +decide [Fintype.card_perm]
  -- Since ϕ.ker is a normal subgroup of S₅ and is contained in H, and H has order 30, ϕ.ker must have order 1, 60, or 120.
  have h_kernel_order : Nat.card (ϕ.ker) = 1 ∨ Nat.card (ϕ.ker) = 60 ∨ Nat.card (ϕ.ker) = 120 := by
    apply normal_subgroup_Perm_Fin5_trichotomy
    infer_instance
  rcases h_kernel_order with h | h | h <;> have := Subgroup.card_dvd_of_le hϕ <;> simp_all

/-
S₅ has no subgroup of order 40. By Sylow, the Sylow 5-subgroup is normal (n₅ = 1),
    so H ≤ N_{S₅}(P₅) which has order 20 < 40. Contradiction.
-/
theorem Perm_Fin5_no_subgroup_order_40 :
    ∀ H : Subgroup (Equiv.Perm (Fin 5)), Nat.card H ≠ 40 := by
  intro H hH_card
  have h_p : ∃ P : Sylow 5 (Equiv.Perm (Fin 5)), P.toSubgroup ≤ H := by
    have h_sylow : ∃ P : Subgroup (Equiv.Perm (Fin 5)), P ≤ H ∧ IsPGroup 5 P ∧ Nat.card P = 5 := by
      have h_sylow : ∃ P : Subgroup (Equiv.Perm (Fin 5)), P ≤ H ∧ Nat.card P = 5 := by
        obtain ⟨g, hg⟩ : ∃ g : H, orderOf g = 5 := by
          have h_cauchy : ∀ {p : ℕ}, Nat.Prime p → p ∣ Nat.card H → ∃ g : H, orderOf g = p := by
            intro p pp dp
            have := Fact.mk pp
            exact exists_prime_orderOf_dvd_card' p dp
          refine h_cauchy (by decide) ?_
          rw [hH_card]
          decide
        use Subgroup.zpowers (g : Equiv.Perm (Fin 5))
        simp_all
        rw [Fintype.card_zpowers]
        aesop
      obtain ⟨P, hP₁, hP₂⟩ := h_sylow
      use P
      simp_all [IsPGroup.iff_card]
      exists 1
    obtain ⟨P, hP₁, hP₂, hP₃⟩ := h_sylow
    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hP₂
    have hP_eq_Q : P = Q.toSubgroup := by
      have hcard : Nat.card P = Nat.card Q.toSubgroup := by
        convert hP₃ using 1
        convert Q.card_eq_multiplicity
        rw [Nat.card_eq_fintype_card]
        native_decide
      exact SetLike.ext' (Set.eq_of_subset_of_ncard_le hQ hcard.ge)
    aesop
  obtain ⟨P, hP⟩ := h_p
  have h_n5_bound : (Nat.card (Sylow 5 (Equiv.Perm (Fin 5)))) = 6 := by
    have h_card_sylow : (Nat.card (Sylow 5 (Equiv.Perm (Fin 5)))) ∣ 24 := by
      have h_card_sylow : (Nat.card (Sylow 5 (Equiv.Perm (Fin 5)))) =
          Nat.card (Equiv.Perm (Fin 5) ⧸ Subgroup.normalizer (P.toSubgroup)) := by
        convert Nat.card_congr (Sylow.equivQuotientNormalizer P) using 1
      have h_card_sylow : (Nat.card (P.toSubgroup)) = 5 := by
        convert P.card_eq_multiplicity using 1
        rw [Nat.card_eq_fintype_card]
        native_decide
      have h_card_sylow : (Nat.card (Equiv.Perm (Fin 5) ⧸ Subgroup.normalizer (P.toSubgroup))) ∣
          (Nat.card (Equiv.Perm (Fin 5) ⧸ P.toSubgroup)) := by
        have hle : P.toSubgroup ≤ Subgroup.normalizer P.toSubgroup := Subgroup.le_normalizer
        exact Subgroup.index_dvd_of_le hle
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup (P.toSubgroup)
      simp_all [Nat.card_eq_fintype_card]
      have hq24 : Nat.card (Equiv.Perm (Fin 5) ⧸ (P : Subgroup (Equiv.Perm (Fin 5)))) = 24 := by
        rw [show Fintype.card (Equiv.Perm (Fin 5)) = 120 by native_decide] at this
        linarith
      rw [← hq24]
      exact h_card_sylow
    have h_card_sylow_mod : (Nat.card (Sylow 5 (Equiv.Perm (Fin 5)))) ≡ 1 [MOD 5] :=
      card_sylow_modEq_one 5 (Equiv.Perm (Fin 5))
    have h_card_sylow_ne_one : (Nat.card (Sylow 5 (Equiv.Perm (Fin 5)))) ≠ 1 := by
      intro h_card_sylow_one
      have h_normal : P.toSubgroup.Normal := by
        have h_unique : ∀ Q : Sylow 5 (Equiv.Perm (Fin 5)), Q = P := by
          rw [Nat.card_eq_one_iff_unique] at h_card_sylow_one
          exact fun Q ↦ h_card_sylow_one.1.elim Q P
        constructor
        intro n hn g
        specialize h_unique (g • P)
        simp_all [Sylow.smul_eq_iff_mem_normalizer]
        exact h_unique n |>.1 hn
      -- Since P is normal in S₅, it must be the case that P contains all 5-cycles in S₅.
      have h_all_5cycles : ∀ g : Equiv.Perm (Fin 5), orderOf g = 5 → g ∈ P.toSubgroup := by
        intro g hg_order
        have h_conj : ∃ h : Equiv.Perm (Fin 5), h * g * h⁻¹ ∈ P.toSubgroup := by
          have h_conj : ∀ g : Equiv.Perm (Fin 5), orderOf g = 5 →
              ∃ Q : Sylow 5 (Equiv.Perm (Fin 5)), g ∈ Q.toSubgroup := by
            intro g hg_order
            have h_conj : ∃ Q : Subgroup (Equiv.Perm (Fin 5)), IsPGroup 5 Q ∧ g ∈ Q := by
              use Subgroup.zpowers g
              simp [IsPGroup]
              intro m
              use 1
              simp [← hg_order]
              simp [Subtype.ext_iff]
            obtain ⟨Q, hQ_pgroup, hQ_g⟩ := h_conj
            obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hQ_pgroup
            exact ⟨Q, hQ hQ_g⟩
          obtain ⟨Q, hQ⟩ := h_conj g hg_order
          have := Subgroup.card_mul_index Q.toSubgroup
          simp_all
          rw [Fintype.card_eq_one_iff] at h_card_sylow_one
          aesop
        obtain ⟨h, hh⟩ := h_conj
        have := h_normal.conj_mem _ hh h⁻¹
        simp_all [mul_assoc]
      have h_card_P_ge : Nat.card P.toSubgroup ≥ 24 := by
        have h_5cyc : Nat.card {g : Equiv.Perm (Fin 5) | orderOf g = 5} ≥ 24 := by
          simp +decide only [orderOf_eq_iff]
          rw [Nat.card_eq_fintype_card]
          native_decide
        exact h_5cyc.trans (Set.ncard_le_ncard h_all_5cycles)
      have h_card_P : Nat.card P.toSubgroup = 5 := by
        convert P.card_eq_multiplicity
        rw [Nat.card_eq_fintype_card]
        native_decide
      linarith!
    have := Nat.le_of_dvd (by decide) h_card_sylow
    interval_cases Nat.card (Sylow 5 (Equiv.Perm (Fin 5))) <;> trivial
  -- Now, show |N_{S₅}(P₅)| = 20
  have h_normalizer_card : Nat.card (Subgroup.normalizer P.toSubgroup) = 120 / 6 := by
    have := Sylow.card_eq_index_normalizer P
    simp_all [Nat.card_eq_fintype_card]
    have := Subgroup.index_mul_card (Subgroup.normalizer (P : Subgroup (Equiv.Perm (Fin 5))))
    simp_all [Nat.card_eq_fintype_card]
    refine Eq.symm (Nat.div_eq_of_eq_mul_left ?_ ?_)
    · linarith
    · rw [show Fintype.card (Equiv.Perm (Fin 5)) = 120 by native_decide] at this
      linarith
  -- Finally, show |H| ≤ |normalizer|
  have h_contradiction : Nat.card H ≤ Nat.card (Subgroup.normalizer P.toSubgroup) := by
    have h_contradiction : H ≤ Subgroup.normalizer P.toSubgroup := by
      have h_normalizer : (Nat.card (Sylow 5 H)) = 1 := by
        have h_unique : Nat.card (Sylow 5 H) ≡ 1 [MOD 5] ∧ Nat.card (Sylow 5 H) ∣ 40 := by
          have := card_sylow_modEq_one 5 H
          simp_all [← ZMod.natCast_eq_natCast_iff]
          rw [← hH_card]
          have := Sylow.card_eq_index_normalizer (Classical.arbitrary (Sylow 5 H))
          simp_all
          rw [← hH_card]
          have := Subgroup.index_dvd_card
            (Subgroup.normalizer (Classical.arbitrary (Sylow 5 H) |> Sylow.toSubgroup))
          aesop
        have := Nat.le_of_dvd (by decide) h_unique.2
        interval_cases Nat.card (Sylow 5 H) <;> trivial
      have h_unique : ∀ Q : Sylow 5 H, Q = P.subtype (by
      assumption) := by
        rw [Nat.card_eq_one_iff_unique] at h_normalizer
        exact fun Q ↦ h_normalizer.1.elim Q _
      intro h hh
      have h_conj : ∀ g : Equiv.Perm (Fin 5), g ∈ H → g • P = P := by
        intro g hg
        specialize h_unique (g • P |> Sylow.subtype <| by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := hx
          simp_all [Subgroup.mul_mem_cancel_left, Subgroup.mul_mem_cancel_right]
          exact hP hy)
        simp_all [Sylow.smul_eq_iff_mem_normalizer]
        generalize_proofs at h_unique
        simp_all [Sylow.ext_iff]
        exact Subgroup.conjAct_pointwise_smul_iff.mp h_unique
      exact Sylow.smul_eq_iff_mem_normalizer.mp (h_conj h hh)
    exact Subgroup.card_le_of_le h_contradiction
  linarith [hH_card, h_normalizer_card]

/-- If n is a positive integer with 5 | n, n | 120, and n ∉ {15, 30, 40, 60, 120},
    then n | 20. -/
theorem dvd_20_of_constraints (n : ℕ) (hn_pos : 0 < n)
    (h5 : 5 ∣ n) (h120 : n ∣ 120)
    (hne60 : n ≠ 60) (hne120 : n ≠ 120)
    (hne15 : n ≠ 15) (hne30 : n ≠ 30) (hne40 : n ≠ 40) :
    n ∣ 20 := by
  have := Nat.le_of_dvd (by decide) h120
  interval_cases n <;> trivial