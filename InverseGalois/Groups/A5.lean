/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.Basic
import InverseGalois.Polynomial.GaloisGroupTools
import InverseGalois.Groups.A5ModSeven

/-!
# A₅ as an Inverse Galois Group

We show that the alternating group `A₅` (order 60) is an inverse Galois group over `ℚ`,
realized as the Galois group of the polynomial `f = X⁵ + 20X + 16`.

## Strategy

1. `f` is irreducible over `ℚ` (via mod 3)
2. `disc(f) = 32000²`, so `Gal(f) ⊆ A₅`, giving `|Gal| | 60`
3. `5 | |Gal|` (from irreducibility, degree 5)
4. `3 | |Gal|` (from Dedekind's theorem mod 7)
5. By simplicity of `A₅`, no subgroup has order 15 or 30
6. Therefore `|Gal| = 60`, so `Gal(f) ≅ A₅`
-/

open Polynomial IntermediateField

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 1000

namespace IsInverseGalois

/-!
## The polynomial X⁵ + 20X + 16
-/

/-- The polynomial `X⁵ + 20X + 16` over `ℤ`. -/
private def f_a5_Z : ℤ[X] := X ^ 5 + C 20 * X + C 16

/-- The polynomial `X⁵ + 20X + 16` over `ℚ`. -/
private def f_a5 : ℚ[X] := X ^ 5 + C 20 * X + C 16

/-- `f_a5` is the image of `f_a5_Z` under the canonical map `ℤ → ℚ`. -/
private lemma f_a5_eq_map :
    f_a5 = f_a5_Z.map (Int.castRingHom ℚ) := by
  unfold f_a5 f_a5_Z
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]
  norm_num

/-- `f_a5_Z` is monic. -/
private lemma f_a5_Z_monic : f_a5_Z.Monic := by
  erw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_add_C,
    Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num [f_a5_Z]
  norm_num [Polynomial.coeff_X]

/-- `f_a5` has degree 5. -/
private lemma f_a5_natDegree : f_a5.natDegree = 5 := by
  erw [Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num

/-- `f_a5` is nonzero. -/
private lemma f_a5_ne_zero : f_a5 ≠ 0 :=
  ne_of_apply_ne (Polynomial.eval 0) (by norm_num [f_a5])

/-!
## Step 1: Irreducibility
-/

/-
`f_a5_Z` is irreducible over `ℤ`.
-/
private lemma f_a5_Z_irreducible : Irreducible f_a5_Z := by
  have h_irred_mod3 : Irreducible (Polynomial.X^5 + 2 * Polynomial.X + 1 : Polynomial (ZMod 3)) := by
    have h_no_factorization : ∀ p q : Polynomial (ZMod 3),
        p.degree = 2 → q.degree = 3 → p * q ≠ Polynomial.X ^ 5 + 2 * Polynomial.X + 1 := by
      intros p q hp hq h_eq
      have h_coeff : p.coeff 2 * q.coeff 3 = 1 ∧
          p.coeff 2 * q.coeff 2 + p.coeff 1 * q.coeff 3 = 0 ∧
          p.coeff 2 * q.coeff 1 + p.coeff 1 * q.coeff 2 + p.coeff 0 * q.coeff 3 = 0 ∧
          p.coeff 2 * q.coeff 0 + p.coeff 1 * q.coeff 1 + p.coeff 0 * q.coeff 2 = 0 ∧
          p.coeff 1 * q.coeff 0 + p.coeff 0 * q.coeff 1 = 2 ∧ p.coeff 0 * q.coeff 0 = 1 := by
        rw [Polynomial.as_sum_range_C_mul_X_pow p, Polynomial.as_sum_range_C_mul_X_pow q] at h_eq
        norm_num [Finset.sum_range_succ', Polynomial.natDegree_eq_of_degree_eq_some hp,
          Polynomial.natDegree_eq_of_degree_eq_some hq] at h_eq
        simp_all +decide [Polynomial.ext_iff]
        have H0 := h_eq 0
        have H1 := h_eq 1
        have H2 := h_eq 2
        have H3 := h_eq 3
        have H4 := h_eq 4
        have H5 := h_eq 5
        simp_all +decide [Polynomial.coeff_one, Polynomial.coeff_X, mul_assoc, add_mul, pow_succ]
      have h_coeff_cases : ∀ a b c d e f g : ZMod 3, a * g = 1 → a * f + b * g = 0 →
          a * e + b * f + c * g = 0 → a * d + b * e + c * f = 0 → b * d + c * e = 2 →
          c * d = 1 → False := by
        native_decide +revert
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h_coeff
      exact h_coeff_cases _ _ _ _ _ _ _ c1 c2 c3 c4 c5 c6
    constructor
    · exact fun h => absurd (Polynomial.degree_eq_zero_of_isUnit h) (by
        erw [Polynomial.degree_add_C] <;>
          repeat (first
            | erw [Polynomial.degree_add_eq_left_of_degree_lt]
            | erw [Polynomial.degree_C]
            | simp +decide))
    · intro p q hpq
      by_contra h_contra
      push_neg at h_contra
      have h_deg : p.degree + q.degree = 5 := by
        rw [← Polynomial.degree_mul, ← hpq, Polynomial.degree_add_eq_left_of_degree_lt] <;>
          erw [Polynomial.degree_add_eq_left_of_degree_lt] <;> norm_num
        · erw [Polynomial.degree_C] <;> norm_num
          decide +revert
        · erw [Polynomial.degree_C] <;> norm_num
          decide +revert
      have h_deg_cases : p.degree = 1 ∧ q.degree = 4 ∨ p.degree = 4 ∧ q.degree = 1 ∨
          p.degree = 2 ∧ q.degree = 3 ∨ p.degree = 3 ∧ q.degree = 2 := by
        rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.isUnit_iff_degree_eq_zero] at h_contra
        have hp0 : p ≠ 0 := fun h => by
          subst h
          exact absurd hpq <| by exact ne_of_apply_ne (Polynomial.eval 0) <| by simp +decide
        have hq0 : q ≠ 0 := fun h => by
          subst h
          exact absurd hpq <| by exact ne_of_apply_ne (Polynomial.eval 0) <| by simp +decide
        rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0] at *
        norm_cast at *
        omega
      rcases h_deg_cases with (⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩) <;>
        simp_all +decide [Polynomial.isUnit_iff_degree_eq_zero]
      · obtain ⟨a, ha⟩ : ∃ a : ZMod 3, p.eval a = 0 := by
          exact Polynomial.exists_root_of_degree_eq_one hp
        replace hpq := congr_arg (Polynomial.eval a) hpq
        simp_all +decide
        fin_cases a <;> contradiction
      · obtain ⟨r, hr⟩ : ∃ r : ZMod 3, q.eval r = 0 := by
          exact Polynomial.exists_root_of_degree_eq_one hq
        replace hpq := congr_arg (Polynomial.eval r) hpq
        simp_all +decide
        fin_cases r <;> contradiction
      · exact h_no_factorization p q hp hq rfl
      · exact h_no_factorization q p hq hp (by rw [mul_comm])
  convert Polynomial.Monic.irreducible_of_irreducible_map _ _ using 1
  any_goals exact Int.castRingHom (ZMod 3)
  any_goals exact f_a5_Z
  · unfold f_a5_Z
    norm_num [Polynomial.ext_iff]
    erw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_add_C,
      Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num [Polynomial.coeff_X]
    grind only [irreducible_iff, of_irreducible_mul, = IsUnit.mul_iff]
  · infer_instance
  · infer_instance

/-- `f_a5` is irreducible over `ℚ`. -/
private lemma f_a5_irreducible : Irreducible f_a5 := by
  rw [f_a5_eq_map]
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    f_a5_Z_monic.isPrimitive).mp f_a5_Z_irreducible

/-!
## Step 2: Divisibility constraints on |Gal|
-/

/-- 5 divides the Galois group order (from irreducibility and degree 5). -/
private lemma five_dvd_card_gal : 5 ∣ Nat.card f_a5.Gal := by
  exact f_a5_natDegree ▸ natDegree_dvd_card f_a5_irreducible

/-- 3 divides the Galois group order (from Dedekind's theorem mod 7). -/
private lemma three_dvd_card_gal : 3 ∣ Nat.card f_a5.Gal := by
  obtain ⟨σ, hσ⟩ := dedekind_theorem f_a5_Z f_a5_Z_monic (by
    convert f_a5_irreducible using 1
    exact f_a5_eq_map.symm) 7 f_a5_mod7_squarefree
  generalize_proofs at *
  have h3_div_order : 3 ∣ orderOf (Polynomial.Gal.galActionHom (Polynomial.map (Int.castRingHom ℚ) f_a5_Z) ℂ σ) := by
    have h3_div_order :
        3 ∈ (Polynomial.Gal.galActionHom (Polynomial.map (Int.castRingHom ℚ) f_a5_Z) ℂ σ).cycleType := by
      exact hσ.symm ▸ f_a5_mod7_factorizationType
    exact dvd_trans (by aesop) (Multiset.dvd_lcm h3_div_order) |> dvd_trans <| by rw [Equiv.Perm.lcm_cycleType]
  have h3_div_order_sigma : 3 ∣ orderOf σ := by
    exact dvd_trans h3_div_order (orderOf_map_dvd _ _)
  convert h3_div_order_sigma.trans (orderOf_dvd_natCard σ) using 1
  rw [show f_a5 = Polynomial.map (Int.castRingHom ℚ) f_a5_Z from f_a5_eq_map]

/-
The Galois group of X⁵+20X+16 is not S₅.

This follows from the discriminant being a perfect square:
disc(X⁵+20X+16) = 32000². When the discriminant is a perfect square,
all Galois automorphisms induce even permutations of the roots,
so Gal ⊆ A₅. In particular |Gal| ≠ 120 = |S₅|.

The discriminant computation can be verified via the Sylvester matrix:
det(Syl(f,f')) = 1024000000 = 32000².
The connection between discriminant and alternating group uses the
classical identity σ(δ) = sign(σ)·δ where δ = ∏_{i<j}(r_i - r_j).
-/
private lemma card_gal_ne_120 : Nat.card f_a5.Gal ≠ 120 := by
  convert card_gal_a5_ne_120 using 1

/-
The Galois group order divides 60 = |A₅|.
-/
private lemma card_gal_dvd_60 : Nat.card f_a5.Gal ∣ 60 := by
  -- Use card_gal_dvd_card_rootSet_factorial, card_rootSet_eq_natDegree, and f_a5_natDegree.
  have h_card_gal_div_120 : Nat.card f_a5.Gal ∣ Nat.factorial 5 := by
    have h_div : Nat.card f_a5.Gal ∣ (Fintype.card (f_a5.rootSet ℂ)).factorial := by
      convert card_gal_dvd_card_rootSet_factorial f_a5 using 1
    convert h_div using 1
    rw [card_rootSet_eq_natDegree] <;> norm_num [f_a5_natDegree, f_a5_irreducible.separable, f_a5_ne_zero]
  have h_card_gal_div_120 : 15 ∣ Nat.card f_a5.Gal := by
    exact Nat.lcm_dvd three_dvd_card_gal five_dvd_card_gal
  have := Nat.le_of_dvd (by decide) ‹Nat.card f_a5.Gal ∣ Nat.factorial 5›
  interval_cases _ : Nat.card f_a5.Gal <;> simp_all +decide only
  exact card_gal_ne_120 ‹_›

/-!
## Step 3: Lower bound — 60 divides |Gal|
-/

/-- A₅ has no subgroup of order 30 (by simplicity: index 2 would be normal). -/
private lemma A5_no_subgroup_order_30 :
    ∀ H : Subgroup (alternatingGroup (Fin 5)), Nat.card H ≠ 30 := by
  intro H hH
  have h_card_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num
  have h_index : H.index = 2 := by
    have := H.index_mul_card
    rw [hH, h_card_A5] at this
    omega
  have h_normal := Subgroup.normal_of_index_eq_two h_index
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H h_normal with h | h
  · simp [h] at hH
  · rw [h, Subgroup.card_top, h_card_A5] at hH
    omega

/-
60 divides the order of the Galois group. -/
private lemma sixty_dvd_card_gal : 60 ∣ Nat.card f_a5.Gal := by
  -- Since 15 divides the Galois group order and the order divides 60, the only possible values for the order are 15, 30, or 60.
  have h_div : Nat.card f_a5.Gal ∈ ({15, 30, 60} : Set ℕ) := by
    have h_div : 15 ∣ Nat.card f_a5.Gal ∧ Nat.card f_a5.Gal ∣ 60 := by
      exact ⟨Nat.lcm_dvd three_dvd_card_gal five_dvd_card_gal, card_gal_dvd_60⟩
    have := Nat.le_of_dvd (by decide) h_div.2
    interval_cases Nat.card f_a5.Gal <;> simp +decide at h_div ⊢
  -- The Galois group injects into S₅ via galActionHom.
  have h_inj : ∃ H : Subgroup (Equiv.Perm (f_a5.rootSet ℂ)), Nat.card H = Nat.card f_a5.Gal := by
    have h_inj : ∃ f : f_a5.Gal →* Equiv.Perm (f_a5.rootSet ℂ), Function.Injective f := by
      refine' ⟨_, _⟩
      convert Polynomial.Gal.galActionHom f_a5 ℂ
      all_goals generalize_proofs at *
      · grind only [Gal.splits_ℚ_ℂ]
      · convert Polynomial.Gal.galActionHom_injective f_a5 ℂ
    obtain ⟨f, hf⟩ := h_inj
    use f.range
    simp +decide [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.ofInjective _ hf) |> Eq.symm
  -- Since rootSet ℂ has 5 elements, Perm(rootSet ℂ) is isomorphic to Perm(Fin 5).
  have h_iso : ∃ e : f_a5.rootSet ℂ ≃ Fin 5, True := by
    refine' ⟨Fintype.equivOfCardEq _, trivial⟩
    convert card_rootSet_eq_natDegree f_a5 _ _
    · erw [Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num
    · exact f_a5_irreducible.separable
    · exact f_a5_ne_zero
  -- Transfer this to Perm(Fin 5) using Equiv.permCongr with an equivalence rootSet ℂ ≃ Fin 5 (from Fintype.equivOfCardEq).
  obtain ⟨e, he⟩ := h_iso
  have h_iso_perm : ∃ H' : Subgroup (Equiv.Perm (Fin 5)), Nat.card H' = Nat.card f_a5.Gal := by
    obtain ⟨H, hH⟩ := h_inj
    refine' ⟨H.map (Equiv.permCongr e |> MonoidHom.mk' <| by aesop), _⟩
    rw [← hH, Nat.card_congr]
    symm
    refine' Equiv.ofBijective (fun x => ⟨_, Subgroup.mem_map_of_mem _ x.2⟩) ⟨fun x y hxy => _, fun x => _⟩ <;> aesop
  obtain ⟨H', hH'⟩ := h_iso_perm
  have := Perm_Fin5_no_subgroup_order_15 H'
  have := Perm_Fin5_no_subgroup_order_30 H'
  aesop

/-!
## Assembly
-/

/-- The Galois group of `f_a5` has order 60 = |A₅|. -/
private lemma card_gal_a5 : Nat.card f_a5.Gal = 60 := by
  exact Nat.dvd_antisymm card_gal_dvd_60 sixty_dvd_card_gal

/-
The Galois group of `f_a5` is isomorphic to `alternatingGroup (Fin 5)`.
-/
private lemma gal_iso_alt5 :
    Nonempty (f_a5.Gal ≃* (alternatingGroup (Fin 5))) := by
      have h_subgroup : ∃ (f : f_a5.Gal →* Equiv.Perm (f_a5.rootSet ℂ)),
          Function.Injective f ∧ (Nat.card (MonoidHom.range f)) = 60 := by
        obtain ⟨f, hf⟩ : ∃ f : f_a5.Gal →* Equiv.Perm (f_a5.rootSet (f_a5.SplittingField)), Function.Injective f := by
          refine' ⟨_, _⟩
          refine' { .. }
          refine' fun σ => Equiv.ofBijective (fun x => ⟨σ x, _⟩) ⟨_, _⟩
          all_goals norm_num [Function.Injective, Function.Surjective, Equiv.Perm.ext_iff]
          · rw [Polynomial.mem_rootSet] at *
            have := x.2
            rw [Polynomial.mem_rootSet] at this
            rw [aeval_def, Polynomial.eval₂_eq_sum_range] at *
            refine ⟨this.1, ?_⟩
            simpa [map_sum, map_mul, map_pow] using
              congr_arg (σ : f_a5.SplittingField → f_a5.SplittingField) this.2
          · intro a ha
            refine' ⟨σ.symm a, _, _⟩ <;> simp_all +decide [Polynomial.mem_rootSet]
            · convert congr_arg (σ.symm : f_a5.SplittingField → f_a5.SplittingField) ha.2 using 1
              · simp +decide [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
              · norm_num
            · exact σ.apply_symm_apply a
          · aesop
          · aesop
          · intro a₁ a₂ h
            ext x
            by_cases hx : x ∈ f_a5.rootSet f_a5.SplittingField <;> aesop
        have h_iso : Nat.card f_a5.Gal = 60 := by
          convert card_gal_a5
        have h_iso : Nat.card (MonoidHom.range f) = Nat.card f_a5.Gal := by
          exact Nat.card_congr (Equiv.ofInjective _ hf) |> Eq.symm
        have h_iso : Nonempty (Equiv.Perm (f_a5.rootSet (f_a5.SplittingField)) ≃* Equiv.Perm (f_a5.rootSet ℂ)) := by
          refine' ⟨_⟩
          refine' { Equiv.permCongr _ with .. }
          refine' Fintype.equivOfCardEq _
          all_goals norm_num [Fintype.card_perm]
          rw [Polynomial.card_rootSet_eq_natDegree, Polynomial.card_rootSet_eq_natDegree]
          · exact f_a5_irreducible.separable
          · exact IsAlgClosed.splits (Polynomial.map (algebraMap ℚ ℂ) f_a5)
          · exact f_a5_irreducible.separable
          · exact Polynomial.SplittingField.splits _
        obtain ⟨g⟩ := h_iso
        refine' ⟨g.toMonoidHom.comp f, _, _⟩ <;> simp_all +decide [Function.Injective]
        · assumption
        · convert h_iso using 1
          rw [← Nat.card_eq_fintype_card]
          rw [← Nat.card_congr]
          exact ⟨fun x => ⟨g x, by aesop⟩, fun x => ⟨g.symm x, by aesop⟩, fun x => by aesop, fun x => by aesop⟩
      obtain ⟨f, hf_inj, hf_card⟩ := h_subgroup
      have h_image : MonoidHom.range f = alternatingGroup (f_a5.rootSet ℂ) := by
        have h_unique : ∀ (H : Subgroup (Equiv.Perm (f_a5.rootSet ℂ))),
            Nat.card H = 60 → H = alternatingGroup (f_a5.rootSet ℂ) := by
          intros H hH_card
          have h_index : H.index = 2 := by
            have := Subgroup.index_mul_card H
            simp_all +decide
            have h_card_roots : Fintype.card (f_a5.rootSet ℂ) = 5 := by
              convert Polynomial.card_rootSet_eq_natDegree _ _
              · erw [Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num
              · exact f_a5_irreducible.separable
              · exact IsAlgClosed.splits (Polynomial.map (algebraMap ℚ ℂ) f_a5)
            simp_all +decide [Fintype.card_perm]
            exact mul_right_cancel₀ (by decide) this
          grind only [Equiv.Perm.eq_alternatingGroup_of_index_eq_two]
        exact h_unique _ hf_card
      have h_iso : Nonempty (f_a5.Gal ≃* alternatingGroup (f_a5.rootSet ℂ)) := by
        refine' ⟨_⟩
        refine' { Equiv.ofBijective (fun x => ⟨f x, _⟩) ⟨fun x y hxy => _, fun x => _⟩ with .. }
        all_goals simp_all +decide [SetLike.ext_iff]
        any_goals rw [← h_image _ |>.1 ⟨x, rfl⟩]
        · exact hf_inj <| Subtype.ext_iff.mp hxy
        · exact Exists.elim (h_image x |>.2 x.2) fun y hy => ⟨y, Subtype.ext hy⟩
        · aesop
      have h_card : Nat.card (f_a5.rootSet ℂ) = 5 := by
        convert Polynomial.card_rootSet_eq_natDegree _ _
        convert Nat.card_eq_fintype_card
        · erw [Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num
        · exact f_a5_irreducible.separable
        · exact IsAlgClosed.splits (Polynomial.map (algebraMap ℚ ℂ) f_a5)
      have h_iso_fin : Nonempty (f_a5.rootSet ℂ ≃ Fin 5) := by
        exact ⟨Fintype.equivOfCardEq <| by simpa [Nat.card_eq_fintype_card] using h_card⟩
      obtain ⟨e⟩ := h_iso_fin
      refine' ⟨h_iso.some.trans _⟩
      exact e.altCongrHom

/-- The alternating group `A₅` is an inverse Galois group, realized as the
Galois group of `X⁵ + 20X + 16` over `ℚ`. -/
theorem alternating_five :
    IsInverseGalois (↥(alternatingGroup (Fin 5))) := by
  obtain ⟨iso⟩ := gal_iso_alt5
  exact ⟨f_a5.SplittingField, inferInstance, inferInstance, inferInstance,
    { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField,
      to_normal := SplittingField.instNormal f_a5 },
    ⟨iso⟩⟩

end IsInverseGalois

end
