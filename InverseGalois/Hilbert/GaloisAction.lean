/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.Basic

/-!
# Galois-action tools for symmetric groups

This file contains general bridges from polynomial Galois actions to inverse-Galois
realizations, a group-theoretic generation criterion for symmetric groups, and elementary
facts about the family `Xⁿ - X - 1` (including the quadratic case). -/

open Polynomial IntermediateField

noncomputable section

/-!
### Bridge lemma: polynomial to IsInverseGalois
-/

namespace IsInverseGalois

/-- If a polynomial `f` over `ℚ` is irreducible and `galActionHom f ℂ` is bijective,
then `Equiv.Perm (f.rootSet ℂ)` is an inverse Galois group. -/
theorem of_galActionHom_bijective (f : ℚ[X]) (_hf_irr : Irreducible f)
    (hf_bij : Function.Bijective
      (@Polynomial.Gal.galActionHom _ _ f ℂ _ _ ⟨IsAlgClosed.splits _⟩)) :
    IsInverseGalois (Equiv.Perm (f.rootSet ℂ)) :=
  ⟨f.SplittingField, inferInstance, inferInstance, inferInstance,
    { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField,
      to_normal := SplittingField.instNormal f },
    ⟨MulEquiv.ofBijective _ hf_bij⟩⟩

/-- If `f` has degree `n`, is irreducible, and `galActionHom f ℂ` is bijective,
then `Equiv.Perm (Fin n)` is an inverse Galois group. -/
theorem of_galActionHom_bijective' (n : ℕ) (f : ℚ[X]) (hf_irr : Irreducible f)
    (hf_deg : f.natDegree = n)
    (hf_bij : Function.Bijective
      (@Polynomial.Gal.galActionHom _ _ f ℂ _ _ ⟨IsAlgClosed.splits _⟩)) :
    IsInverseGalois (Equiv.Perm (Fin n)) := by
  have h_card : Fintype.card (f.rootSet ℂ) = Fintype.card (Fin n) := by
    rw [Polynomial.card_rootSet_eq_natDegree hf_irr.separable
      (IsAlgClosed.splits _), hf_deg, Fintype.card_fin]
  exact (IsInverseGalois.of_galActionHom_bijective f hf_irr hf_bij).of_mulEquiv
    { Equiv.permCongr (Fintype.equivOfCardEq h_card) with
      map_mul' := fun σ τ ↦ by
        ext
        simp [Equiv.permCongr] }

/-- If `f` is irreducible and `Nat.card f.Gal = (natDegree f)!`, then `galActionHom f ℂ`
is bijective. -/
theorem galActionHom_bijective_of_card_eq_factorial (f : ℚ[X]) (hf_irr : Irreducible f)
    (hf_card : Nat.card f.Gal = f.natDegree.factorial) :
    Function.Bijective
      (@Polynomial.Gal.galActionHom _ _ f ℂ _ _ ⟨IsAlgClosed.splits _⟩) := by
  have : Fact (Polynomial.map (algebraMap ℚ ℂ) f).Splits := ⟨IsAlgClosed.splits _⟩
  constructor
  · exact Polynomial.Gal.galActionHom_injective f ℂ
  · have h_card : Nat.card (Equiv.Perm (f.rootSet ℂ)) = Nat.factorial f.natDegree := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_perm]
      rw [Polynomial.card_rootSet_eq_natDegree]
      · exact hf_irr.separable
      · exact IsAlgClosed.splits _
    have h_card_eq : ∀ {α β : Type} [Finite α] [Finite β],
        Nat.card α = Nat.card β → ∀ {f : α → β}, Function.Injective f →
        Function.Surjective f := by
      intros α β hα hβ h_card f hf_inj
      have := Fintype.ofFinite α
      have := Fintype.ofFinite β
      have hcard' : Fintype.card α = Fintype.card β := by
        simpa [Nat.card_eq_fintype_card] using h_card
      exact ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcard'⟩).2
    exact h_card_eq (hf_card.trans h_card.symm) (Gal.galActionHom_injective f ℂ)

end IsInverseGalois

/-!
### Group theory: generating `Sₙ` from transpositions and cycles

We prove that a transitive subgroup of `Sₙ` containing a transposition and an
`(n-1)`-cycle is all of `Sₙ`.
-/

namespace Equiv.Perm

/-- A transitive subgroup of `Sₙ` containing a transposition and an `(n-1)`-cycle
(i.e., a cycle fixing exactly one point) equals `⊤ = Sₙ`.

**Proof**: Let `σ` be the `(n-1)`-cycle fixing point `c`, and let `(a, b)` be a
transposition in `G`. By transitivity, some conjugate involves `c`, say `(c, d)`.
Conjugating `(c, d)` by powers of `σ` gives `(c, σᵏ(d))` for all `k` (since `σ` fixes `c`).
Since `σ` acts transitively on its support, this gives all star transpositions `(c, x)`.
These generate `Sₙ` since `(x, y) = (c, x)(c, y)(c, x)`. -/
theorem subgroup_eq_top_of_swap_and_cycle {α : Type*} [DecidableEq α] [Fintype α]
    (G : Subgroup (Equiv.Perm α))
    (h_trans : ∀ i j : α, ∃ g ∈ G, g i = j)
    (h_swap : ∃ σ ∈ G, σ.IsSwap)
    (h_cycle : ∃ τ ∈ G, τ.IsCycle ∧ τ.support.card + 1 = Fintype.card α) :
    G = ⊤ := by
  obtain ⟨σ, hσG, hσ_cycle⟩ := h_cycle
  obtain ⟨τ, hτG, hτ_swap⟩ := h_swap
  obtain ⟨c, hc⟩ : ∃ c, c ∉ σ.support ∧ ∀ x, x ≠ c → x ∈ σ.support := by
    obtain ⟨c, hc⟩ : ∃ c, c ∉ σ.support := by
      apply not_forall.mp
      intro h
      have := Finset.eq_univ_of_forall h
      aesop
    have hsub : σ.support ⊆ Finset.univ \ {c} := fun x hx ↦
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hx' ↦ by aesop⟩
    have := Finset.eq_of_subset_of_card_le hsub
    simp_all [Finset.card_sdiff]
  obtain ⟨d, hd⟩ : ∃ d, d ≠ c ∧ (Equiv.swap c d) ∈ G := by
    obtain ⟨a, b, hab, hτ_ab⟩ := hτ_swap
    obtain ⟨g, hgG, hg⟩ := h_trans a c
    refine ⟨g b, ?_, ?_⟩
    · intro h
      have := g.injective (hg.trans h.symm)
      aesop
    · convert G.mul_mem (G.mul_mem hgG hτG) (G.inv_mem hgG) using 1
      ext x
      simp [Equiv.swap_apply_def]
      aesop
  have h_star : ∀ x, x ≠ c → (Equiv.swap c x) ∈ G := by
    intro x hx
    have hσc : ∀ k : ℕ, (σ ^ k) c = c :=
      fun k ↦ Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
        (Equiv.Perm.notMem_support.mp hc.1) k
    have h_conj : ∀ k : ℕ, (Equiv.swap c (σ^[k] d)) ∈ G := by
      intro k
      have : (σ ^ k * Equiv.swap c d * (σ ^ k)⁻¹) ∈ G :=
        G.mul_mem (G.mul_mem (G.pow_mem hσG k) hd.2) (G.inv_mem (G.pow_mem hσG k))
      convert this using 1
      simp [Equiv.Perm.ext_iff, Equiv.swap_apply_def]
      intro x
      split_ifs <;> simp_all [Equiv.symm_apply_eq]
    have h_orbit : ∀ x ∈ σ.support, ∃ k : ℕ, σ^[k] d = x := by
      intro x hx
      rw [Equiv.Perm.mem_support] at hx
      obtain ⟨k, hk⟩ := hσ_cycle.1.choose_spec.2 hx
      obtain ⟨m, hm⟩ := hσ_cycle.1.choose_spec.2 (Equiv.Perm.mem_support.mp (hc.2 d hd.1))
      use Int.toNat ((k - m) % (orderOf σ))
      simp [← hk, ← hm, ← zpow_natCast,
        Int.toNat_of_nonneg (Int.emod_nonneg _
          (Int.natCast_ne_zero.mpr (ne_of_gt (orderOf_pos σ)))), zpow_mod_orderOf]
      simp [zpow_sub]
    obtain ⟨k, rfl⟩ := h_orbit x (hc.2 x hx)
    exact h_conj k
  have h_all : ∀ x y, x ≠ y → (Equiv.swap x y) ∈ G := by
    intro x y hxy
    by_cases hx : x = c
    · grind
    · by_cases hy : y = c
      · simpa [hy, Equiv.swap_comm] using h_star x hx
      · convert G.mul_mem (G.mul_mem (h_star x hx) (h_star y hy)) (h_star x hx) using 1
        aesop
  refine eq_top_iff.mpr fun g _ ↦ ?_
  induction' g using Equiv.Perm.swap_induction_on' with x y hxy ih hmem
  · exact G.one_mem
  · exact G.mul_mem (hmem (Subgroup.mem_top x)) (h_all _ _ ih)

end Equiv.Perm

/-!
### The polynomial `Xⁿ - X - 1` and its properties

We work with the family of trinomials `fₙ(X) = Xⁿ - X - 1` for `n ≥ 2`.
-/

section PolynomialFamily

/-- The polynomial `Xⁿ - X - 1` over `ℚ`. -/
def xnSubXSubOne (n : ℕ) : ℚ[X] := X ^ n - X - C 1

lemma xnSubXSubOne_natDegree (n : ℕ) (hn : 2 ≤ n) :
    (xnSubXSubOne n).natDegree = n := by
  unfold xnSubXSubOne
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
  · linarith
  · linarith
  · lia

/-- **Selmer's Theorem** (1956): The polynomial `Xⁿ - X - 1` is irreducible over `ℚ`
for all `n ≥ 2`. This follows directly from `Polynomial.X_pow_sub_X_sub_one_irreducible_rat`
in Mathlib. -/
theorem selmer_irreducible (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (xnSubXSubOne n) :=
  Polynomial.X_pow_sub_X_sub_one_irreducible_rat (show n ≠ 1 by omega)

/-
For `n = 2`, the Galois group of `X² - X - 1` has order `2 = 2!`.
This follows because the polynomial is irreducible of degree 2, so
`finrank ℚ SplittingField = 2`.
-/
theorem gal_xnSubXSubOne_card_two :
    Nat.card (xnSubXSubOne 2).Gal = Nat.factorial 2 := by
  -- The Galois group of `X² - X - 1` is isomorphic to `S₂`, which has order 2.
  have h_galois : Nat.card (xnSubXSubOne 2).Gal ∣ 2 := by
    convert Subgroup.card_subgroup_dvd_card (Subgroup.map (Polynomial.Gal.galActionHom (xnSubXSubOne 2) ℂ) ⊤) using 1
    all_goals norm_num [Fintype.card_perm]
    · convert Fintype.card_congr (Equiv.ofInjective _ <| Polynomial.Gal.galActionHom_injective _ _)
      · exact Set.Finite.fintype (Set.toFinite _)
      · exact ⟨IsAlgClosed.splits _⟩
    · rw [Fintype.card_ofFinset]
      · rw [show (xnSubXSubOne 2 : ℚ[X]) = X ^ 2 - X - 1 from rfl, Polynomial.aroots_def]
        norm_num
        have hfac : (X ^ 2 - X - 1 : Polynomial ℂ) =
            (X - Polynomial.C ((1 + Real.sqrt 5) / 2 : ℂ)) *
              (X - Polynomial.C ((1 - Real.sqrt 5) / 2 : ℂ)) := by
          refine Polynomial.funext fun x ↦ ?_
          norm_num
          ring_nf
          norm_num [← Complex.ofReal_pow]
          ring
        rw [hfac]
        rw [Polynomial.roots_mul <| mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
            (Polynomial.X_sub_C_ne_zero _),
          Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
        norm_num
        rw [Finset.card_insert_of_notMem, Finset.card_singleton] <;> norm_num [Complex.ext_iff]
        have := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
        nlinarith
      · simp [Polynomial.rootSet_def]
  have h_galois_order : 2 ∣ Nat.card (xnSubXSubOne 2).Gal := by
    convert Polynomial.Gal.prime_degree_dvd_card (selmer_irreducible 2 (by decide)) _
    · erw [Polynomial.natDegree_sub_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
    · rw [xnSubXSubOne_natDegree] <;> norm_num
  exact Nat.dvd_antisymm h_galois h_galois_order

/-! -/

end PolynomialFamily

end
