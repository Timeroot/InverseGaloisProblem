/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.DorgeBauer
import InverseGalois.Hilbert.Analytic.DorgeBauerPuiseux
import InverseGalois.Polynomial.MonicAssociate

/-!
# Hilbert's Irreducibility Theorem

This file states and proves Hilbert's Irreducibility Theorem (HIT).

## Main result

**Hilbert's Irreducibility Theorem**: If `f(T, X) ∈ ℚ[T, X]` is irreducible as a
bivariate polynomial, then for infinitely many `t₀ ∈ ℤ`, the specialization
`f(t₀, X) ∈ ℚ[X]` is irreducible.

1. **Gauss's Lemma reduction**: We may assume `f ∈ ℤ[T][X]` is primitive.

2. **Root bound**: For monic `f(t₀, X)` of degree `d`, all roots satisfy
   `|α| ≤ 1 + max|aᵢ(t₀)|`, which grows polynomially in `|t₀|`.

3. **Factor counting**: If `f(t₀, X) = g(X)·h(X)` with `deg g = k`, then the
   coefficients of `g` are elementary symmetric functions of `k` roots, bounded
   by `C · |t₀|^M` for constants `C, M` depending only on `f`.

4. **Key estimate**: For each degree split `(k, d-k)`, the set of `t₀ ∈ [-N, N]`
   giving this split has cardinality `O(N^{1-1/d})`, which is `o(N)`.

5. **Conclusion**: Since there are finitely many degree splits and each contributes
   `o(N)` bad specializations, the total number of bad `t₀ ∈ [-N, N]` is `o(N)`,
   so infinitely many `t₀` give irreducible specializations.

## Formalization notes

We represent bivariate polynomials as elements of `Polynomial (Polynomial ℚ)` ≅ ℚ[T][X],
where the outer variable is X and the coefficients are polynomials in T over ℚ.

The specialization `f(t₀, X)` is obtained by mapping each coefficient polynomial via
`Polynomial.evalRingHom t₀`, giving `f.map (Polynomial.evalRingHom (↑t₀ : ℚ))`.

## References

* Hilbert, D. "Über die Irreduzibilität ganzer rationaler Funktionen mit ganzzahligen
  Koeffizienten", 1892
* Dörge, K. "Einfacher Beweis des Hilbertschen Irreduzibilitätssatzes", 1927
* Serre, J.-P. "Topics in Galois Theory", 2008, Chapter 3
* Lang, S. "Fundamentals of Diophantine Geometry", 1983, Chapter 9 -/

open Polynomial

noncomputable section

/-!
### Specialization of bivariate polynomials
-/

/-- The specialization map: given `t : ℤ`, evaluate each coefficient polynomial at `t`.
For `f ∈ ℚ[T][X]`, this gives `f(t, X) ∈ ℚ[X]`. -/
def specialize (f : Polynomial (Polynomial ℚ)) (t : ℤ) : Polynomial ℚ :=
  f.map (Polynomial.evalRingHom (↑t : ℚ))

/-
Specialization preserves monicity for monic polynomials.
If `f ∈ ℚ[T][X]` is monic in `X`, then `f(t₀, X)` is monic for all `t₀`.
-/
lemma specialize_monic (f : Polynomial (Polynomial ℚ))
    (hf_monic : f.Monic) (t : ℤ) :
    (specialize f t).Monic :=
  hf_monic.map _

/-
Specialization preserves the degree for monic polynomials.
-/
lemma specialize_monic_natDegree (f : Polynomial (Polynomial ℚ))
    (hf_monic : f.Monic) (t : ℤ) :
    (specialize f t).natDegree = f.natDegree := by
      unfold specialize
      rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero]
      simp_all

/-!
### Statement of Hilbert's Irreducibility Theorem
-/

/-- A union of `n` sets satisfying the same cardinality bound on symmetric intervals
satisfies that bound multiplied by `n`.

The statement does not require positivity or sublinearity assumptions on `C` and `α`; those
conditions belong to applications of this estimate, not to the finite-union argument. -/
lemma union_sublinear_ncard {n : ℕ} (S : Fin n → Set ℤ)
    (C α : ℝ)
    (hS : ∀ i : Fin n, ∀ N : ℕ, 0 < N →
      (Set.ncard (S i ∩ Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) ≤ C * (N : ℝ) ^ α) :
    ∀ N : ℕ, 0 < N →
      (Set.ncard ((⋃ i, S i) ∩ Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) ≤ n * C * (N : ℝ) ^ α := by
  intro N hN
  rw [Set.inter_comm, Set.ncard_eq_toFinset_card']
  refine le_trans ?_ (show (∑ i : Fin n, (Set.ncard (S i ∩ Set.Icc (-N : ℤ) N) : ℝ)) ≤ n * C * N ^ α from ?_)
  · norm_cast
    convert Finset.card_biUnion_le
    any_goals try infer_instance
    any_goals exact fun i ↦ (S i ∩ Set.Icc (-N : ℤ) N).toFinset
    · ext
      simp_all only [Set.mem_toFinset, Set.mem_inter_iff, Set.mem_Icc, Set.mem_iUnion, Finset.mem_biUnion, Finset.mem_univ,
        true_and, exists_and_right]
      apply Iff.intro
      · intro a_1
        simp_all only [and_self]
      · intro a_1
        simp_all only [and_self]
    · rw [Set.ncard_eq_toFinset_card']
  · simpa [mul_assoc] using Finset.sum_le_sum fun i (hi : i ∈ Finset.univ) ↦ hS i N hN

/-
The monic case of HIT: for monic irreducible f of degree ≥ 2, the irreducible
specializations form an infinite set. Uses the Dörge density estimate.
-/

/-- **Absolute irreducibility is inherited by the monic associate.**

If `f` is absolutely irreducible (irreducible after base change `ℚ → ℚ̄`) and
`deg f ≥ 2`, then so is its monic associate `monicAssociate f`.

Base change by the field hom `ℚ → ℚ̄` (which is injective and preserves
`natDegree`, `leadingCoeff` and `coeff`) commutes with `monicAssociate`, so
`(monicAssociate f).map (ℚ → ℚ̄) = monicAssociate (f.map (ℚ → ℚ̄))`. The
result then follows from the field-level version of `monicAssociate_irreducible`
applied to the absolutely irreducible polynomial `f.map (ℚ → ℚ̄)` over `ℚ̄[T]`. -/

/-
Composition with `C c * X` for a nonzero `c` in a field `L` preserves
irreducibility (it is a ring automorphism of `L[X]` with inverse
`·.comp (C c⁻¹ * X)`).
-/
lemma irreducible_comp_C_mul_X {L : Type*} [Field L] (q : Polynomial L) {c : L} (hc : c ≠ 0) :
    Irreducible (q.comp (Polynomial.C c * Polynomial.X)) ↔ Irreducible q := by
  constructor <;> intro hq <;> have := hq.2 <;> simp_all
  · -- Let's assume that $q$ is reducible and derive a contradiction.
    by_contra hq_reducible
    obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : L[X], a.degree > 0 ∧ b.degree > 0 ∧ q = a * b := by
      by_cases hq_unit : IsUnit q <;> by_cases hq_zero : q = 0 <;> simp_all [irreducible_iff]
      · rw [Polynomial.isUnit_iff] at hq_unit
        simp_all only [isUnit_iff_ne_zero, ne_eq]
        obtain ⟨w, h⟩ := hq_unit
        obtain ⟨left, right⟩ := h
        subst right
        simp_all only [C_comp, isUnit_map_iff, isUnit_iff_ne_zero, ne_eq, not_false_eq_true, not_true_eq_false]
      · rcases hq_reducible with ⟨a, b, rfl, ha, hb⟩
        refine ⟨a, ?_, b, ?_, rfl⟩
        · exact not_le.mp fun ha' ↦ ha <| Polynomial.isUnit_iff_degree_eq_zero.mpr <|
            le_antisymm ha' <| le_of_not_gt fun ha'' ↦ by simp_all
        · exact not_le.mp fun hb' ↦ hb <| Polynomial.isUnit_iff_degree_eq_zero.mpr <|
            le_antisymm hb' <| le_of_not_gt fun hb'' ↦ by simp_all
    simp_all [Polynomial.isUnit_iff_degree_eq_zero]
    cases this rfl <;>
      simp_all [Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt ha),
        Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hb)]
    all_goals
      rw [Polynomial.degree_eq_natDegree
        (ne_of_apply_ne Polynomial.natDegree
          (by
            erw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X]
            · simp only [mul_one, Polynomial.natDegree_zero]
              omega
            · exact hc))] at *
      simp_all [Polynomial.natDegree_comp, Polynomial.natDegree_mul']
  · constructor
    · intro h
      have := Polynomial.natDegree_eq_zero_of_isUnit h
      simp_all [Polynomial.natDegree_comp, Polynomial.natDegree_mul']
      have hpos := Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hq)
      exact absurd this (Nat.ne_of_gt hpos)
    · intro a b hab
      have := @this (a.comp (Polynomial.C c⁻¹ * Polynomial.X)) (b.comp (Polynomial.C c⁻¹ * Polynomial.X)) ?_
      · rcases this with (h | h) <;> have := Polynomial.natDegree_eq_zero_of_isUnit h <;>
          simp_all [Polynomial.natDegree_comp, Polynomial.natDegree_mul']
        all_goals
          rw [Polynomial.eq_C_of_natDegree_eq_zero this] at h ⊢
          simp_all
      · convert congr_arg (Polynomial.comp · (Polynomial.C c⁻¹ * Polynomial.X)) hab using 1 <;>
          simp [Polynomial.comp_assoc]
        simp [← mul_assoc, ← Polynomial.C_mul, hc]

lemma monicAssociate_absIrr (f : Polynomial (Polynomial ℚ)) (hf_deg : 2 ≤ f.natDegree)
    (hf_abs_irr :
      Irreducible (f.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))))) :
    Irreducible ((monicAssociate f).map
      (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) := by
  -- Let K = AlgebraicClosure ℚ and φ = mapRingHom (algebraMap ℚ K) : ℚ[T] →+* K[T] (injective). Put
  set K := AlgebraicClosure ℚ
  set φ : Polynomial ℚ →+* Polynomial K := mapRingHom (algebraMap ℚ K)
  set fK := f.map φ
  set M := (monicAssociate f).map φ
  set Ψ := algebraMap (Polynomial K) (FractionRing (Polynomial K))
  have hf_deg1 : f.natDegree ≥ 1 := by linarith
  -- By `IsPrimitive.irreducible_iff_irreducible_map_fraction_map`, it suffices to show `Irreducible (M.map Ψ)`, where Ψ is the fraction field map.
  suffices hM_map : Irreducible (M.map Ψ) by
    convert Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map _ |>.2 hM_map
    exact ((monicAssociate_monic f hf_deg1).map φ).isPrimitive
  have hM_comp_base : M.comp (Polynomial.C (fK.leadingCoeff) * Polynomial.X) =
      Polynomial.C (fK.leadingCoeff ^ (fK.natDegree - 1)) * fK := by
    convert congr_arg (Polynomial.map φ) (monicAssociate_comp_identity f hf_deg1) using 1
    · rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero]
      · simp_all only [ge_iff_le, coe_mapRingHom, fK, K, φ, M]
        ext n n_1 : 2
        simp_all only [comp_C_mul_X_coeff, coeff_map, coe_mapRingHom, Polynomial.map_mul, Polynomial.map_pow]
      · simp_all only [ge_iff_le, coe_mapRingHom, ne_eq, Polynomial.map_eq_zero, leadingCoeff_eq_zero, fK, K, φ]
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [natDegree_zero, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero]
    · simp +zetaDelta
      rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;> norm_num
      · rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero]
        · simp_all only [ge_iff_le, coe_mapRingHom, true_or, fK, K, φ]
        · simp_all only [ge_iff_le, coe_mapRingHom, ne_eq, Polynomial.map_eq_zero, leadingCoeff_eq_zero, fK, K, φ]
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [natDegree_zero, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero]
      · simp_all only [ge_iff_le, fK, K, φ]
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [natDegree_zero, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero]
  have hM_comp : (M.map Ψ).comp (Polynomial.C (Ψ (fK.leadingCoeff)) * Polynomial.X) =
      Polynomial.C (Ψ (fK.leadingCoeff ^ (fK.natDegree - 1))) * (fK.map Ψ) := by
    convert congr_arg (Polynomial.map Ψ) hM_comp_base using 1 <;> norm_num [Polynomial.map_comp]
  have h_fK_nonconst : fK.natDegree > 0 := by
    rw [Polynomial.natDegree_map_eq_of_injective]
    · linarith
    · exact Polynomial.map_injective _ (algebraMap ℚ K).injective
  have h_fK_primitive : fK.IsPrimitive := by
    grind only [Irreducible.isPrimitive]
  have hM_irred_base : Irreducible (fK.map Ψ) := by
    convert Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map h_fK_primitive |>.1 hf_abs_irr using 1
    infer_instance
  have hM_irred : Irreducible (Polynomial.C (Ψ (fK.leadingCoeff ^ (fK.natDegree - 1))) * (fK.map Ψ)) := by
    rw [irreducible_mul_iff]
    refine Or.inr ⟨hM_irred_base, Polynomial.isUnit_C.mpr ?_⟩
    simp_all only [ge_iff_le, map_pow, gt_iff_lt, isUnit_iff_ne_zero, ne_eq, pow_eq_zero_iff', FaithfulSMul.algebraMap_eq_zero_iff, leadingCoeff_eq_zero, not_and, natDegree_zero, zero_tsub, not_true_eq_false, not_false_eq_true, implies_true, fK, K, φ, M, Ψ]
  convert irreducible_comp_C_mul_X (Polynomial.map (algebraMap K[X] (FractionRing K[X])) M)
    (show algebraMap K[X] (FractionRing K[X]) fK.leadingCoeff ≠ 0 from ?_) |>.1 ?_ using 1

  · simp_all only [ge_iff_le, map_pow, gt_iff_lt, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, leadingCoeff_eq_zero, fK, K, φ, M, Ψ]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [not_irreducible_zero]
  · simp_all only [ge_iff_le, map_pow, gt_iff_lt, fK, K, φ, M, Ψ]

theorem hilbert_irreducibility_monic (f : Polynomial (Polynomial ℚ))
    (hf : Irreducible f) (hf_monic : f.Monic) (hf_deg : 2 ≤ f.natDegree)
    (hf_abs_irr :
      Irreducible (f.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))))) :
    Set.Infinite {t : ℤ | Irreducible (specialize f t)} := by
  refine Set.Infinite.mono (s := Set.univ \ ⋃ k ∈ Finset.Ico 1 f.natDegree,
    { t : ℤ | ∃ g : Polynomial ℚ, g.natDegree = k ∧ g.Monic ∧ g ∣ specialize f t }) ?_ ?_
  · intro t ht
    simp [specialize] at ht ⊢
    constructor
    · intro h
      have := Polynomial.natDegree_eq_zero_of_isUnit h
      rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] at this <;> simp_all
    · intro a b hab
      contrapose! ht
      simp_all [Polynomial.isUnit_iff_degree_eq_zero]
      -- Since $a$ and $b$ are non-constant polynomials, their degrees are at least 1.
      have ha_deg : 1 ≤ a.natDegree := by
        by_cases ha : a = 0 <;> simp_all [Polynomial.degree_eq_natDegree]
        · rw [Polynomial.ext_iff] at hab
          specialize hab (Polynomial.natDegree f)
          simp_all [Polynomial.coeff_map]
        · exact Nat.pos_of_ne_zero ht.1
      have hb_deg : 1 ≤ b.natDegree := by
        by_cases hb : b = 0 <;> simp_all [Polynomial.degree_eq_natDegree]
        · replace hab := congr_arg (fun p ↦ p.coeff (Polynomial.natDegree f)) hab
          simp_all [Polynomial.coeff_map]
        · exact Nat.pos_of_ne_zero ht.2
      refine ⟨Polynomial.C (a.leadingCoeff) ⁻¹ * a, ?_, ?_, ?_, ?_⟩
      · rw [Polynomial.natDegree_C_mul]
        · simp_all only
        · simp_all only [ne_eq, inv_eq_zero, leadingCoeff_eq_zero]
          obtain ⟨left, right⟩ := ht
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          subst a_1
          simp_all only [zero_mul, natDegree_zero, nonpos_iff_eq_zero, one_ne_zero]
      · rw [Polynomial.natDegree_C_mul] <;> norm_num [ha_deg, hb_deg]
        · have := congr_arg Polynomial.natDegree hab
          rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] at this <;> norm_num at this ⊢
          · rw [this, Polynomial.natDegree_mul']
            · omega
            · have ha0 : a ≠ 0 := fun h ↦ by simp [h] at ha_deg
              have hb0 : b ≠ 0 := fun h ↦ by simp [h] at hb_deg
              exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr ha0)
                (Polynomial.leadingCoeff_ne_zero.mpr hb0)
          · simp_all
        · obtain ⟨left, right⟩ := ht
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          subst a_1
          simp_all only [zero_mul, natDegree_zero, nonpos_iff_eq_zero, one_ne_zero]
      · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, inv_mul_cancel₀]
        simp_all only [ne_eq, leadingCoeff_eq_zero]
        obtain ⟨left, right⟩ := ht
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [zero_mul, natDegree_zero, nonpos_iff_eq_zero, one_ne_zero]
      · refine ⟨Polynomial.C a.leadingCoeff * b, ?_⟩
        ring_nf
        rw [mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ (by simp_all only [ne_eq, leadingCoeff_eq_zero]; obtain ⟨left, right⟩ := ht; apply Aesop.BuiltinRules.not_intro; intro a_1; subst a_1; simp_all only [zero_mul, natDegree_zero, nonpos_iff_eq_zero, one_ne_zero]), Polynomial.C_1, mul_one]
  · have h_union_sublinear : ∃ (C : ℝ) (α : ℝ), 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard ((⋃ k ∈ Finset.Ico 1 f.natDegree, {t : ℤ | ∃ g : Polynomial ℚ,
          g.natDegree = k ∧ g.Monic ∧ g ∣ specialize f t}) ∩
        Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) ≤ C * (N : ℝ) ^ α := by
          have h_per_k : ∀ k ∈ Finset.Ico 1 f.natDegree,
              ∃ (C : ℝ) (α : ℝ), 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
              (Set.ncard ({t : ℤ | ∃ g : Polynomial ℚ, g.natDegree = k ∧ g.Monic ∧ g ∣ specialize f t} ∩
                Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) ≤ C * (N : ℝ) ^ α :=
            fun k hk ↦
              dorge_density_estimate f hf hf_monic hf_abs_irr k
                (Finset.mem_Ico.mp hk |>.1) (Finset.mem_Ico.mp hk |>.2)
          choose! C α hC hα hα' h using h_per_k
          refine ⟨∑ k ∈ Finset.Ico 1 f.natDegree, C k, sSup (Finset.image α (Finset.Ico 1 f.natDegree)), ?_, ?_, ?_, ?_⟩
          · exact Finset.sum_pos hC (Finset.nonempty_Ico.mpr hf_deg)
          · apply Real.sSup_nonneg
            intro x a
            simp_all only [Finset.mem_Ico, and_imp, Finset.coe_image, Finset.coe_Ico, Set.mem_image, Set.mem_Ico]
            obtain ⟨w, h_1⟩ := a
            obtain ⟨left, right⟩ := h_1
            obtain ⟨left, right_1⟩ := left
            subst right
            simp_all only
          · rcases Finset.eq_empty_or_nonempty (Finset.image α (Finset.Ico 1 f.natDegree)) with h | ⟨x, hx⟩ <;> simp_all
            -- Since the image of α over the finite set {1, ..., f.natDegree - 1} is finite, its supremum is attained.
            obtain ⟨k, hk⟩ : ∃ k ∈ Finset.Ico 1 f.natDegree, ∀ j ∈ Finset.Ico 1 f.natDegree, α j ≤ α k := by
              exact Finset.exists_max_image _ _ ⟨hx.choose, Finset.mem_Ico.mpr hx.choose_spec.1⟩
            exact lt_of_le_of_lt
              (csSup_le (Set.Nonempty.image _ <| Set.nonempty_Ico.mpr <| by linarith) <|
                Set.forall_mem_image.mpr fun j hj ↦ hk.2 j <| Finset.mem_Ico.mpr hj) <|
              hα' k (Finset.mem_Ico.mp hk.1 |>.1) (Finset.mem_Ico.mp hk.1 |>.2)
          · intro N hN_pos
            have h_ncard_le : (Set.ncard ((⋃ k ∈ Finset.Ico 1 f.natDegree, {t : ℤ | ∃ g : Polynomial ℚ,
              g.natDegree = k ∧ g.Monic ∧ g ∣ specialize f t}) ∩
              Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) ≤
                ∑ k ∈ Finset.Ico 1 f.natDegree, (Set.ncard ({t : ℤ | ∃ g : Polynomial ℚ,
              g.natDegree = k ∧ g.Monic ∧ g ∣ specialize f t} ∩
              Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) := by
                rw [Set.inter_comm, Set.inter_iUnion₂]
                norm_cast
                simpa only [Set.inter_comm] using
                  Finset.set_ncard_biUnion_le (Finset.Ico 1 f.natDegree) fun k ↦
                    Set.Icc (-N : ℤ) N ∩ { t : ℤ | ∃ g : Polynomial ℚ, g.natDegree = k ∧ g.Monic ∧ g ∣ specialize f t }
            refine le_trans h_ncard_le ?_
            rw [Finset.sum_mul]
            have hbdd : ∀ k ∈ Finset.Ico 1 f.natDegree,
                α k ≤ sSup (Finset.image α (Finset.Ico 1 f.natDegree)) :=
              fun k hk ↦ le_csSup (Set.Finite.bddAbove <| Finset.finite_toSet _)
                (Finset.mem_image_of_mem _ hk)
            exact Finset.sum_le_sum fun k hk ↦
              le_trans (h k hk N hN_pos)
                (mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow_of_exponent_le (mod_cast hN_pos) (hbdd k hk))
                  (le_of_lt <| hC k hk))
    obtain ⟨C, α, hC, hα, hα', h⟩ := h_union_sublinear
    rw [← Set.compl_eq_univ_diff]
    exact infinite_complement_of_sublinear_ncard hC hα' h

/-- A degree-one bivariate polynomial has infinitely many irreducible integer
specializations. Only the finitely many zeros of its leading coefficient are excluded. -/
lemma hit_degree_one (f : Polynomial (Polynomial ℚ))
    (hf : Irreducible f) (hf_deg : f.natDegree = 1) :
    Set.Infinite {t : ℤ | Irreducible (specialize f t)} := by
  obtain ⟨a, b, ha⟩ : ∃ a b : Polynomial ℚ, f = Polynomial.C a * Polynomial.X + Polynomial.C b ∧ a ≠ 0 := by
    refine ⟨f.coeff 1, f.coeff 0, ?_, ?_⟩
    · nth_rw 1 [Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hf_deg)]
    · rw [← hf_deg, Polynomial.coeff_natDegree]
      simp_all only [ne_eq, leadingCoeff_eq_zero]
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [not_irreducible_zero]
  -- The set {t : a(t) = 0} is finite (a is a nonzero polynomial, has finitely many roots).
  have h_finite_roots : Set.Finite {t : ℤ | a.eval (t : ℚ) = 0} :=
    Set.Finite.subset (a.roots.toFinset.finite_toSet.preimage Int.cast_injective.injOn) fun x hx ↦ by simp_all
  refine Set.Infinite.mono ?_ (h_finite_roots.infinite_compl)
  intro t ht
  simp_all [specialize]
  convert Polynomial.irreducible_of_degree_eq_one _
  rw [Polynomial.degree_add_C] <;> rw [Polynomial.degree_C_mul_X] <;> trivial

/-- Multiplication by a constant unit in `ℚ[T]` preserves irreducibility after every
integer specialization. -/
lemma irreducible_specialize_of_C_mul {f : Polynomial (Polynomial ℚ)}
    {c : Polynomial ℚ} (hc : IsUnit c) (t : ℤ) :
    Irreducible (specialize (Polynomial.C c * f) t) ↔ Irreducible (specialize f t) := by
  simp [specialize]
  constructor <;> intro h
  · rw [irreducible_mul_iff] at h
    cases h <;> simp_all [Polynomial.isUnit_iff_degree_eq_zero]
    exact absurd ‹Irreducible (C (eval (t : ℚ) c)) ∧ (map (evalRingHom (t : ℚ)) f).degree = 0›.1
      (Polynomial.not_irreducible_C _)
  · rw [irreducible_mul_iff]
    refine Or.inr ⟨h, Polynomial.isUnit_C.mpr ?_⟩
    rw [Polynomial.isUnit_iff] at *
    simp_all only [isUnit_iff_ne_zero, ne_eq]
    obtain ⟨w, h_1⟩ := hc
    obtain ⟨left, right⟩ := h_1
    subst right
    simp_all only [eval_C, not_false_eq_true]

/-- **Hilbert's irreducibility theorem for integer specializations.**

If `f ∈ ℚ[T][X]` has positive `X`-degree and remains irreducible after extending the
coefficient field to `ℚ̄`, then infinitely many integer specializations `f(t, X)` are
irreducible over `ℚ`. The separate arithmetic irreducibility hypothesis is retained as a
convenient explicit interface for callers. -/
theorem hilbert_irreducibility_theorem (f : Polynomial (Polynomial ℚ))
    (hf : Irreducible f) (hf_deg : 1 ≤ f.natDegree)
    (hf_abs_irr :
      Irreducible (f.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))))) :
    Set.Infinite {t : ℤ | Irreducible (specialize f t)} := by
  rcases eq_or_lt_of_le hf_deg with h_eq | h_lt
  · exact hit_degree_one f hf h_eq.symm
  · by_cases hm : f.Monic
    · exact hilbert_irreducibility_monic f hf hm h_lt hf_abs_irr
    · -- Non-monic case: reduce to monic via Tschirnhaus substitution.
      -- Let a = f.leadingCoeff ∈ ℚ[T]. Define f̃(T, X) = a(T)^{d-1} · f(T, X/a(T)).
      -- Then f̃ ∈ ℚ[T][X] is monic, irreducible, same degree d, and for all t
      -- with a(t) ≠ 0: Irreducible(specialize f t) ↔ Irreducible(specialize f̃ t).
      -- Since {t : a(t) = 0} is finite and {t : Irreducible(specialize f̃ t)} is
      -- infinite (by hilbert_irreducibility_monic), the conclusion follows.
      -- By leadingCoeff_roots_finite, there are only finitely many $t$ such that $f(t)$ is not monic.
      have hf_deg1 : f.natDegree ≥ 1 := by linarith
      have h_finite_monomial : Set.Finite {t : ℤ | Polynomial.eval (t : ℚ) f.leadingCoeff = 0} := by
        apply leadingCoeff_roots_finite
        simp_all only [ge_iff_le, ne_eq, leadingCoeff_eq_zero]
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [not_irreducible_zero]
      -- By monicAssociate_specialize_iff, for any $t$ not in the finite set, the specialize of $f$ at $t$ is irreducible if and only if the specialize of $monicAssociate f$ at $t$ is irreducible.
      have h_equiv : {t : ℤ | Irreducible (specialize f t)} ⊇
          {t : ℤ | Irreducible (specialize (monicAssociate f) t)} \
            {t : ℤ | Polynomial.eval (t : ℚ) f.leadingCoeff = 0} := by
        intro t ht
        refine (monicAssociate_specialize_iff f hf_deg1 t ?_).mp ht.left
        simp_all
      have h_inf_monomial : Set.Infinite {t : ℤ | Irreducible (specialize (monicAssociate f) t)} := by
        apply hilbert_irreducibility_monic
        · exact monicAssociate_irreducible f hf h_lt
        · exact monicAssociate_monic f hf_deg1
        · rw [monicAssociate_natDegree] <;> linarith
        · exact monicAssociate_absIrr f h_lt hf_abs_irr
      exact Set.Infinite.mono h_equiv (h_inf_monomial.diff h_finite_monomial)

/-!
### Key estimate: bounding reducible specializations

The heart of the proof: for each factorization degree `k`, there are at most
`O(N^{1-1/d})` integers `t ∈ [-N, N]` such that `f(t, X)` has a factor of degree `k`.
-/

/-- The set of integers `t` for which `f(t, X)` has a monic factor of exact degree `k`
in `ℚ[X]`. -/
def reducibleLocus (f : Polynomial (Polynomial ℚ)) (k : ℕ) : Set ℤ :=
  {t : ℤ | ∃ g : Polynomial ℚ, g.natDegree = k ∧ g.Monic ∧ g ∣ (specialize f t)}

/-
**Key lemma**: If `f ∈ ℚ[T][X]` is irreducible, monic in `X` of degree `d ≥ 2`,
and `1 ≤ k < d`, then the reducible locus for degree `k` is not all of ℤ. -/
lemma reducibleLocus_not_univ (f : Polynomial (Polynomial ℚ))
    (hf : Irreducible f) (hf_monic : f.Monic)
    (hf_abs_irr :
      Irreducible (f.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))))
    (k : ℕ) (hk : 1 ≤ k) (hk' : k < f.natDegree) :
    (reducibleLocus f k) ≠ Set.univ := by
      refine Set.nonempty_compl.1 ?_
      obtain ⟨C, α, hC, hα, hα', h⟩ := dorge_density_estimate f hf hf_monic hf_abs_irr k hk hk'
      convert infinite_complement_of_sublinear_ncard hC hα' _ |> Set.Infinite.nonempty
      convert h using 1

/-!
### From the key lemma to HIT

The final assembly: take the complement of all reducible loci.
-/

/-- A positive-degree specialization of unchanged degree is irreducible exactly when it
has no monic factor of any degree strictly between zero and the degree of the family.

Monicity of the family is not needed: any nonconstant factor can be normalized to a monic
one over `ℚ`. -/
lemma irreducible_iff_not_in_reducibleLocus (f : Polynomial (Polynomial ℚ))
    (t : ℤ)
    (ht_deg : (specialize f t).natDegree = f.natDegree)
    (h_pos : 1 ≤ f.natDegree) :
    Irreducible (specialize f t) ↔
      ∀ k, 1 ≤ k → k < f.natDegree → t ∉ reducibleLocus f k := by
        constructor <;> intro h <;> contrapose! h <;> simp_all [reducibleLocus]
        · rcases h with ⟨g, hg₁, hg₂, hg₃, hg₄⟩
          rw [irreducible_iff]
          simp_all [Polynomial.Monic.def]
          obtain ⟨q, hq⟩ := hg₄
          use fun _ ↦ ⟨g, q, by linear_combination' hq,
            fun h ↦ by linarith [Polynomial.natDegree_eq_zero_of_isUnit h],
            fun h ↦ by
              have h1 := Polynomial.natDegree_eq_zero_of_isUnit h
              have h2 := congr_arg Polynomial.natDegree hq
              rw [Polynomial.natDegree_mul'] at h2
              · omega
              · rw [hg₃, one_mul, Ne, Polynomial.leadingCoeff_eq_zero]
                exact h.ne_zero⟩
        · obtain ⟨g, hg⟩ : ∃ g : Polynomial ℚ, g ∣ specialize f t ∧ 1 ≤ g.natDegree ∧ g.natDegree < f.natDegree := by
            by_cases h_unit : IsUnit (specialize f t) ∨ specialize f t = 0
            · cases h_unit <;> simp_all [Polynomial.natDegree_eq_zero_of_isUnit]
              · linarith
              · grind
            · obtain ⟨g, hg⟩ : ∃ g : Polynomial ℚ,
                  g ∣ specialize f t ∧ 1 ≤ g.natDegree ∧ g.natDegree < (specialize f t).natDegree := by
                have h_factor : ∃ g h : Polynomial ℚ,
                    g ∣ specialize f t ∧ h ∣ specialize f t ∧
                      g.natDegree + h.natDegree = (specialize f t).natDegree ∧
                        1 ≤ g.natDegree ∧ 1 ≤ h.natDegree := by
                  obtain ⟨g, h, hg, hh, hgh⟩ : ∃ g h : Polynomial ℚ,
                      g ∣ specialize f t ∧ h ∣ specialize f t ∧ g * h = specialize f t ∧
                        ¬IsUnit g ∧ ¬IsUnit h := by
                    rw [irreducible_iff] at h
                    push_neg at h
                    obtain ⟨a, b, hb⟩ := h (by tauto)
                    exact ⟨a, b, hb.1.symm ▸ dvd_mul_right _ _, hb.1.symm ▸ dvd_mul_left _ _,
                      hb.1.symm, hb.2.1, hb.2.2⟩
                  refine ⟨g, h, hg, hh, ?_, ?_, ?_⟩
                  · rw [← hgh.1, Polynomial.natDegree_mul']
                    rw [← Polynomial.leadingCoeff_mul, hgh.1, Ne,
                      Polynomial.leadingCoeff_eq_zero]
                    exact fun hz ↦ h_unit (Or.inr hz)
                  · exact Nat.pos_of_ne_zero fun con ↦
                      hgh.2.1 <| Polynomial.isUnit_iff_degree_eq_zero.mpr <|
                        by
                          rw [Polynomial.degree_eq_natDegree]
                          · exact_mod_cast con
                          · rintro rfl
                            exact h_unit (Or.inr (by simpa using hgh.1.symm))
                  · exact Nat.pos_of_ne_zero fun con ↦
                      hgh.2.2 <| Polynomial.isUnit_iff_degree_eq_zero.mpr <|
                        by
                          rw [Polynomial.degree_eq_natDegree]
                          · exact_mod_cast con
                          · rintro rfl
                            exact h_unit (Or.inr (by simpa using hgh.1.symm))
                grind
              exact ⟨g, hg.1, hg.2.1, ht_deg ▸ hg.2.2⟩
          refine ⟨Polynomial.C g.leadingCoeff⁻¹ * g, ?_, ?_, ?_, ?_⟩
          · rw [Polynomial.natDegree_C_mul]
            · simp_all only
            · simp_all only [ne_eq, inv_eq_zero, leadingCoeff_eq_zero]
              obtain ⟨left, right⟩ := hg
              obtain ⟨left_1, right⟩ := right
              apply Aesop.BuiltinRules.not_intro
              intro a
              subst a
              simp_all only [zero_dvd_iff, natDegree_zero, nonpos_iff_eq_zero, one_ne_zero]
          · rw [Polynomial.natDegree_C_mul]
            · simp_all only
            · simp_all only [ne_eq, inv_eq_zero, leadingCoeff_eq_zero]
              obtain ⟨left, right⟩ := hg
              obtain ⟨left_1, right⟩ := right
              apply Aesop.BuiltinRules.not_intro
              intro a
              subst a
              simp_all only [zero_dvd_iff, natDegree_zero, nonpos_iff_eq_zero, one_ne_zero]
          · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul,
              Polynomial.leadingCoeff_C, inv_mul_cancel₀]
            refine Polynomial.leadingCoeff_ne_zero.mpr ?_
            simp_all only [ne_eq]
            obtain ⟨left, right⟩ := hg
            obtain ⟨left_1, right⟩ := right
            apply Aesop.BuiltinRules.not_intro
            intro a
            subst a
            simp_all only [zero_dvd_iff, natDegree_zero, nonpos_iff_eq_zero, one_ne_zero]
          · refine dvd_trans ?_ hg.1
            refine ⟨Polynomial.C g.leadingCoeff, ?_⟩
            rw [mul_right_comm, ← Polynomial.C_mul, inv_mul_cancel₀ (by simp_all only [ne_eq, leadingCoeff_eq_zero]; obtain ⟨left, right⟩ := hg; obtain ⟨left_1, right⟩ := right; apply Aesop.BuiltinRules.not_intro; intro a; subst a; simp_all only [zero_dvd_iff, natDegree_zero, nonpos_iff_eq_zero, one_ne_zero]), Polynomial.C_1, one_mul]

end
