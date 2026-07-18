/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Core.Basic
import InverseGalois.Core.Cyclic
import InverseGalois.Core.Product
import InverseGalois.Groups.D4
import InverseGalois.Groups.A4
import InverseGalois.Groups.A5
import InverseGalois.Groups.D5

/-!
# Small Groups as Inverse Galois Groups

We show that various small groups — in particular all transitive subgroups of `S₄` and `S₅`
that arise as Galois groups of degree 4 and 5 extensions — are inverse Galois groups over `ℚ`.

## Groups of order ≤ 5 (all are inverse Galois)
* Trivial group: `Unit` (already in `Basic.lean`)
* `ℤ/2ℤ`, `ℤ/3ℤ`, `ℤ/5ℤ`: Cyclic groups (already in `Cyclic.lean`)
* `ℤ/4ℤ`: Cyclic (already in `Cyclic.lean`)
* `V₄ ≅ (ℤ/2ℤ) × (ℤ/2ℤ)`: Klein four group — realized by `ℚ(√2, √3)/ℚ`

## Transitive subgroups of `S₄` (degree 4 Galois groups)
* `ℤ/4ℤ`: Cyclic (done)
* `V₄ ≅ (ℤ/2ℤ) × (ℤ/2ℤ)`: Klein four group (order 4)
* `D₄`: Dihedral group of order 8
* `A₄`: Alternating group on 4 elements (order 12)
* `S₄`: Symmetric group on 4 elements (order 24) — see `Symmetric.lean`

## Transitive subgroups of `S₅` (degree 5 Galois groups)
* `ℤ/5ℤ`: Cyclic (done)
* `D₅`: Dihedral group of order 10
* `F₂₀ ≅ ℤ/5ℤ ⋊ ℤ/4ℤ`: Frobenius group of order 20
* `A₅`: Alternating group on 5 elements (order 60)
* `S₅`: Symmetric group on 5 elements (order 120) — see `Symmetric.lean`

## Main results

* `IsInverseGalois.klein_four`: `V₄` is an inverse Galois group
* `IsInverseGalois.dihedral_four`: `D₄` is an inverse Galois group
* `IsInverseGalois.alternating_four`: `A₄` is an inverse Galois group
* `IsInverseGalois.dihedral_five`: `D₅` is an inverse Galois group
* `IsInverseGalois.alternating_five`: `A₅` is an inverse Galois group
-/

open Polynomial IntermediateField Module

noncomputable section

namespace IsInverseGalois

/-!
### V₄ — Klein Four Group

The Klein four group `V₄ ≅ (ℤ/2ℤ) × (ℤ/2ℤ)` is realized as the Galois group of the
biquadratic extension `ℚ(√2, √3)/ℚ`.

The strategy is:
1. Define `K₁ = ℚ(√2)` and `K₂ = ℚ(√3)` as intermediate fields of `AlgebraicClosure ℚ / ℚ`.
2. Show both are Galois of degree 2 over `ℚ`.
3. Show `K₁ ⊓ K₂ = ⊥` (they are linearly disjoint).
4. Apply the disjoint product theorem (`of_disjoint_intermediate_fields`).
5. Conclude `Gal(ℚ(√2, √3) / ℚ) ≅ Gal(ℚ(√2)/ℚ) × Gal(ℚ(√3)/ℚ) ≅ ℤ/2ℤ × ℤ/2ℤ`.
-/

private def p₂ : ℚ[X] := X ^ 2 - C 2
private def p₃ : ℚ[X] := X ^ 2 - C 3

private instance : IsGalois ℚ p₂.SplittingField :=
  { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField
    to_normal := SplittingField.instNormal p₂ }

private instance : IsGalois ℚ p₃.SplittingField :=
  { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField
    to_normal := SplittingField.instNormal p₃ }

/-
`X² - 2` is irreducible over `ℚ`.
-/
private lemma p₂_irreducible : Irreducible p₂ := by
  -- The polynomial $X^2 - 2$ is irreducible over $\mathbb{Q}$ because it has no rational roots.
  have h_no_rational_roots : ¬∃ (q : ℚ), q^2 = 2 := by
    exact fun ⟨ q, hq ⟩ => by apply_fun fun x => x.num at hq; norm_num [ sq, Rat.mul_self_num ] at hq; nlinarith [ show q.num ≤ 1 by nlinarith, show q.num ≥ -1 by nlinarith ] ;
  constructor;
  · exact fun h => absurd ( Polynomial.degree_eq_zero_of_isUnit h ) ( by erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num );
  · intros a b hab
    have h_deg : a.degree + b.degree = 2 := by
      erw [ ← Polynomial.degree_mul, ← hab, Polynomial.degree_X_pow_sub_C ] <;> norm_num;
    by_cases ha : a.degree = 0 <;> by_cases hb : b.degree = 0 <;> simp_all [ Polynomial.isUnit_iff_degree_eq_zero ];
    -- Since $a$ and $b$ are non-constant polynomials with degrees adding up to 2, they must both be linear.
    have h_linear : a.degree = 1 ∧ b.degree = 1 := by
      rw [ Polynomial.degree_eq_natDegree ( by aesop_cat ), Polynomial.degree_eq_natDegree ( by aesop_cat ) ] at * ; norm_cast at * ; omega;
    -- Let $r$ be a root of $a$. Then $r^2 = 2$, � which� contradicts $ �h�_no_rational_roots$.
    obtain ⟨r, hr⟩ : ∃ r : ℚ, a.eval r = 0 := by
      exact Polynomial.exists_root_of_degree_eq_one h_linear.1;
    replace hab := congr_arg ( Polynomial.eval r ) hab; simp_all [ p₂ ] ;
    exact h_no_rational_roots r <| sub_eq_zero.mp hab

/-
`X² - 3` is irreducible over `ℚ`.
-/
private lemma p₃_irreducible : Irreducible p₃ := by
  -- We can use the fact that a polynomial of degree 2 is irreducible if it has no rational roots.
  have h_no_rational_roots : ¬∃ r : ℚ, p₃.eval r = 0 := by
    unfold p₃;
    norm_num [ sub_eq_iff_eq_add ];
    exact fun x hx => by apply_fun fun y => y.num at hx; norm_num [ sq, Rat.mul_self_num ] at hx; nlinarith [ show x.num ≤ 1 by nlinarith, show x.num ≥ -1 by nlinarith ] ;
  constructor;
  · exact fun h => absurd ( Polynomial.degree_eq_zero_of_isUnit h ) ( by erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num );
  · intros a b hab
    have h_deg : a.degree + b.degree = 2 := by
      erw [ ← Polynomial.degree_mul, ← hab, Polynomial.degree_X_pow_sub_C ] <;> norm_num;
    by_cases ha : a.degree = 0 <;> by_cases hb : b.degree = 0 <;> simp_all [ Polynomial.isUnit_iff_degree_eq_zero ];
    -- Since $a$ and $b$ are non-constant polynomials with degrees adding up to 2, they must both be linear.
    have h_linear : a.degree = 1 ∧ b.degree = 1 := by
      rw [ Polynomial.degree_eq_natDegree ( show a ≠ 0 from fun h => by simpa [ h ] using h_no_rational_roots 0 ), Polynomial.degree_eq_natDegree ( show b ≠ 0 from fun h => by simpa [ h ] using h_no_rational_roots 0 ) ] at * ; norm_cast at * ; omega;
    exact h_no_rational_roots ( Classical.choose ( Polynomial.exists_root_of_degree_eq_one h_linear.1 ) ) |>.1 ( Classical.choose_spec ( Polynomial.exists_root_of_degree_eq_one h_linear.1 ) )

/-
The splitting field of `X² - 2` has degree 2 over `ℚ`.
-/
private lemma p₂_finrank : finrank ℚ (p₂.SplittingField) = 2 := by
  -- Let α be a root of � p�₂ in the splitting field.
  obtain ⟨α, hα⟩ : ∃ α : p₂.SplittingField, α ^ 2 = 2 := by
    obtain ⟨α, hα⟩ : ∃ α : p₂.SplittingField, Polynomial.eval α (Polynomial.map (algebraMap ℚ p₂.SplittingField) (X^2 - 2)) = 0 := by
      convert Polynomial.Splits.exists_eval_eq_zero _ _;
      · exact Polynomial.SplittingField.splits _;
      · erw [ Polynomial.degree_map, Polynomial.degree_X_pow_sub_C ] <;> norm_num;
    exact ⟨ α, by simpa [ sub_eq_zero ] using hα ⟩;
  -- Since $p₂$ is irreducible, the degree of the extension $\mathbb{Q}(\alpha)/\mathbb{Q}$ is equal to the degree of $ �p�₂$, which is 2.
  have h_deg : finrank ℚ (↥(IntermediateField.adjoin ℚ {α})) = 2 := by
    -- The minimal polynomial of α over � ℚ� is p₂, which has degree 2.
    have h_minpoly : minpoly ℚ α = p₂ := by
      refine' Eq.symm ( minpoly.eq_of_irreducible_of_monic _ _ _ ) <;> norm_num [ p₂_irreducible ];
      · unfold p₂; simp_all only [aeval_sub, map_pow, aeval_X, aeval_C, eq_ratCast, Rat.cast_ofNat, sub_self];
      · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
    rw [ IntermediateField.adjoin.finrank ];
    · erw [ h_minpoly, Polynomial.natDegree_X_pow_sub_C ];
    · exact ⟨ Polynomial.X ^ 2 - 2, by exact Polynomial.monic_X_pow_sub_C _ two_ne_zero, by simp_all only [eval₂_sub, eval₂_X_pow, eval₂_ofNat, sub_self] ⟩;
  convert h_deg using 1;
  have h_split : Polynomial.IsSplittingField ℚ p₂.SplittingField p₂ := by
    infer_instance;
  have := h_split.adjoin_rootSet;
  rw [ show p₂.rootSet p₂.SplittingField = { α, -α } from ?_ ] at this;
  · rw [ show ( IntermediateField.adjoin ℚ { α } : IntermediateField ℚ p₂.SplittingField ) = ⊤ from ?_ ];
    · simp;
    · rw [ show ( Algebra.adjoin ℚ { α, -α } : Subalgebra ℚ p₂.SplittingField ) = Algebra.adjoin ℚ { α } from ?_ ] at this;
      · grind only [adjoin_eq_top_of_algebra];
      · refine' le_antisymm _ _ <;> norm_num [ Algebra.adjoin_le_iff, Set.insert_subset_iff ];
        exact Algebra.subset_adjoin ( Set.mem_insert _ _ );
  · ext; simp [p₂];
    rw [ Polynomial.mem_rootSet ] ; norm_num [ hα ];
    exact ⟨ fun h => eq_or_eq_neg_of_sq_eq_sq _ _ <| by linear_combination' h.2 - hα, fun h => by rcases h with ( rfl | rfl ) <;> exact ⟨ by exact ne_of_apply_ne ( Polynomial.eval 0 ) <| by norm_num, by linear_combination' hα ⟩ ⟩

/-- The splitting field of `X² - 3` has degree 2 over `ℚ`. -/
private lemma p₃_finrank : finrank ℚ (p₃.SplittingField) = 2 := by
  obtain ⟨α, hα⟩ : ∃ α : p₃.SplittingField, α ^ 2 = 3 := by
    obtain ⟨α, hα⟩ : ∃ α : p₃.SplittingField, Polynomial.eval α (Polynomial.map (algebraMap ℚ p₃.SplittingField) (X^2 - 3)) = 0 := by
      convert Polynomial.Splits.exists_eval_eq_zero _ _
      · exact Polynomial.SplittingField.splits _
      · erw [ Polynomial.degree_map, Polynomial.degree_X_pow_sub_C ] <;> norm_num
    exact ⟨ α, by simpa [ sub_eq_zero ] using hα ⟩
  have h_deg : finrank ℚ (↥(IntermediateField.adjoin ℚ {α})) = 2 := by
    have h_minpoly : minpoly ℚ α = p₃ := by
      refine' Eq.symm ( minpoly.eq_of_irreducible_of_monic _ _ _ ) <;> norm_num [ p₃_irreducible ]
      · unfold p₃; simp_all only [aeval_sub, map_pow, aeval_X, aeval_C, eq_ratCast, Rat.cast_ofNat, sub_self]
      · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num
    rw [ IntermediateField.adjoin.finrank ]
    · erw [ h_minpoly, Polynomial.natDegree_X_pow_sub_C ]
    · exact ⟨ Polynomial.X ^ 2 - 3, by exact Polynomial.monic_X_pow_sub_C _ two_ne_zero, by simp_all only [eval₂_sub, eval₂_X_pow, eval₂_ofNat, sub_self] ⟩
  convert h_deg using 1
  have h_split : Polynomial.IsSplittingField ℚ p₃.SplittingField p₃ := by infer_instance
  have := h_split.adjoin_rootSet
  rw [ show p₃.rootSet p₃.SplittingField = { α, -α } from ?_ ] at this
  · rw [ show ( IntermediateField.adjoin ℚ { α } : IntermediateField ℚ p₃.SplittingField ) = ⊤ from ?_ ]
    · simp
    · rw [ show ( Algebra.adjoin ℚ { α, -α } : Subalgebra ℚ p₃.SplittingField ) = Algebra.adjoin ℚ { α } from ?_ ] at this
      · grind only [adjoin_eq_top_of_algebra]
      · refine' le_antisymm _ _ <;> norm_num [ Algebra.adjoin_le_iff, Set.insert_subset_iff ]
        exact Algebra.subset_adjoin ( Set.mem_insert _ _ )
  · ext; simp [p₃]
    rw [ Polynomial.mem_rootSet ] ; norm_num [ hα ]
    exact ⟨ fun h => eq_or_eq_neg_of_sq_eq_sq _ _ <| by linear_combination' h.2 - hα, fun h => by rcases h with ( rfl | rfl ) <;> exact ⟨ by exact ne_of_apply_ne ( Polynomial.eval 0 ) <| by norm_num, by linear_combination' hα ⟩ ⟩

/-
The finrank of the field range of an algebra embedding equals the finrank of the source.
-/
private lemma fieldRange_finrank {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    (i : L →ₐ[ℚ] AlgebraicClosure ℚ) :
    finrank ℚ i.fieldRange = finrank ℚ L := by
      fapply LinearEquiv.finrank_eq;
      exact ( LinearEquiv.ofInjective ( i.toLinearMap ) ( show Function.Injective i.toLinearMap from i.toRingHom.injective ) ).symm

/-
There is no element `x` in `SplittingField(X² - 2)` such that `x² = 3`.

Proof: Let α be a root of X²-2 in the splitting field, so α² = 2.
The splitting field equals ℚ(α), and every element is of the form a + bα
for a, b ∈ ℚ. If (a + bα)² = 3, then a² + 2b² + 2abα = 3.
Since {1, α} is ℚ-linearly independent, ab = 0 and a² + 2b² = 3.
If b = 0: a² = 3, impossible in ℚ. If a = 0: 2b² = 3, impossible in ℚ.
-/
private lemma no_sq_eq_three_in_p₂_sf :
    ∀ x : p₂.SplittingField, x ^ 2 ≠ algebraMap ℚ _ 3 := by
      obtain ⟨α, hα⟩ : ∃ α : (p₂.SplittingField), α ^ 2 = (algebraMap ℚ p₂.SplittingField) 2 := by
        have := Polynomial.SplittingField.splits ( X ^ 2 - 2 : Polynomial ℚ );
        simp_all [ Polynomial.splits_iff_card_roots ];
        exact Exists.elim ( Multiset.card_pos_iff_exists_mem.mp ( by erw [ this ] ; erw [ Polynomial.natDegree_X_pow_sub_C ] ; norm_num ) ) fun x hx => ⟨ x, by norm_num at hx; linear_combination hx.2 ⟩;
      -- Since {1, α} is-linearly independent �,� we have that α is not in ℚ.
      have h_lin_indep : ∀ (a b : ℚ), a • (1 : p₂.SplittingField) + b • α = 0 → a = 0 ∧ b = 0 := by
        -- Since α is a root of the irreducible polynomial x² - 2, � it� is not in � ℚ�.
        have h_not_in_Q : α ∉ Set.range (algebraMap ℚ p₂.SplittingField) := by
          rintro ⟨ q, hq ⟩;
          norm_num [ ← hq ] at hα;
          exact absurd hα ( by norm_cast; intros h; apply_fun ( fun x => x.num ) at h; norm_num [ sq, Rat.mul_self_num ] at h; nlinarith [ show q.num ≤ 1 by nlinarith, show q.num ≥ -1 by nlinarith ] );
        intro a b h; by_cases hb : b = 0 <;> simp_all [ add_eq_zero_iff_eq_neg, Algebra.smul_def ] ;
        exact h_not_in_Q ( -a / b ) ( by simp [ *, mul_div_cancel_left₀ ] );
      -- Since {1, α �} is a basis for the splitting field over ℚ, any element � x� in the splitting field can be written as a + bα for some a, b ∈.
      have h_basis : ∀ x : p₂.SplittingField, ∃ a b : ℚ, x = a • (1 : p₂.SplittingField) + b • α := by
        -- Since {1, α} � is� a basis for the splitting field over, � any� element x in the splitting field can be written as a linear combination of 1 and α.
        have h_basis : Submodule.span ℚ {1, α} = ⊤ := by
          refine' Submodule.eq_top_of_finrank_eq _;
          rw [ p₂_finrank ];
          convert finrank_span_eq_card ( show LinearIndependent ℚ ( fun i : Fin 2 => if i = 0 then ( 1 : p₂.SplittingField ) else α ) from ?_ ) using 1;
          · congr;
            · congr! 2;
              congr with x ; simp [ Set.mem_range, Fin.exists_fin_two ];
              tauto;
            · exact Set.ext fun x => ⟨ fun hx => by rcases hx with ( rfl | rfl ) <;> [ exact ⟨ 0, rfl ⟩ ; exact ⟨ 1, rfl ⟩ ], fun hx => by rcases hx with ⟨ i, rfl ⟩ ; fin_cases i <;> simp ⟩;
            · exact Set.ext fun x => ⟨ fun hx => by rcases hx with ( rfl | rfl ) <;> [ exact ⟨ 0, rfl ⟩ ; exact ⟨ 1, rfl ⟩ ], fun hx => by rcases hx with ⟨ i, rfl ⟩ ; fin_cases i <;> simp ⟩;
          · rw [ Fintype.linearIndependent_iff ] ; norm_num;
            exact fun g hg => h_lin_indep _ _ <| by simpa [ add_comm ] using hg;
        intro x; replace h_basis := SetLike.ext_iff.mp h_basis x; simp [ Submodule.mem_span_pair ] at h_basis ⊢; tauto;
      intro x hx
      obtain ⟨a, b, hx_eq⟩ := h_basis x
      have h_eq : a^2 + 2 * b^2 = 3 ∧ 2 * a * b = 0 := by
        have h_eq : (a^2 + 2 * b^2) • (1 : p₂.SplittingField) + (2 * a * b) • α = (algebraMap ℚ p₂.SplittingField) 3 := by
          convert hx using 1 ; rw [ hx_eq ] ; simp [mul_assoc, mul_left_comm, pow_two, add_mul, mul_add, Algebra.smul_def] ; ring_nf;
          erw [ hα ] ; norm_num;
        specialize h_lin_indep ( a^2 + 2 * b^2 - 3 ) ( 2 * a * b ) ; simp_all [ sub_eq_iff_eq_add ];
        exact h_lin_indep ( by linear_combination' h_eq );
      by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ ha, hb ] at h_eq ⊢;
      · -- From $2b^2 = 3$, we get $b^2 = \frac{3}{2}$, which is not a rational number, leading to a contradiction.
        have h_not_rational : ¬ ∃ (q : ℚ), q^2 = 3 / 2 := by
          exact fun ⟨ q, hq ⟩ => by apply_fun ( fun x => x.num ) at hq; norm_num [ sq, Rat.mul_self_num ] at hq; nlinarith [ show q.num ≤ 1 by nlinarith, show q.num ≥ -1 by nlinarith ] ;
        grind +qlia;
      · exact absurd h_eq ( by apply_fun ( fun x => x.num ) ; norm_num [ sq, Rat.mul_self_num ] ; intros h; nlinarith [ show a.num ≤ 1 by nlinarith, show a.num ≥ -1 by nlinarith ] )

/-
The images of `ℚ(√2)` and `ℚ(√3)` in the algebraic closure have trivial intersection.

Since both have degree 2 (prime) and are distinct (no element of ℚ(√2) squares to 3),
their intersection has degree dividing 2 but ≠ 2, hence = 1, so it equals ⊥.
-/
private lemma biquadratic_inf_eq_bot :
    ∀ (i₁ : p₂.SplittingField →ₐ[ℚ] AlgebraicClosure ℚ)
      (i₂ : p₃.SplittingField →ₐ[ℚ] AlgebraicClosure ℚ),
    i₁.fieldRange ⊓ i₂.fieldRange = ⊥ := by
      intro i₁ i₂
      have h_finrank : finrank ℚ (↥(i₁.fieldRange ⊓ i₂.fieldRange)) ∣ 2 := by
        convert IntermediateField.finrank_dvd_of_le_right ( show i₁.fieldRange ⊓ i₂.fieldRange ≤ i₁.fieldRange from inf_le_left ) using 1;
        rw [ fieldRange_finrank, p₂_finrank ];
      by_cases h : finrank ℚ (↥(i₁.fieldRange ⊓ i₂.fieldRange)) = 2;
      · have h_eq : i₁.fieldRange = i₂.fieldRange := by
          have h_eq : i₁.fieldRange ⊓ i₂.fieldRange = i₁.fieldRange := by
            apply_rules [ IntermediateField.eq_of_le_of_finrank_eq ];
            · exact inf_le_left;
            · rw [ h, fieldRange_finrank i₁, p₂_finrank ];
            · have h_finrank_i₁ : finrank ℚ (↥i₁.fieldRange) = 2 := by
                convert p₂_finrank using 1;
                convert fieldRange_finrank i₁;
              exact FiniteDimensional.of_finrank_pos ( by linarith );
          have h_eq : i₁.fieldRange ≤ i₂.fieldRange := by
            exact h_eq ▸ inf_le_right;
          have h_eq : Module.finrank ℚ (↥i₁.fieldRange) = Module.finrank ℚ (↥i₂.fieldRange) := by
            rw [ fieldRange_finrank, fieldRange_finrank, p₂_finrank, p₃_finrank ];
          apply_rules [ IntermediateField.eq_of_le_of_finrank_eq ];
          have h_finrank : Module.finrank ℚ (↥i₂.fieldRange) = 2 := by
            convert p₃_finrank using 1;
            convert fieldRange_finrank i₂ using 1;
          exact FiniteDimensional.of_finrank_pos ( by linarith );
        obtain ⟨β, hβ⟩ : ∃ β : p₃.SplittingField, β ^ 2 = algebraMap ℚ _ 3 := by
          have := Polynomial.SplittingField.splits p₃;
          unfold p₃ at this; simp_all [ Polynomial.splits_iff_card_roots ] ;
          obtain ⟨ β, hβ ⟩ := Multiset.card_pos_iff_exists_mem.mp ( by linarith ) ; use β; simp_all [ sub_eq_iff_eq_add ] ;
        have h_contradiction : ∃ γ : p₂.SplittingField, γ ^ 2 = algebraMap ℚ _ 3 := by
          have h_contradiction : ∃ γ : p₂.SplittingField, i₁ γ = i₂ β := by
            replace h_eq := SetLike.ext_iff.mp h_eq ( i₂ β ) ; simp_all only [dvd_refl, eq_ratCast, Rat.cast_ofNat, AlgHom.mem_fieldRange, exists_apply_eq_apply, iff_true];
          obtain ⟨γ, hγ⟩ := h_contradiction
          have h_contradiction : i₁ (γ ^ 2) = i₁ (algebraMap ℚ _ 3) := by
            convert congr_arg ( fun x => i₂ x ) hβ using 1 <;> simp [ hγ ];
            exact map_natCast i₁ 3 ▸ map_natCast i₂ 3 ▸ rfl;
          exact ⟨ γ, i₁.injective h_contradiction ⟩;
        exact False.elim <| no_sq_eq_three_in_p₂_sf _ h_contradiction.choose_spec;
      · have := Nat.le_of_dvd ( by decide ) h_finrank; interval_cases _ : finrank ℚ ( ↥ ( i₁.fieldRange ⊓ i₂.fieldRange ) ) <;> simp_all ;

/-
The Galois group of `ℚ(√2)/ℚ` is isomorphic to `Multiplicative (ℤ/2ℤ)`.
-/
private lemma gal_p₂_iso :
    Nonempty (Gal(p₂.SplittingField / ℚ) ≃* Multiplicative (ZMod 2)) := by
      -- Since the Galois group has order 2, it is isomorphic� to� the cyclic group of order 2.
      have h_iso : Nonempty (Gal(p₂.SplittingField/ℚ) ≃* Multiplicative (ZMod (Nat.card Gal(p₂.SplittingField/ℚ)))) := by
        refine' ⟨ _ ⟩;
        have h_iso : IsCyclic Gal(p₂.SplittingField/ℚ) := by
          have h_iso : Nat.card Gal(p₂.SplittingField/ℚ) = 2 := by
            rw [ IsGalois.card_aut_eq_finrank ] ; norm_num [ p₂_finrank ];
          exact isCyclic_of_prime_card h_iso;
        exact (zmodCyclicMulEquiv h_iso).symm;
      convert h_iso;
      rw [ IsGalois.card_aut_eq_finrank, p₂_finrank ]

/-
The Galois group of `ℚ(√3)/ℚ` is isomorphic to `Multiplicative (ℤ/2ℤ)`.
-/
private lemma gal_p₃_iso :
    Nonempty (Gal(p₃.SplittingField / ℚ) ≃* Multiplicative (ZMod 2)) := by
      -- Since the Galois group is a finite� group� of order 2, � it� must be isomorphic to Z/2Z.
      have h_iso : Nonempty (Gal(p₃.SplittingField / ℚ) ≃* Multiplicative (ZMod (Nat.card Gal(p₃.SplittingField / ℚ)))) := by
        refine' ⟨ _ ⟩;
        have h_iso : IsCyclic Gal(p₃.SplittingField / ℚ) := by
          have h_iso : Nat.card Gal(p₃.SplittingField / ℚ) = 2 := by
            rw [ IsGalois.card_aut_eq_finrank ];
            convert p₃_finrank;
          exact isCyclic_of_prime_card h_iso;
        exact (zmodCyclicMulEquiv h_iso).symm;
      have h_card : Nat.card Gal(p₃.SplittingField / ℚ) = 2 := by
        have := IsGalois.card_aut_eq_finrank ℚ ( p₃.SplittingField );
        exact this.trans ( p₃_finrank );
      grind

/-- The Klein four group `V₄ ≅ Multiplicative (ℤ/2ℤ) × Multiplicative (ℤ/2ℤ)` is an inverse
Galois group, realized by the biquadratic extension `ℚ(√2, √3)/ℚ`. -/
theorem klein_four :
    IsInverseGalois (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  -- Embed splitting fields into algebraic closure
  let i₁ : p₂.SplittingField →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let i₂ : p₃.SplittingField →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let K₁ := i₁.fieldRange
  let K₂ := i₂.fieldRange
  -- Get Galois instances
  obtain ⟨hg₁, ⟨ψ₁⟩⟩ := galois_image_in_algClosure p₂.SplittingField i₁
  obtain ⟨hg₂, ⟨ψ₂⟩⟩ := galois_image_in_algClosure p₃.SplittingField i₂
  -- FiniteDimensional instances
  haveI : FiniteDimensional ℚ K₁ := FiniteDimensional.of_injective
    (AlgEquiv.ofInjectiveField i₁).symm.toLinearMap (AlgEquiv.ofInjectiveField i₁).symm.injective
  haveI : FiniteDimensional ℚ K₂ := FiniteDimensional.of_injective
    (AlgEquiv.ofInjectiveField i₂).symm.toLinearMap (AlgEquiv.ofInjectiveField i₂).symm.injective
  -- Get Galois isomorphisms
  obtain ⟨e₁⟩ := gal_p₂_iso
  obtain ⟨e₂⟩ := gal_p₃_iso
  -- Apply the disjoint product theorem
  exact of_disjoint_intermediate_fields K₁ K₂
    (biquadratic_inf_eq_bot i₁ i₂)
    (ψ₁.symm.trans e₁) (ψ₂.symm.trans e₂)

end IsInverseGalois

end
