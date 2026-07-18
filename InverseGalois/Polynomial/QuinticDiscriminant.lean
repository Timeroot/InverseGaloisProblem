/-
# Discriminant argument for A₅

This file proves that the Galois group of X⁵+20X+16 over ℚ is not S₅,
by showing all Galois automorphisms are even permutations of the roots.
-/
import Mathlib
import InverseGalois.Polynomial.PowerSums

open Polynomial Matrix Finset

noncomputable section

set_option maxHeartbeats 800000

/-!
## Part 1: Pure algebra — Vandermonde and permutation signs
-/

/-- The Vandermonde matrix of `v ∘ σ` is the Vandermonde matrix of `v` with rows permuted by `σ`. -/
lemma vandermonde_comp_perm {n : ℕ} {R : Type*} [CommRing R]
    (v : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    Matrix.vandermonde (v ∘ σ) = (Matrix.vandermonde v).submatrix σ id := by
  ext i j; simp [vandermonde_apply]

/-- Permuting the inputs of a Vandermonde determinant multiplies it by the sign. -/
lemma det_vandermonde_perm {n : ℕ} {R : Type*} [CommRing R]
    (v : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    (Matrix.vandermonde (v ∘ σ)).det = ↑↑(Equiv.Perm.sign σ) * (Matrix.vandermonde v).det := by
  rw [vandermonde_comp_perm, Matrix.det_permute]

/-- The product ∏_{i<j}(v(σj)-v(σi)) = sign(σ) * ∏_{i<j}(vj-vi). -/
lemma prod_sub_perm_eq_sign_mul {n : ℕ} {R : Type*} [CommRing R]
    (v : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    ∏ i : Fin n, ∏ j ∈ Ioi i, (v (σ j) - v (σ i)) =
    ↑↑(Equiv.Perm.sign σ) * ∏ i : Fin n, ∏ j ∈ Ioi i, (v j - v i) := by
  have h1 := det_vandermonde_perm v σ
  rw [Matrix.det_vandermonde, Matrix.det_vandermonde] at h1
  exact h1

/-
In a char 0 domain, x² = c² implies x = c or x = -c.
-/
lemma sq_eq_sq_of_charZero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {x c : R} (h : x ^ 2 = c ^ 2) : x = c ∨ x = -c := by
      exact eq_or_eq_neg_of_sq_eq_sq _ _ h

/-!
## Part 2: The polynomial and its properties
-/

private abbrev f_poly : ℚ[X] := X ^ 5 + C 20 * X + C 16

private lemma f_poly_ne_zero : f_poly ≠ 0 :=
  ne_of_apply_ne (Polynomial.eval 0) (by norm_num [f_poly])

private lemma f_poly_natDegree : f_poly.natDegree = 5 := by
  erw [Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num

private lemma f_poly_separable : f_poly.Separable := by
  -- Compute the derivative of $f_poly$.
  set f_poly' : ℚ[X] := Polynomial.derivative f_poly;
  have h_deriv : f_poly' = 5 * Polynomial.X ^ 4 + 20 := by
    simp +zetaDelta at *;
    erw [ show ( C 4 + 1 : Polynomial ℚ ) = 5 by exact Polynomial.funext fun x => by norm_num ] ; norm_cast;
  -- Since $f$ and $f'$ have no common roots, they are coprime.
  have h_coprime : ∀ r : ℂ, Polynomial.eval r (Polynomial.map (algebraMap ℚ ℂ) f_poly) = 0 → Polynomial.eval r (Polynomial.map (algebraMap ℚ ℂ) f_poly') ≠ 0 := by
    intros r hr; by_contra h_contra; simp_all [ Polynomial.eval_map ] ;
    grind +ring;
  apply isCoprime_of_dvd;
  · exact not_and_of_not_left _ f_poly_ne_zero;
  · intros z hz hz' hz'' hz'''; contrapose! h_coprime;
    obtain ⟨ r, hr ⟩ := Complex.exists_root ( show Polynomial.degree ( Polynomial.map ( algebraMap ℚ ℂ ) z ) > 0 from by erw [ Polynomial.degree_map ] ; exact lt_of_not_ge fun h => hz <| Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' => by simp_all only [derivative_add, derivative_X_pow_succ, Nat.cast_ofNat, map_add, map_one, derivative_mul, derivative_C,
      zero_mul, derivative_X, mul_one, zero_add, add_zero, mem_nonunits_iff, ne_eq, Nat.WithBot.lt_zero_iff,
      degree_eq_bot, f_poly'] ) ; use r; have := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero ( Polynomial.map_dvd ( algebraMap ℚ ℂ ) hz'' ) hr; have := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero ( Polynomial.map_dvd ( algebraMap ℚ ℂ ) hz''' ) hr; simp_all only [derivative_add, derivative_X_pow_succ, Nat.cast_ofNat, map_add, map_one, derivative_mul, derivative_C,
      zero_mul, derivative_X, mul_one, zero_add, add_zero, mem_nonunits_iff, ne_eq, IsRoot.def, eval_map_algebraMap,
      Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_mul, map_C, eq_ratCast, Rat.cast_ofNat, eval_add,
      eval_pow, eval_X, eval_mul, eval_C, Polynomial.map_ofNat, eval_ofNat, and_self, f_poly'];

/-!
## Part 3: The discriminant computation
-/

/-
The discriminant value: ∏_{i<j}(r_j - r_i)² = 32000² in the splitting field
-/
private lemma disc_value (v : Fin 5 ≃ (f_poly.rootSet f_poly.SplittingField)) :
    (∏ i : Fin 5, ∏ j ∈ Ioi i,
      ((v j : f_poly.SplittingField) - (v i : f_poly.SplittingField))) ^ 2 =
    algebraMap ℚ _ (32000 ^ 2) := by
      -- By definition of $v$, we know that $v$ is an equivalence between $Fin 5$ and the roots of $f_poly$ in its splitting field.
      have hv : (f_poly.map (algebraMap ℚ (f_poly.SplittingField))).roots = Multiset.map (fun i : Fin 5 => (v i : f_poly.SplittingField)) (Finset.univ.val) := by
        have hv : (f_poly.map (algebraMap ℚ (f_poly.SplittingField))).roots = Multiset.map (fun x => x) (Multiset.map (fun x => (x : f_poly.SplittingField)) (f_poly.rootSet f_poly.SplittingField).toFinset.val) := by
          have h_distinct : Multiset.Nodup (Polynomial.map (algebraMap ℚ (f_poly.SplittingField)) f_poly).roots := by
            convert Polynomial.nodup_roots _;
            exact Polynomial.Separable.map f_poly_separable;
          norm_num +zetaDelta at *;
          unfold Polynomial.rootSet; norm_num;
          rw [ Polynomial.aroots_def ] ; norm_num;
          grind only [Multiset.dedup_eq_self];
        have hv : Multiset.map (fun x => (x : f_poly.SplittingField)) (f_poly.rootSet f_poly.SplittingField).toFinset.val = Multiset.map (fun x => (x : f_poly.SplittingField)) (Multiset.map (fun i : Fin 5 => (v i : f_poly.SplittingField)) (Finset.univ.val)) := by
          refine' congr_arg _ _;
          refine' Eq.symm _;
          convert Multiset.map_univ_val_equiv v using 1;
          constructor <;> intro h;
          · exact Multiset.map_univ_val_equiv v;
          · convert congr_arg ( Multiset.map ( fun x : f_poly.rootSet f_poly.SplittingField => ( x : f_poly.SplittingField ) ) ) h using 1;
        simp_all only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_mul, map_C, eq_ratCast, Rat.cast_ofNat,
      Fin.univ_val_map, List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc,
      List.ofFn_zero, Multiset.map_coe, List.map_cons, List.map_nil, Multiset.map_id'];
      -- By definition of $v$, we know that $v$ is an equivalence between $Fin 5$ and the roots of $f_poly$ in its splitting field. Therefore, we can write $f_poly$ as $\prod_{i=0}^{4} (X - v_i)$.
      have h_factor : f_poly.map (algebraMap ℚ (f_poly.SplittingField)) = ∏ i : Fin 5, (Polynomial.X - Polynomial.C (v i : f_poly.SplittingField)) := by
        convert Polynomial.Splits.eq_prod_roots _ using 1;
        all_goals try infer_instance;
        · erw [ Polynomial.leadingCoeff_map, Polynomial.leadingCoeff, Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num [ Polynomial.coeff_X, Polynomial.coeff_C ];
          convert congr_arg ( Multiset.prod ∘ Multiset.map ( fun x => Polynomial.X - Polynomial.C x ) ) hv.symm using 1;
          unfold f_poly; norm_num;
        · exact Polynomial.SplittingField.splits _;
      -- By Vieta's formulas, we know that the sum of the roots of $f_poly$ is zero.
      have h_vieta_sum : ∑ i : Fin 5, (v i : f_poly.SplittingField) ^ 0 = 5 ∧ ∑ i : Fin 5, (v i : f_poly.SplittingField) ^ 1 = 0 ∧ ∑ i : Fin 5, (v i : f_poly.SplittingField) ^ 2 = 0 ∧ ∑ i : Fin 5, (v i : f_poly.SplittingField) ^ 3 = 0 ∧ ∑ i : Fin 5, (v i : f_poly.SplittingField) ^ 4 = -80 := by
        simp_all [ Fin.prod_univ_five, Polynomial.eval_prod ];
        simp_all [ Fin.sum_univ_five ];
        have h₁ := congr_arg ( Polynomial.eval 0 ) h_factor; have h₂ := congr_arg ( Polynomial.eval 1 ) h_factor; have h₃ := congr_arg ( Polynomial.eval ( -1 ) ) h_factor; have h₄ := congr_arg ( Polynomial.eval ( -2 ) ) h_factor; have h₅ := congr_arg ( Polynomial.eval 2 ) h_factor; norm_num at h₁ h₂ h₃ h₄ h₅;
        grind +ring;
      -- By Vieta's formulas, we know that the sum of the products of the roots taken two at a time is zero.
      have h_vieta_sum2 : ∑ i : Fin 5, (v i : f_poly.SplittingField) ^ 5 = -80 ∧ ∑ i : Fin 5, (v i : f_poly.SplittingField) ^ 6 = 0 ∧ ∑ i : Fin 5, (v i : f_poly.SplittingField) ^ 7 = 0 ∧ ∑ i : Fin 5, (v i : f_poly.SplittingField) ^ 8 = 1600 := by
        have h_vieta_sum2 : ∀ i : Fin 5, (v i : f_poly.SplittingField) ^ 5 = -20 * (v i : f_poly.SplittingField) - 16 := by
          intro i
          have h_root : (v i : f_poly.SplittingField) ^ 5 + 20 * (v i : f_poly.SplittingField) + 16 = 0 := by
            replace h_factor := congr_arg ( Polynomial.eval ( v i : f_poly.SplittingField ) ) h_factor ; simp_all [ Finset.prod_eq_prod_diff_singleton_mul ( Finset.mem_univ i ) ] ;
          linear_combination' h_root;
        simp_all [ Fin.sum_univ_succ ];
        grind;
      convert gram_det_value ( fun i => ( v i : f_poly.SplittingField ) ) _ _ _ _ _ _ _ _ _ using 1 <;> norm_num [ h_vieta_sum, h_vieta_sum2 ];
      · convert vandermonde_det_sq ( fun i => ( v i : f_poly.SplittingField ) ) using 1;
        rw [ Matrix.det_vandermonde ];
      · simpa using h_vieta_sum.2.1

/-
The discriminant element is nonzero
-/
private lemma disc_elem_ne_zero (v : Fin 5 ≃ (f_poly.rootSet f_poly.SplittingField)) :
    (∏ i : Fin 5, ∏ j ∈ Ioi i,
      ((v j : f_poly.SplittingField) - (v i : f_poly.SplittingField))) ≠ 0 := by
        simp [ Finset.prod_eq_zero_iff, sub_eq_zero ];
        exact fun i j hij => v.injective.ne hij.ne'

/-!
## Part 4: Connecting Galois to the sign
-/

private lemma rootSet_card :
    Fintype.card (f_poly.rootSet f_poly.SplittingField) = 5 := by
  rw [Polynomial.card_rootSet_eq_natDegree f_poly_separable
    (SplittingField.splits f_poly), f_poly_natDegree]

-- A bijection Fin 5 ≃ rootSet
private def rootEnum : Fin 5 ≃ (f_poly.rootSet f_poly.SplittingField) :=
  Fintype.equivFinOfCardEq rootSet_card |>.symm

/-!
## Part 5: Main result
-/

/-
The Galois group of X⁵+20X+16 is not S₅ (has order ≠ 120).
-/
theorem card_gal_f_poly_ne_120 :
    Nat.card f_poly.Gal ≠ 120 := by
  -- Set up: we work with the roots in the splitting field
  set K := f_poly.SplittingField
  set v := rootEnum
  set δ := ∏ i : Fin 5, ∏ j ∈ Ioi i,
    ((v j : K) - (v i : K))
  -- Step 1: δ² = 32000² and δ ≠ 0
  have hδ_sq : δ ^ 2 = algebraMap ℚ K (32000 ^ 2) := disc_value v
  have hδ_ne : δ ≠ 0 := disc_elem_ne_zero v
  -- Step 2: δ = ±32000 (in ℚ, via algebraMap)
  have hδ_val : δ = algebraMap ℚ K 32000 ∨ δ = algebraMap ℚ K (-32000) := by
    have := sq_eq_sq_of_charZero (R := K) (x := δ) (c := algebraMap ℚ K 32000)
      (by rw [hδ_sq, map_pow])
    rcases this with h | h
    · left; exact h
    · right; rw [h, map_neg]
  -- Step 3: Every Galois automorphism fixes δ (since δ ∈ ℚ)
  -- and σ(δ) = sign(galActionHom σ) · δ
  -- Therefore sign(galActionHom σ) = 1 for all σ
  -- This means |image of galActionHom| ≤ |A₅| = 60
  -- So |Gal| ≤ 60 ≠ 120
  -- Define the permutation π induced by σ on Fin 5.
  have h_perm : ∀ σ : f_poly.Gal, ∃ π : Equiv.Perm (Fin 5), ∀ i : Fin 5, σ (v i : f_poly.SplittingField) = v (π i) := by
    intro σ
    have h_perm : ∀ i : Fin 5, σ (v i : f_poly.SplittingField) ∈ f_poly.rootSet f_poly.SplittingField := by
      simp [ Polynomial.mem_rootSet ];
      intro i
      have h_root : (v i : f_poly.SplittingField) ^ 5 + 20 * (v i : f_poly.SplittingField) + 16 = 0 := by
        have := Polynomial.mem_rootSet.mp ( v i |>.2 );
        convert this.2 using 1 ; norm_num [ f_poly ];
      convert congr_arg ( σ : f_poly.SplittingField → f_poly.SplittingField ) h_root using 1 ; norm_num [ f_poly ];
      erw [ σ.commutes, σ.commutes ] ; norm_num;
      exact fun _ => ne_of_apply_ne ( Polynomial.eval 0 ) ( by norm_num );
    exact ⟨ Equiv.ofBijective ( fun i => v.symm ⟨ σ ( v i ), h_perm i ⟩ ) ( Finite.injective_iff_bijective.mp ( fun i j hij => by simpa [ v.injective.eq_iff ] using hij ) ), fun i => by simp ⟩;
  choose π hπ using h_perm;
  -- Since $\sigma(\delta) = \delta$ for any $\sigma \in \text{Gal}$, we have $\text{sign}(\pi) = 1$.
  have h_sign : ∀ σ : f_poly.Gal, Equiv.Perm.sign (π σ) = 1 := by
    intro σ
    have h_sigma_delta : σ δ = Equiv.Perm.sign (π σ) * δ := by
      convert prod_sub_perm_eq_sign_mul ( fun i => ( v i : f_poly.SplittingField ) ) ( π σ ) using 1;
      erw [ map_prod, Finset.prod_congr rfl ] ; intros ; erw [ map_prod, Finset.prod_congr rfl ] ; intros ; simp_all only [eq_ratCast, Rat.cast_pow, Rat.cast_ofNat, ne_eq, Rat.cast_neg, mem_univ, mem_Ioi, map_sub, K, δ, v];
    cases hδ_val <;> simp_all [ Algebra.smul_def ];
    · erw [ map_natCast ] at h_sigma_delta ; norm_num at h_sigma_delta;
      exact h_sigma_delta;
    · erw [ map_natCast ] at h_sigma_delta ; norm_num at h_sigma_delta ; cases' Int.units_eq_one_or ( Equiv.Perm.sign ( π σ ) ) with h h <;> simp_all;
  -- Since $\pi$ is injective, the image of $\pi$ is a subgroup of $A_5$.
  have h_image : Function.Injective π := by
    intros σ τ h_eq
    have h_eq_roots : ∀ i : Fin 5, σ (v i : f_poly.SplittingField) = τ (v i : f_poly.SplittingField) := by
      grind;
    ext x;
    convert h_eq_roots ( v.symm ⟨ x, by assumption ⟩ ) using 1 <;> simp [ h_eq ];
  have h_image_card : Nat.card (Set.range π) ≤ Nat.card {σ : Equiv.Perm (Fin 5) | Equiv.Perm.sign σ = 1} := by
    apply_rules [ Nat.card_mono ];
    · exact Set.toFinite _;
    · exact Set.range_subset_iff.mpr h_sign;
  rw [ Nat.card_range_of_injective h_image ] at h_image_card;
  exact ne_of_lt ( lt_of_le_of_lt h_image_card ( by rw [ Nat.card_eq_fintype_card ] ; native_decide ) )

end
