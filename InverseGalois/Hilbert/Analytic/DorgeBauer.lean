/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.IntegralModelExists
import InverseGalois.Resolvent.ResolventConstruction
import InverseGalois.Hilbert.Analytic.SmoothRootBranches
import InverseGalois.Hilbert.Analytic.SmoothSeparableReduction
import InverseGalois.NumberTheory.IntegerPointsSublinear

/-!
# Dörge–Bauer Infrastructure for Hilbert's Irreducibility Theorem

This file develops the key algebraic and analytic infrastructure needed for the
Dörge–Bauer proof of Hilbert's Irreducibility Theorem (HIT).

## Main results

### Algebraic infrastructure
- `irreducible_over_fractionRing`: If `f ∈ R[X]` is monic and irreducible, then `f` is
  irreducible over `Frac(R)[X]`.
- `Polynomial.Monic.coprime_of_irreducible`: An irreducible polynomial over a field is
  coprime with any nonzero polynomial of strictly smaller degree.
- `monic_int_factor_of_monic_int_poly`: Monic factors of monic integer polynomials have
  integer coefficients (Gauss's lemma for ℤ[X]).

### Root and coefficient bounds
- `cauchy_root_bound`: Every root of a monic polynomial satisfies
  `‖α‖ ≤ 1 + ∑ᵢ ‖aᵢ‖` (Cauchy's bound).
- `factor_coeff_bound`: Coefficients of monic factors are bounded by
  binomial coefficients times the root bound.

### Counting
- `int_points_on_poly_curve_bound`: The number of integer points on a polynomial curve
  is bounded by the degree.
- `bad_specializations_bound`: The Dörge estimate for reducible specializations.

## References

* Dörge, K. "Einfacher Beweis des Hilbertschen Irreduzibilitätssatzes", 1927
* Serre, J.-P. "Topics in Galois Theory", 2008, Chapter 3
-/

open Polynomial

open ResolventConstruction

noncomputable section

/-!
## Section 1: Gauss's Lemma — Irreducibility Transfer

Key results for transferring irreducibility between `R[X]` and `Frac(R)[X]`.
-/

/-- A monic irreducible polynomial over a GCD domain remains irreducible over the
fraction field. This is a consequence of Gauss's lemma: monic polynomials are primitive,
and primitive irreducible polynomials remain irreducible over the fraction field. -/
lemma irreducible_map_fractionRing {R : Type*} [CommRing R] [IsDomain R]
    [NormalizedGCDMonoid R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {f : Polynomial R} (hf_monic : f.Monic) (hf_irr : Irreducible f) :
    Irreducible (f.map (algebraMap R K)) := by
  exact (hf_monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map).mp hf_irr

/-- Over `ℚ[T]`, a monic irreducible polynomial `f ∈ ℚ[T][X]` remains irreducible when
viewed over `ℚ(T)[X]`. Here `ℚ(T) = FractionRing(ℚ[T])`.

This is the Gauss lemma in the specific form needed for HIT: the bivariate polynomial
`f(T, X)`, irreducible in `ℚ[T, X] = ℚ[T][X]`, remains irreducible when we allow
the `T`-coefficients to be rational functions. -/
lemma irreducible_over_ratFunc
    {f : Polynomial (Polynomial ℚ)} (hf_monic : f.Monic) (hf_irr : Irreducible f) :
    Irreducible (f.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))) := by
  exact irreducible_map_fractionRing hf_monic hf_irr

/-!
## Section 2: Coprimality from Irreducibility

An irreducible polynomial over a field is coprime with any polynomial of strictly
smaller degree (that is nonzero).
-/

/-
An irreducible polynomial over a field is coprime with any nonzero polynomial of
strictly smaller degree. This is because an irreducible polynomial in a PID is prime,
and a prime cannot divide a nonzero polynomial of smaller degree.
-/
lemma Polynomial.Monic.isCoprime_of_irreducible_of_natDegree_lt {K : Type*} [Field K]
    {f g : Polynomial K} (hf_irr : Irreducible f) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree < f.natDegree) :
    IsCoprime f g := by
  refine hf_irr.coprime_iff_not_dvd.2 fun h ↦ ?_
  exact Nat.not_lt_of_ge (Polynomial.natDegree_le_of_dvd h hg_ne) hdeg

/-
Consequence: the resultant of an irreducible polynomial with a nonzero polynomial
of strictly smaller degree is nonzero.
-/
lemma Polynomial.resultant_ne_zero_of_irreducible {K : Type*} [Field K]
    {f g : Polynomial K} (hf_irr : Irreducible f) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree < f.natDegree) :
    Polynomial.resultant f g ≠ 0 := by
  have := Polynomial.Monic.isCoprime_of_irreducible_of_natDegree_lt hf_irr hg_ne hdeg
  obtain ⟨a, b, h⟩ := this
  contrapose! h
  rw [Polynomial.resultant_eq_zero_iff] at h
  exact fun h' ↦ h.2 ⟨a, b, h'⟩

/-!
## Section 3: Integer Factors of Monic Integer Polynomials (Gauss's Lemma for ℤ[X])

If `f ∈ ℤ[X]` is monic and `f = g · h` in `ℚ[X]` with `g, h` monic,
then `g, h ∈ ℤ[X]`.
-/

/-
A monic polynomial over ℤ that is a product of two monic polynomials over ℚ
must have both factors in ℤ[X]. This follows from Gauss's lemma: the product of
primitive polynomials is primitive, and monic polynomials are primitive.
-/
lemma monic_int_factor_of_monic_int_dvd {f : Polynomial ℤ} {g : Polynomial ℚ}
    (hf_monic : f.Monic)
    (hg_monic : g.Monic)
    (hg_dvd : g ∣ f.map (Int.castRingHom ℚ)) :
    ∃ g' : Polynomial ℤ, g'.Monic ∧ g'.map (Int.castRingHom ℚ) = g := by
  -- By Gauss's Lemma, since `g` is monic and divides `f` in `ℚ[X]`, there is a monic `g' ∈ ℤ[X]` with `g' = g`.
  obtain ⟨g', hg', hg'_monic⟩ : ∃ g' : Polynomial ℤ, g'.Monic ∧ g = g'.map (Int.castRingHom ℚ) := by
    have h_intg : ∀ c ∈ g.support, IsIntegral ℤ (g.coeff c) :=
      fun c _ ↦ isIntegral_coeff_of_dvd f g hf_monic hg_monic hg_dvd c
    have h_alg_int : ∀ c ∈ g.support, ∃ z : ℤ, g.coeff c = z := by
      intro c hc
      obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp (h_intg c hc)
      use z
      simp_all
    choose! z hz using h_alg_int
    refine ⟨∑ c ∈ g.support, z c • Polynomial.X ^ c, ?_, ?_⟩
    · rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some]
      any_goals exact g.natDegree
      · simp_all [Polynomial.Monic.def, Polynomial.leadingCoeff, Polynomial.natDegree]
        exact_mod_cast hz _ (by simp_all) |>.symm.trans hg_monic
      · rw [Polynomial.degree_eq_of_le_of_coeff_ne_zero] <;> norm_num
        · exact le_trans (Polynomial.degree_sum_le _ _)
            (Finset.sup_le fun x hx ↦ Polynomial.degree_C_mul_X_pow_le _ _ |> le_trans
              <| WithBot.coe_le_coe.mpr <| Polynomial.le_natDegree_of_mem_supp _ hx)
        · refine ⟨hg_monic.ne_zero, ?_⟩
          specialize hz (Polynomial.natDegree g)
          simp_all only [mem_support_iff, ne_eq, coeff_natDegree, Monic.leadingCoeff, one_ne_zero, not_false_eq_true,
            forall_const]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [Int.cast_zero, one_ne_zero]
    · ext
      simp_all only [mem_support_iff, ne_eq, zsmul_eq_mul, coeff_map, finset_sum_coeff, coeff_intCast_mul, Int.cast_eq,
        coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, ite_not, eq_intCast, Int.cast_ite, Int.cast_zero]
      split
      next h => simp_all only
      next h =>
        apply hz
        simp_all only [not_false_eq_true]
  tauto

/-!
## Section 4: Root Bounds (Cauchy's Bound)

Every root of a monic polynomial `p(X) = Xⁿ + aₙ₋₁Xⁿ⁻¹ + ⋯ + a₀` over ℂ satisfies
`‖α‖ ≤ 1 + ∑ᵢ ‖aᵢ‖`.
-/

/-
**Cauchy's root bound**: Every root of a monic polynomial `p` over ℂ satisfies
`‖α‖ ≤ 1 + ∑ᵢ ‖p.coeff i‖` where the sum is over non-leading coefficients.
-/
lemma cauchy_root_bound {p : Polynomial ℂ} (hp : p.Monic) {α : ℂ} (hα : p.IsRoot α) :
    ‖α‖ ≤ 1 + ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ := by
  by_cases hα_le_one : ‖α‖ ≤ 1
  · exact le_add_of_le_of_nonneg hα_le_one <| Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  · -- Since ‖α‖ > 1, we can divide both sides of the inequality by ‖α‖^{n-1} > 0: ‖α‖ ≤ ∑ᵢ ‖aᵢ‖ ≤ 1 + ∑ᵢ ‖aᵢ‖.
    have h_div : ‖α‖ ^ p.natDegree ≤ (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) * ‖α‖ ^ (p.natDegree - 1) := by
      have h_eq : ‖α‖ ^ p.natDegree = ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * α ^ i‖ := by
        simp_all [Polynomial.eval_eq_sum_range]
        simp_all [Finset.sum_range_succ]
        rw [eq_neg_of_add_eq_zero_left hα, norm_neg, norm_pow]
      rw [h_eq]
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi ↦ ?_
      simpa [abs_mul] using mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith) (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi)))
        (by positivity)
    rcases n : p.natDegree with (_ | n) <;> simp_all [pow_succ']
    nlinarith [pow_pos (zero_lt_one.trans hα_le_one) ‹_›]

/-
A simpler form of Cauchy's bound using the maximum coefficient.
-/
lemma cauchy_root_bound_max {p : Polynomial ℂ} (hp : p.Monic) {α : ℂ} (hα : p.IsRoot α)
    (_hd : 1 ≤ p.natDegree)
    {B : ℝ} (hB : ∀ i, i < p.natDegree → ‖p.coeff i‖ ≤ B) :
    ‖α‖ ≤ 1 + p.natDegree * B := by
  -- Apply Cauchy's bound to get ‖α‖ ≤ 1 + ∑ i ∈ range n, ‖p.coeff i‖.
  have h_cauchy : ‖α‖ ≤ 1 + ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ := by
    exact cauchy_root_bound hp hα
  exact h_cauchy.trans
    (by simpa using Finset.sum_le_sum fun i (hi : i ∈ Finset.range p.natDegree) ↦ hB i (Finset.mem_range.mp hi))

/-!
## Section 5: Coefficient Bounds for Factors

If `g` is a monic factor of a monic polynomial `f` over ℂ, and all roots of `f` have
absolute value at most `B`, then the coefficients of `g` satisfy
`‖gᵢ‖ ≤ (k choose i) · Bⁱ` where `k = deg g`.
-/

/-
Coefficients of a monic polynomial are elementary symmetric functions of its roots,
hence bounded by binomial coefficients times the root bound.

More precisely, if `g = ∏ᵢ (X - αᵢ)` with `‖αᵢ‖ ≤ B`, then
`‖coeff g j‖ ≤ (k choose (k - j)) · B^(k - j)` for `j < k = deg g`.
-/
lemma factor_coeff_bound {g : Polynomial ℂ} (hg : g.Monic) (k : ℕ) (hk : g.natDegree = k)
    {B : ℝ} (hB : 0 ≤ B)
    (hroots : ∀ α : ℂ, g.IsRoot α → ‖α‖ ≤ B)
    (j : ℕ) (hj : j < k) :
    ‖g.coeff j‖ ≤ (k.choose (k - j)) * B ^ (k - j) := by
  obtain ⟨l, hl⟩ :
      ∃ l : List ℂ, l.length = k ∧ g = List.prod (List.map (fun α ↦ Polynomial.X - Polynomial.C α) l) := by
    have h_factor :
        ∃ l : Multiset ℂ, l.card = k ∧ g = Multiset.prod (Multiset.map (fun α ↦ Polynomial.X - Polynomial.C α) l) := by
      use g.roots
      have := Polynomial.Splits.natDegree_eq_card_roots (show g.Splits from ?_)
      · refine ⟨this ▸ hk, ?_⟩
        nth_rw 1 [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hg]
        omega
      · exact IsAlgClosed.splits g
    obtain ⟨l, hl₁, hl₂⟩ := h_factor
    refine ⟨l.toList, ?_, ?_⟩
    · simpa using hl₁
    · simpa using hl₂
  -- By Vieta's formulas, the coefficient of `X^j` in `g` is `(-1)^(k-j) · σ_(k-j)(α₁, …, α_k)`, where `σ_(k-j)` is the `(k-j)`-th elementary symmetric polynomial.
  have h_vieta : g.coeff j = (-1) ^ (k - j) *
      Multiset.sum (Multiset.map (fun s ↦ Multiset.prod s)
        (Multiset.powersetCard (k - j) (Multiset.ofList l))) := by
    have h_coeff : g.coeff j =
        Polynomial.coeff
          (Multiset.prod (Multiset.map (fun α ↦ Polynomial.X - Polynomial.C α) (Multiset.ofList l))) j := by
      simp_all
    rw [h_coeff, Multiset.prod_X_sub_C_coeff]
    · simp [hl.1, Multiset.esymm]
    · simpa [hl.1] using hj.le
  -- Since `|αᵢ| ≤ B` for all `i`, we have `|σ_(k-j)| ≤ (k choose (k-j)) · B^(k-j)`.
  have h_prod_bound : ∀ s : Multiset ℂ, (∀ α ∈ s, ‖α‖ ≤ B) → ‖Multiset.prod s‖ ≤ B ^ Multiset.card s := by
    intros s hs
    induction s using Multiset.induction <;> norm_num at *
    simpa only [pow_succ'] using
      mul_le_mul hs.1
        (by
          apply_assumption
          tauto) (by positivity) (by positivity)
  have h_subset_bound : ∀ s ∈ Multiset.powersetCard (k - j) (Multiset.ofList l),
      ‖Multiset.prod s‖ ≤ B ^ (k - j) := by
    intros s hs
    specialize h_prod_bound s
    simp_all [Multiset.mem_powersetCard]
    refine h_prod_bound fun α hα ↦ hroots α ?_
    rw [Polynomial.eval_list_prod]
    simp_all [List.prod_eq_zero_iff, sub_eq_zero]
    exact Multiset.mem_of_le hs.1 hα
  have h_sum_bound :
      ‖Multiset.sum (Multiset.map (fun s ↦ Multiset.prod s)
        (Multiset.powersetCard (k - j) (Multiset.ofList l)))‖ ≤ (Nat.choose k (k - j)) * B ^ (k - j) := by
    refine le_trans (norm_multiset_sum_le _) ?_
    convert Multiset.sum_le_card_nsmul _ _ _ <;> norm_num
    · ext
      simp [hl.1]
    · infer_instance
    · intro x x_1 a a_1 a_2; subst hk a_2; simp_all only [IsRoot.def, Multiset.mem_powersetCard, and_imp]
  simp_all

/-!
## Section 6: Finite Polynomial Root Counting

A nonzero polynomial in one variable has finitely many roots. This extends to
counting integer roots and projections of polynomial curves.
-/

/-
A nonzero polynomial over ℚ has finitely many rational roots.
-/
lemma Polynomial.finite_roots_rat {p : Polynomial ℚ} (hp : p ≠ 0) :
    Set.Finite {x : ℚ | p.IsRoot x} := by
  exact p.roots.toFinset.finite_toSet.subset fun x hx ↦ by simp_all

/-
A nonzero polynomial over ℤ (viewed as a polynomial in one variable) has at most
`natDegree` integer roots.
-/
lemma int_roots_bounded {p : Polynomial ℤ} (hp : p ≠ 0) :
    Set.Finite {x : ℤ | (p.map (Int.castRingHom ℚ)).IsRoot (x : ℚ)} := by
  refine Set.Finite.of_finite_image (f := fun x : ℤ ↦ (x : ℚ)) ?_ ?_
  · refine Set.Finite.subset
      (p.map (Int.castRingHom ℚ) |> Polynomial.roots |> Multiset.toFinset |> Finset.finite_toSet) ?_
    norm_num [Set.subset_def]
    exact fun a ha ↦ ⟨by rw [Polynomial.map_eq_zero_iff] <;> (first | (intro a_1; subst a_1; simp_all only [ne_eq, not_true_eq_false]) | (intro a₁ a₂ a_1; simp_all only [ne_eq, eq_intCast, Int.cast_inj])), ha⟩
  · simp

/-
For a fixed monic polynomial `g ∈ ℤ[X]` of degree `k` and a polynomial
`f ∈ ℚ[T][X]` irreducible over `ℚ(T)`, the set of integers `t` for which
`g ∣ f(t, X)` is finite.

This is because the condition `g ∣ f(t, X)` translates to `k` polynomial
equations in `t`, and since `f` is irreducible (hence `g` does not divide `f`
over `ℚ(T)`), at least one of these equations is nonzero.
-/
lemma finite_specializations_for_fixed_factor
    {f : Polynomial (Polynomial ℚ)} {g : Polynomial ℤ}
    (hf_irr : Irreducible f) (hf_monic : f.Monic)
    (hg_monic : g.Monic) (hg_deg : 0 < g.natDegree) (hg_lt : g.natDegree < f.natDegree) :
    Set.Finite {t : ℤ | (g.map (Int.castRingHom ℚ)) ∣
      f.map (Polynomial.evalRingHom (↑t : ℚ))} := by
  -- Polynomial division gives `q(T, X)` and a remainder `r(T, X)` with `f(T, X) = g(X) q(T, X) + r(T, X)` and `deg_X r < deg g = k`.
  obtain ⟨q, r, hr⟩ :
      ∃ q r : Polynomial ℚ[X], f = g.map (algebraMap ℤ (Polynomial ℚ)) * q + r ∧ r.degree < g.natDegree := by
    refine ⟨f /ₘ (g.map (algebraMap ℤ ℚ[X])), f %ₘ (g.map (algebraMap ℤ ℚ[X])), ?_, ?_⟩
    · rw [add_comm, Polynomial.modByMonic_add_div f (Polynomial.Monic.map (algebraMap ℤ ℚ[X]) hg_monic)]
    · convert Polynomial.degree_modByMonic_lt f _
      · rw [Polynomial.degree_map_eq_of_leadingCoeff_ne_zero, Polynomial.degree_eq_natDegree]
        · simp_all only [ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [not_monic_zero]
        · simp_all only [algebraMap_int_eq, Monic.leadingCoeff, eq_intCast, Int.cast_one, ne_eq, one_ne_zero, not_false_eq_true]
      · exact hg_monic.map _
  -- Since `g` does not divide `f` over `ℚ(T)`, the remainder `r` must be nonzero.
  have hr_nonzero : r ≠ 0 := by
    contrapose! hg_lt
    simp_all
    rw [irreducible_mul_iff] at hf_irr
    rcases hf_irr with (⟨hg₁, hg₂⟩ | ⟨hg₁, hg₂⟩) <;>
      have := Polynomial.natDegree_eq_zero_of_isUnit hg₂ <;> simp_all
    rw [Polynomial.natDegree_mul']
    · simp [hg_monic.natDegree_map, this]
    · rw [← Polynomial.leadingCoeff_mul, hf_monic.leadingCoeff]
      exact one_ne_zero
  -- The condition `g(X) ∣ f(t, X)` is equivalent to `r(t, X) = 0`.
  have h_equiv : ∀ t : ℤ, (g.map (Int.castRingHom ℚ)) ∣ (f.map (evalRingHom (t : ℚ))) ↔
      ∀ j < g.natDegree, Polynomial.eval (t : ℚ) (r.coeff j) = 0 := by
    intro t
    constructor
    · intro h_div
      have h_r_zero : (r.map (evalRingHom (t : ℚ))) = 0 := by
        have h_r_dvd : (g.map (Int.castRingHom ℚ)) ∣ (r.map (evalRingHom (t : ℚ))) := by
          simp_all
          convert dvd_sub h_div
            (dvd_mul_right (map (Int.castRingHom ℚ) g) (map (evalRingHom (t : ℚ)) q)) using 1
          ring_nf!
          simp [mul_comm, Polynomial.map_map]
          rw [sub_eq_zero, mul_comm]
          congr
          ext
          simp
        refine Polynomial.eq_zero_of_dvd_of_degree_lt h_r_dvd ?_
        refine lt_of_le_of_lt (b := ↑(Polynomial.natDegree r)) ?_ ?_
        · exact le_trans (Polynomial.degree_map_le) (Polynomial.degree_le_natDegree)
        · rw [Polynomial.degree_map_eq_of_leadingCoeff_ne_zero] <;> norm_num [hg_monic]
          exact_mod_cast Polynomial.natDegree_lt_iff_degree_lt (by trivial) |>.2 hr.2
      simp_all [Polynomial.ext_iff]
    · intro h
      have h_r_zero : (r.map (evalRingHom (t : ℚ))) = 0 := by
        ext j
        by_cases hj : j < g.natDegree <;> simp_all
        rw [Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hr.2 (WithBot.coe_le_coe.mpr hj)),
          Polynomial.eval_zero]
      simp_all [Polynomial.map_map]
      have hcomp : (evalRingHom (t : ℚ) |> RingHom.comp <| Int.castRingHom ℚ[X]) = (Int.castRingHom ℚ) := by
        ext
        simp
      exact dvd_mul_of_dvd_left (by rw [hcomp]) _
  -- Since `r` is nonzero, some `j < g.natDegree` has `r.coeff j ≠ 0`.
  obtain ⟨j, hj_lt, hj_nonzero⟩ : ∃ j < g.natDegree, r.coeff j ≠ 0 := by
    contrapose! hr_nonzero
    ext j
    by_cases hj : j < g.natDegree <;> simp_all [Polynomial.coeff_eq_zero_of_degree_lt]
    rw [Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hr.2 (WithBot.coe_le_coe.mpr hj)),
      Polynomial.coeff_zero]
  refine Set.Finite.subset
    (r.coeff j |> Polynomial.roots |> Multiset.toFinset |> Finset.finite_toSet
      |> Set.Finite.image (fun x : ℚ ↦ ⌊x⌋)) ?_
  intro t ht
  specialize h_equiv t
  refine ⟨(t : ℚ), ?_, Int.floor_intCast t⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq]
  exact ⟨hj_nonzero, h_equiv.mp ht j hj_lt⟩

/-!
## Section 7: The Dörge Counting Estimate

The heart of the Dörge–Bauer proof: for a monic irreducible `f ∈ ℚ[T][X]`, the
number of integers `t ∈ [-N, N]` for which `f(t, X)` has a monic factor of degree `k`
is bounded sublinearly in `N`.

The argument combines:
1. Root bounds → coefficient bounds on factors
2. Each fixed factor occurs for finitely many `t`
3. The number of possible factors for `t ∈ [-N, N]` grows sublinearly
-/

/-- The set of monic integer polynomials of degree `k` with all coefficients bounded
by `B` in absolute value. -/
def boundedMonicPolys (k : ℕ) (B : ℤ) : Set (Polynomial ℤ) :=
  {g : Polynomial ℤ | g.Monic ∧ g.natDegree = k ∧
    ∀ i, i < k → |g.coeff i| ≤ B}

/-
The set of bounded monic polynomials is finite.
-/
lemma finite_boundedMonicPolys (k : ℕ) (B : ℤ) :
    Set.Finite (boundedMonicPolys k B) := by
  refine Set.Finite.subset ?_
    (show boundedMonicPolys k B ⊆
        { g : Polynomial ℤ | ∃ c : Fin k → ℤ, g = Polynomial.monomial k 1 +
          ∑ i : Fin k, Polynomial.monomial i (c i) ∧ ∀ i : Fin k, |c i| ≤ B } from ?_)
  · refine Set.Finite.subset
      (Set.toFinite (Finset.image (fun c : Fin k → ℤ ↦ (monomial k) 1 +
        ∑ i : Fin k, (monomial i) (c i)) (Finset.Icc (-B • 1) (B • 1)))) ?_
    intro g hg
    obtain ⟨c, rfl, hc⟩ := hg
    refine Finset.mem_image.mpr ⟨c, ?_, rfl⟩
    simp [Pi.le_def, abs_le] at *
    simp_all
  · intro g hg
    refine ⟨fun i ↦ g.coeff i, ?_, ?_⟩ <;> have := hg.2.1 <;> simp_all [← Polynomial.C_mul_X_pow_eq_monomial]
    · conv_lhs => rw [g.as_sum_range_C_mul_X_pow]
      simp [this, Finset.sum_range, Fin.sum_univ_castSucc]
      rw [add_comm, ← this, hg.1.coeff_natDegree]
      norm_num
    · exact fun i ↦ hg.2.2 _ (Fin.is_lt i)

/-!
## Section 7: The Dörge Density Estimate

The heart of the Dörge–Bauer proof: for a monic irreducible `f ∈ ℚ[T][X]`, the
number of integers `t ∈ [-N, N]` for which `f(t, X)` has a monic factor of degree `k`
is bounded sublinearly in `N`. This section provides the key intermediate results.
-/

/-
If a subset `S ⊆ ℤ` grows sublinearly (i.e., `|S ∩ [-N, N]| ≤ C · N^α` with `α < 1`),
then the complement `Sᶜ` is infinite.

The proof is by contradiction: if `Sᶜ` were finite with `m` elements, then for large `N`,
`|S ∩ [-N, N]| ≥ 2N + 1 - m`, which exceeds `C · N^α` for `N` large enough.
-/
lemma infinite_complement_of_sublinear_ncard {S : Set ℤ} {C : ℝ} {α : ℝ}
    (_hC : 0 < C) (hα : α < 1)
    (hS : ∀ N : ℕ, 0 < N →
      (Set.ncard (S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) ≤ C * (N : ℝ) ^ α) :
    Set.Infinite Sᶜ := by
  by_contra h
  -- If Sᶜ is finite, then for large N, |S ∩ [-N, N]| ≥ 2N + 1 - m.
  obtain ⟨m, hm⟩ :
      ∃ m : ℕ, ∀ N : ℕ, 0 < N → (S ∩ Set.Icc (-N : ℤ) N).ncard ≥ (2 * N + 1) - m := by
    -- Since Sᶜ is finite, let m be its cardinality.
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m = Set.ncard (Sᶜ) := by
      exact ⟨_, rfl⟩
    -- For any N ≥ 1, the set S ∩ [-N, N] contains all but m elements of ℤ.
    use m
    intro N hN_pos
    have h_card :
        (S ∩ Set.Icc (-N : ℤ) N).ncard + (Sᶜ ∩ Set.Icc (-N : ℤ) N).ncard = 2 * N + 1 := by
      rw [← Set.ncard_union_eq]
      · rw [show S ∩ Set.Icc (-N : ℤ) N ∪ Sᶜ ∩ Set.Icc (-N : ℤ) N = Set.Icc (-N : ℤ) N by
          ext x
          by_cases hx : x ∈ S <;> simp_all]
        norm_num [Set.ncard_eq_toFinset_card']
        ring_nf
        norm_cast
      · exact Set.disjoint_left.mpr fun x hx₁ hx₂ ↦ hx₂.1 hx₁.1
    simp at *
    have hsub : Set.ncard (Sᶜ ∩ Set.Icc (-N : ℤ) N) ≤ m := by
      rw [hm]
      exact Set.ncard_le_ncard (fun x hx ↦ hx.1) h
    linarith
  -- Choose N large enough such that 2N + 1 - m > C * N^α.
  obtain ⟨N, hN⟩ :
      ∃ N : ℕ, 0 < N ∧ (2 * N + 1 - m : ℝ) > C * N ^ α := by
    -- Since `α < 1`, we have `C · N^α / N → 0` as `N → ∞`.
    have h_lim :
        Filter.Tendsto (fun N : ℕ ↦ C * (N : ℝ) ^ α / (N : ℝ)) Filter.atTop (nhds 0) := by
      have h_lim_sub : Filter.Tendsto (fun N : ℕ ↦ C * (N : ℝ) ^ (α - 1)) Filter.atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul
          (tendsto_rpow_neg_atTop (by linarith : 0 < - (α - 1)) |> Filter.Tendsto.comp
            <| tendsto_natCast_atTop_atTop)
      refine h_lim_sub.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with N hN
      rw [Real.rpow_sub_one (by positivity)]
      ring
    have := h_lim.eventually (gt_mem_nhds <| show 0 < 1 / 2 by norm_num)
    rw [Filter.eventually_atTop] at this
    rcases this with ⟨N, hN⟩
    refine ⟨N + m + 1, by positivity, ?_⟩
    have := hN (N + m + 1) (by linarith)
    rw [div_lt_iff₀ (by positivity)] at this
    push_cast at *
    linarith
  specialize hm N hN.1
  rw [ge_iff_le, tsub_le_iff_right] at hm
  have hnc : (2 * N + 1 : ℝ) ≤ (S ∩ Set.Icc (-N : ℤ) N |> Set.ncard : ℝ) + m := by
    exact_mod_cast hm
  linarith [hS N hN.1]

/-
**Dörge's density estimate** (the quantitative core of HIT):
For `f ∈ ℚ[T][X]` monic and irreducible of degree `d ≥ 2` in `X`, and `1 ≤ k < d`,
the set of integers `t` for which `f(t, X)` has a monic factor of degree `k`
grows sublinearly in `[-N, N]`.

More precisely, the number of such `t ∈ [-N, N]` is `O(N^{1-1/d})`, where `d = deg_X f`.

Key helper: for an irreducible polynomial f(T, X) monic of degree d ≥ 2 in X,
the specialization f(T, x₀) at any integer x₀ is a nonzero polynomial in T.
This is because (X - x₀) cannot divide the irreducible f when deg_X f ≥ 2. -/
lemma specialization_at_int_nonzero
    (f : Polynomial (Polynomial ℚ)) (hf_irr : Irreducible f)
    (hf_deg : 2 ≤ f.natDegree) (x₀ : ℤ) :
    (f.eval (Polynomial.C (x₀ : ℚ))) ≠ 0 := by
  -- Since `f` is irreducible of degree at least 2, `(X - C x₀)` cannot divide `f` in `ℚ[T][X]`.
  have h_not_div : ¬(Polynomial.X - Polynomial.C (Polynomial.C (x₀ : ℚ)) ∣ f) := by
    contrapose! hf_deg
    have := Polynomial.degree_le_of_dvd hf_deg
    simp_all
    cases hf_deg
    simp_all
    rw [irreducible_mul_iff] at hf_irr
    rcases hf_irr with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;>
      have := Polynomial.degree_eq_zero_of_isUnit h₂ <;> simp_all
    · rw [Polynomial.natDegree_mul'] <;> norm_num [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · rw [Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq this)]
        norm_num
      · exact ⟨Polynomial.X_sub_C_ne_zero _, by rename_i h; subst h; apply Aesop.BuiltinRules.not_intro; intro a; subst a; simp_all only [isUnit_zero_iff, zero_ne_one]⟩
    · refine absurd this ?_
      erw [Polynomial.degree_X_sub_C]
      norm_num
  exact fun h ↦ h_not_div <| Polynomial.dvd_iff_isRoot.mpr h

/-- The composite ring hom `ℤ[T] → ℚ(T)`, factoring through `ℤ[T] → ℚ[T] → Frac(ℚ[T])`.
Used to phrase "`P` has no root in the rational function field `ℚ(T)`". -/
def toRatFunc : Polynomial ℤ →+* FractionRing (Polynomial ℚ) :=
  (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))).comp
    (mapRingHom (Int.castRingHom ℚ))

/-- **Evaluation commutes**: evaluating `P ∈ ℤ[T][Y]` at `T := t` then `Y := y` equals
evaluating at `Y := y` (giving the value polynomial `P(T, y) ∈ ℤ[T]`) then at `T := t`. -/
lemma eval_map_evalRingHom_eq (P : Polynomial (Polynomial ℤ)) (t y : ℤ) :
    (P.map (Polynomial.evalRingHom t)).eval y = (P.eval (Polynomial.C y)).eval t := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_eval_map, Polynomial.eval_map]
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [Polynomial.eval₂_monomial]

/-- For `P` with no root in `ℚ(T)`, the value polynomial `P(T, y) = P.eval (C y) ∈ ℤ[T]`
is nonzero for every integer `y`: otherwise the constant `y ∈ ℚ(T)` would be a root of
`P.map toRatFunc`. -/
lemma eval_C_ne_zero_of_no_root
    (P : Polynomial (Polynomial ℤ))
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a)
    (y : ℤ) : P.eval (Polynomial.C y) ≠ 0 := by
  intro h
  apply hP_no_root (toRatFunc (Polynomial.C y))
  unfold Polynomial.IsRoot
  have : (P.map toRatFunc).eval (toRatFunc (Polynomial.C y))
      = toRatFunc (P.eval (Polynomial.C y)) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rw [this, h, map_zero]

/-
**Small-root part (elementary).** For `P ∈ ℤ[T][Y]` with no root in `ℚ(T)`, the number
of integers `t ∈ [-N, N]` for which the specialization `P(t, Y)` has an *integer* root `y`
with `y² ≤ N` is `O(N^{1/2})`.

This part is completely elementary: for each fixed integer `y`, the value polynomial
`P(T, y) ∈ ℤ[T]` is nonzero (`eval_C_ne_zero_of_no_root`), so it has at most `deg_T P` many
roots `t`; there are only `O(√N)` admissible values `y` with `y² ≤ N`.
-/
lemma int_root_locus_small_sublinear
    (P : Polynomial (Polynomial ℤ))
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard ({t : ℤ | ∃ y : ℤ, y ^ 2 ≤ (N : ℤ) ∧
          (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩
        Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) ≤ C * (N : ℝ) ^ (1 / 2 : ℝ) := by
  -- Let `m := ∑_(i=0)^(P.natDegree) (P.coeff i).natDegree`.
  set m := ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).natDegree
  refine ⟨3 * (m + 1), ?_, ?_⟩ <;> norm_num
  · positivity
  · intro N hN_pos
    set s := Nat.sqrt N
    have h_card :
        Set.ncard ({t : ℤ | ∃ y : ℤ, y^2 ≤ (N : ℤ) ∧
          (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩ Set.Icc (-(N : ℤ)) (N : ℤ)) ≤ (2 * s + 1) * m := by
      have h_card_y : ∀ y : ℤ, y^2 ≤ (N : ℤ) →
          Set.ncard ({t : ℤ | (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩ Set.Icc (-(N : ℤ)) (N : ℤ)) ≤ m := by
        intro y hy
        have hQ_nonzero : P.eval (Polynomial.C y) ≠ 0 := by
          apply eval_C_ne_zero_of_no_root P hP_no_root y
        have hQ_natDegree : (P.eval (Polynomial.C y)).natDegree ≤ m := by
          rw [Polynomial.eval_eq_sum_range]
          refine le_trans (Polynomial.natDegree_sum_le _ _) (Finset.sup_le ?_)
          intro i hi
          by_cases hi' : P.coeff i = 0 <;> simp_all
          refine le_trans ?_
            (Finset.single_le_sum (fun i _ ↦ Nat.zero_le (Polynomial.natDegree (P.coeff i)))
              (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
          exact le_trans (Polynomial.natDegree_mul_le ..) (by norm_num)
        have hQ_roots :
            Set.ncard ({t : ℤ | (P.eval (Polynomial.C y)).IsRoot t} ∩ Set.Icc (-(N : ℤ)) (N : ℤ)) ≤
              (P.eval (Polynomial.C y)).natDegree := by
          have hQ_finset :
              Set.ncard ({t : ℤ | (P.eval (Polynomial.C y)).IsRoot t} ∩ Set.Icc (-(N : ℤ)) (N : ℤ)) ≤
                (P.eval (Polynomial.C y)).roots.toFinset.card := by
            rw [← Set.ncard_coe_finset]
            apply Set.ncard_le_ncard
            · intro t ht
              simp_all
            · exact Finset.finite_toSet _
          exact hQ_finset.trans (le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _))
        convert hQ_roots.trans hQ_natDegree using 2
        ext
        simp [eval_map_evalRingHom_eq]
      have h_card_union :
          Set.ncard (⋃ y ∈ Finset.Icc (-(s : ℤ)) (s : ℤ),
            {t : ℤ | (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩ Set.Icc (-(N : ℤ)) (N : ℤ)) ≤ (2 * s + 1) * m := by
        have h_card_S : ∀ {S : Finset ℤ}, (∀ y ∈ S, y^2 ≤ (N : ℤ)) →
            Set.ncard (⋃ y ∈ S, {t : ℤ | (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩
              Set.Icc (-(N : ℤ)) (N : ℤ)) ≤ S.card * m := by
          intros S hS
          induction' S using Finset.induction with y S hyS ih <;> simp_all
          exact le_trans (Set.ncard_union_le _ _) (by linarith [h_card_y y hS.1])
        refine le_trans (h_card_S ?_) ?_
        · exact fun y hy ↦ by nlinarith [Finset.mem_Icc.mp hy, Nat.sqrt_le N]
        · norm_num [two_mul, add_assoc]
          norm_cast
          ring_nf
          norm_num
      refine le_trans ?_ h_card_union
      fapply Set.ncard_le_ncard
      · intro t ht
        obtain ⟨y, hy₁, hy₂⟩ := ht.1
        refine Set.mem_iUnion₂.mpr ⟨y, Finset.mem_Icc.mpr ⟨?_, ?_⟩, hy₂, ht.2⟩
        · nlinarith [Nat.lt_succ_sqrt N]
        · nlinarith [Nat.lt_succ_sqrt N]
      · exact Set.Finite.subset (Set.finite_Icc (-N : ℤ) N) fun x hx ↦ by simp_all only [IsRoot.def, Finset.mem_Icc, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, exists_and_left, exists_prop, m, s]
                                                                          obtain ⟨w, h⟩ := hx
                                                                          obtain ⟨left, right⟩ := h
                                                                          obtain ⟨left_1, right⟩ := right
                                                                          obtain ⟨left_2, right⟩ := right
                                                                          obtain ⟨left_2, right_1⟩ := left_2
                                                                          simp_all only [and_self]
    refine le_trans (Nat.cast_le.mpr h_card) ?_
    norm_num [← Real.sqrt_eq_rpow]
    nlinarith only [show (s : ℝ) ≤ Real.sqrt N by exact Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' N,
      show (1 : ℝ) ≤ Real.sqrt N by exact Real.le_sqrt_of_sq_le <| mod_cast hN_pos,
      Real.mul_self_sqrt <| Nat.cast_nonneg N]

/-
**Root-magnitude bound (Step 1 towards `int_root_locus_large_sublinear`).**

For `P ∈ ℤ[T][Y]` monic in `Y`, every integer root `y` of the specialization `P(t, ·)`
satisfies Cauchy's bound
`|y| ≤ 1 + ∑_{i < deg_Y P} |c_i(t)|`, where `c_i = P.coeff i ∈ ℤ[T]`.

Since each `c_i` is a fixed integer polynomial, for `|t| ≤ N` the right-hand side is bounded
by `K · N^e` (with `e = max_i deg_T c_i` and `K` a constant), so *every* integer root of
`P(t, ·)` has magnitude polynomial in `N`. This is precisely the input that confines the
"large" roots to the window `√N < |y| ≤ K·N^e` in the sparsity estimate
`int_root_locus_large_sublinear`.
-/
lemma int_root_specialization_abs_le
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic)
    (t y : ℤ) (hy : (P.map (Polynomial.evalRingHom t)).IsRoot y) :
    (|y| : ℝ) ≤ 1 + ∑ i ∈ Finset.range P.natDegree, ((|(P.coeff i).eval t| : ℤ) : ℝ) := by
  -- Apply the Cauchy bound to the polynomial `P(t, Y)`.
  convert cauchy_root_bound
    (p := Polynomial.map (algebraMap ℤ ℂ) (P.map (Polynomial.evalRingHom t))) _
    (α := (y : ℂ)) _ using 1 <;>
    norm_num [Polynomial.coeff_map]
  · rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;> norm_num [hP_monic]
    intro h
    simp_all [Polynomial.ext_iff]
    specialize h (Polynomial.natDegree P)
    simp_all
  · exact Polynomial.Monic.map (Int.castRingHom ℂ) (Polynomial.Monic.map (Polynomial.evalRingHom t) hP_monic)
  · exact hy

/-
**Combination lemma: a finite cover by sublinear sets is sublinear.**

If a family of integer sets `S N` is, for every `N`, covered by finitely many sets
`T 0 N, …, T (n-1) N`, each of which is finite and grows sublinearly
(`#(T j N) ≤ C_j · N^{α_j}` with `α_j < 1`), then `S N` itself grows sublinearly.

This is the elementary book-keeping step that lets us assemble the per-branch estimates of
`int_root_locus_large_cover` into the single bound of `int_root_locus_large_sublinear`.
Take `α = maxⱼ α_j < 1` and `C = ∑ⱼ C_j`.
-/
lemma sublinear_finite_cover {n : ℕ} (S : ℕ → Set ℤ) (T : Fin n → ℕ → Set ℤ)
    (hcover : ∀ N : ℕ, S N ⊆ ⋃ j, T j N)
    (hTfin : ∀ (j : Fin n) (N : ℕ), (T j N).Finite)
    (hsub : ∀ j : Fin n, ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
        (Set.ncard (T j N) : ℝ) ≤ C * (N : ℝ) ^ α) :
    ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
        (Set.ncard (S N) : ℝ) ≤ C * (N : ℝ) ^ α := by
  -- For each j, obtain the constants C_j and α_j from the hypothesis hsub.
  obtain ⟨C, α, hC_pos, hα_nonneg, hα_lt_1, h_bound⟩ :
      ∃ (C : Fin n → ℝ) (α : Fin n → ℝ), (∀ j, 0 < C j) ∧ (∀ j, 0 ≤ α j) ∧ (∀ j, α j < 1) ∧
        (∀ j, ∀ N : ℕ, 0 < N → (Set.ncard (T j N)) ≤ C j * (N : ℝ) ^ (α j)) := by
    exact ⟨fun j ↦ Classical.choose (hsub j),
      fun j ↦ Classical.choose_spec (hsub j) |> Classical.choose,
      fun j ↦ Classical.choose_spec (hsub j) |> Classical.choose_spec |> And.left,
      fun j ↦ Classical.choose_spec (hsub j) |> Classical.choose_spec |> And.right |> And.left,
      fun j ↦ Classical.choose_spec (hsub j) |> Classical.choose_spec |> And.right |> And.right |> And.left,
      fun j N hN ↦ Classical.choose_spec (hsub j) |> Classical.choose_spec |> And.right |> And.right
        |> And.right |> fun h ↦ h N hN⟩
  by_cases hn : n = 0
  · subst hn
    use 1, 0
    simp_all
  · refine ⟨∑ j, C j,
      Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩) fun j ↦ α j,
      ?_, ?_, ?_, ?_⟩ <;>
      norm_num [Finset.sum_nonneg, hC_pos, hα_nonneg, hα_lt_1]
    · exact Finset.sum_pos (fun _ _ ↦ hC_pos _) ⟨⟨0, Nat.pos_of_ne_zero hn⟩, Finset.mem_univ _⟩
    · exact ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    · intro N hN_pos
      have h_card_union : (Set.ncard (⋃ j, T j N)) ≤ ∑ j, (Set.ncard (T j N)) :=
        Set.ncard_iUnion_le_of_fintype _
      refine le_trans ?_ (le_trans (Nat.cast_le.mpr h_card_union) ?_)
      · gcongr
        · exact Set.finite_iUnion fun j ↦ hTfin j N
        · exact hcover N
      · push_cast [Finset.sum_mul]
        exact Finset.sum_le_sum fun i _ ↦
          le_trans (h_bound i N hN_pos)
            (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (mod_cast hN_pos)
                (Finset.le_sup' (fun j ↦ α j) (Finset.mem_univ i)))
              (le_of_lt (hC_pos i)))

/-
**Magnitude window (Step 2, elementary).**

For `P ∈ ℤ[T][Y]` monic in `Y`, there are constants `K > 0` and an exponent `e` such that
for `|t| ≤ N` every integer root `y` of the specialization `P(t, ·)` satisfies
`|y| ≤ K · N^e`.

This is the direct consequence of Cauchy's bound `int_root_specialization_abs_le`
(`|y| ≤ 1 + ∑_{i<deg_Y P} |c_i(t)|`) together with the polynomial growth of each fixed
integer coefficient polynomial `c_i = P.coeff i` on `|t| ≤ N`. Combined with the defining
inequality `N < y²` of the large-root locus, it confines the large roots to the window
`√N < |y| ≤ K · N^e`, so that only finitely many branch values are relevant for each `N`.
-/
lemma int_root_large_magnitude_window
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic) :
    ∃ (K : ℝ) (e : ℕ), 0 < K ∧ ∀ (N : ℕ), 0 < N → ∀ t : ℤ, -(N : ℤ) ≤ t → t ≤ (N : ℤ) →
      ∀ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y → (|y| : ℝ) ≤ K * (N : ℝ) ^ e := by
  obtain ⟨K, e, hK⟩ :
      ∃ K e : ℤ, 0 < K ∧ ∀ N : ℕ, 0 < N → ∀ t : ℤ, -↑N ≤ t → t ≤ ↑N →
        ∀ y : ℤ, (map (evalRingHom t) P).IsRoot y →
          |(y : ℝ)| ≤ 1 + ∑ i ∈ Finset.range P.natDegree,
            (∑ j ∈ Finset.range ((P.coeff i).natDegree + 1), |(P.coeff i).coeff j| : ℝ) *
              (N : ℝ) ^ ((P.coeff i).natDegree) := by
    refine ⟨1, 0, by norm_num,
      fun N hN t ht₁ ht₂ y hy ↦ le_trans (int_root_specialization_abs_le P hP_monic t y hy) ?_⟩
    gcongr
    rw [Polynomial.eval_eq_sum_range]
    norm_cast
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    norm_num [abs_mul, Finset.sum_mul]
    exact Finset.sum_le_sum fun i hi ↦
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr ⟨by linarith, by linarith⟩) _ |> le_trans
          <| pow_le_pow_right₀ (by linarith) <| Finset.mem_range_succ_iff.mp hi) <| abs_nonneg _
  refine ⟨1 + ∑ i ∈ Finset.range P.natDegree, ∑ j ∈ Finset.range ((P.coeff i |> Polynomial.natDegree) + 1),
      |(P.coeff i |> Polynomial.coeff) j|,
    ∑ i ∈ Finset.range P.natDegree, (P.coeff i |> Polynomial.natDegree), ?_, ?_⟩ <;> norm_num
  · exact add_pos_of_pos_of_nonneg zero_lt_one <| Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  · intro N hN t ht₁ ht₂ y hy
    have := hK.2 N hN t ht₁ ht₂ y hy
    simp_all [add_mul, Finset.sum_mul]
    refine le_trans this (add_le_add ?_ ?_)
    · exact_mod_cast Nat.one_le_pow _ _ hN
    · exact Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (mod_cast hN)
            (Finset.single_le_sum (fun a _ ↦ Nat.zero_le (Polynomial.natDegree (P.coeff a))) hi))
          (abs_nonneg _)

/-
**The abstract smooth-arc formulation of the Bombieri–Pila core is false.**

Mere `k`-fold continuous differentiability together with non-polynomiality is *not* enough
to force sublinearly many integer values.  The smooth function `f x = sin (π x)` is `C^∞`
(hence `C^k` for every `k`), is not a polynomial, yet it takes the integer value `0` at
*every* integer, so it has `N` integer values in `[1, N]` — linear, not sublinear.

This is why the original abstract statement (smoothness + non-polynomiality only) cannot be
proved as written, and why the corrected `graph_integer_points_sublinear` needs an extra structural
hypothesis (a monotone, decaying `k`-th derivative — the behaviour of a real Puiseux branch
of an algebraic function at infinity).
-/
lemma graph_integer_points_sublinear_false :
    ∃ (f : ℝ → ℝ) (k : ℕ), 2 ≤ k ∧ ContDiffOn ℝ k f (Set.Ici (1 : ℝ)) ∧
      (∀ p : Polynomial ℝ, p.natDegree ≤ k → ∃ x ∈ Set.Ici (1 : ℝ), f x ≠ p.eval x) ∧
      ¬ (∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
          (Set.ncard {t : ℤ | (1 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (N : ℝ) ∧
              ∃ m : ℤ, f (t : ℝ) = (m : ℝ)} : ℝ) ≤ C * (N : ℝ) ^ α) := by
  refine ⟨fun x ↦ Real.sin (Real.pi * x), 2, ?_, ?_, ?_, ?_⟩ <;> norm_num
  · exact ContDiff.contDiffOn (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))
  · intro p hp
    by_contra! h
    have := h 1
    have := h 2
    have := h 3
    norm_num [mul_assoc, mul_comm Real.pi] at *
    -- Since `p` has degree at most 2, write it as `p x = a x^2 + b x + c`.
    obtain ⟨a, b, c, ha⟩ :
        ∃ a b c : ℝ, p = Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c := by
      refine ⟨p.coeff 2, p.coeff 1, p.coeff 0, ?_⟩
      refine Polynomial.as_sum_range_C_mul_X_pow p ▸ ?_
      interval_cases p.natDegree <;> norm_num [Finset.sum_range_succ']
    norm_num [ha, Real.sin_three_mul] at *
    have := h (3 / 2) (by norm_num)
    norm_num [(by ring : 3 / 2 * Real.pi = Real.pi + Real.pi / 2), Real.sin_add] at this
    linarith
  · intro x hx y hy hxy
    -- Since `sin (π t) = 0` for all integers `t`, the set `{t ∈ ℤ | 1 ≤ t ≤ N ∧ ∃ m ∈ ℤ, sin (π t) = m}` is just the integers from `1` to `N`.
    have h_set : ∀ N : ℕ, 0 < N →
        {t : ℤ | 1 ≤ t ∧ t ≤ N ∧ ∃ m : ℤ, Real.sin (Real.pi * t) = m} = Set.Icc 1 (N : ℤ) := by
      intro N hN
      ext t
      simp [Set.mem_setOf_eq]
      exact fun _ _ ↦ ⟨0, by norm_num [mul_comm Real.pi]⟩
    -- Choose `N` such that `x · N^y < N`.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 0 < N ∧ x * (N : ℝ) ^ y < N := by
      -- Since `y < 1`, we can choose `N` such that `x < N^(1-y)`.
      obtain ⟨N, hN⟩ : ∃ N : ℕ, 0 < N ∧ x < (N : ℝ) ^ (1 - y) := by
        have h_lim : Filter.Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 - y)) Filter.atTop Filter.atTop := by
          exact tendsto_rpow_atTop (by linarith) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop
        exact Filter.eventually_atTop.mp (h_lim.eventually_gt_atTop x) |>
          fun ⟨N, hN⟩ ↦ ⟨N + 1, Nat.succ_pos _, hN _ (Nat.le_succ _)⟩
      refine ⟨N, hN.1, ?_⟩
      convert mul_lt_mul_of_pos_right hN.2 (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN.1) y) using 1
      rw [← Real.rpow_add (Nat.cast_pos.mpr hN.1)]
      norm_num
    use N
    convert hN using 2
    have hrw : {t : ℤ | 1 ≤ (t : ℝ) ∧ (t : ℝ) ≤ N ∧ ∃ m : ℤ, Real.sin (Real.pi * t) = m}
        = Set.Icc 1 (N : ℤ) := mod_cast h_set N hN.1
    rw [hrw]
    norm_num [Set.ncard_eq_toFinset_card']

/-
**The `monotone (or antitone) + tends-to-0` correction is *still* false.**

Concrete counterexample (`k = 2`), fully machine-checked in
`graph_integer_points_sublinear_still_false` below:

  `f x = (min (x - 2) 0) ^ 3`,

i.e. `f x = (x - 2)^3` for `x ≤ 2` and `f x = 0` for `x ≥ 2`.  Then
* `f` is `C^2` (`gipsCexF_contDiff`), with `f'' x = 6 · min (x - 2) 0`;
* `f''` is (weakly) monotone increasing on `[1, ∞)` and is eventually `0`, so it tends to
  `0` at infinity (`gipsCexF_mono_iter`, `gipsCexF_tends`);
* `f` is not a polynomial of degree `≤ 2` (`gipsCexF_nonpoly`);
* yet `f t ∈ ℤ` for *every* integer `t` (`f t = (min (t - 2) 0)^3 ∈ ℤ`,
  `gipsCexF_int`), so there are `N` integer values in `[1, N]` — linear, not sublinear.

The genuinely true statement (feeding the algebraic application) requires the `k`-th
derivative to be *strictly* monotone (equivalently, of one strict sign) so that no tail is
polynomial — the real Jarník / Bombieri–Pila situation.  See the corrected
`graph_integer_points_sublinear` further below. -/

section GraphIntegerPointsCounterexample
open Set Filter Topology

/-- Witness function for `graph_integer_points_sublinear_still_false`:
`f x = (min (x - 2) 0)^3`, i.e. `(x - 2)^3` for `x ≤ 2` and `0` for `x ≥ 2`. -/
noncomputable def gipsCexF (x : ℝ) : ℝ := (min (x-2) 0)^3
/-- First derivative of `gipsCexF`. -/
noncomputable def gipsCexF' (x : ℝ) : ℝ := 3*(min (x-2) 0)^2
/-- Second derivative of `gipsCexF`. -/
noncomputable def gipsCexF'' (x : ℝ) : ℝ := 6*(min (x-2) 0)

lemma gipsCexF_hasDerivAt (x : ℝ) : HasDerivAt gipsCexF (gipsCexF' x) x := by
  rcases lt_trichotomy x 2 with h | h | h
  · rw [show gipsCexF' x = 3*(x-2)^2 by simp [gipsCexF', min_eq_left (by linarith : x - 2 ≤ 0)]]
    have hev : gipsCexF =ᶠ[𝓝 x] (fun x ↦ (x-2)^3) := by
      filter_upwards [eventually_lt_nhds h] with y hy
      simp [gipsCexF, min_eq_left (by linarith : y - 2 ≤ 0)]
    have hd : HasDerivAt (fun x : ℝ ↦ (x-2)^3) (3*(x-2)^2) x := by
      simpa using (((hasDerivAt_id x).sub_const 2).pow 3)
    exact hd.congr_of_eventuallyEq hev
  · subst h
    rw [show gipsCexF' 2 = 0 by simp [gipsCexF']]
    rw [hasDerivAt_iff_tendsto_slope]
    apply squeeze_zero_norm (a := fun x : ℝ ↦ |x - 2|^2)
    · intro x
      rw [slope_def_field, norm_div]
      rcases eq_or_ne x 2 with rfl | hx
      · simp [gipsCexF]
      · rw [div_le_iff₀ (by simp [sub_ne_zero, hx])]
        have heq : ‖gipsCexF x - gipsCexF 2‖ = |min (x-2) 0|^3 := by
          simp only [gipsCexF]
          norm_num [Real.norm_eq_abs, abs_pow]
        rw [heq]
        have hmin : |min (x-2) 0| ≤ |x-2| := by
          rcases le_or_gt (x-2) 0 with h | h
          · rw [min_eq_left h]
          · rw [min_eq_right h.le]
            simp
        calc |min (x-2) 0|^3 ≤ |x-2|^3 := by gcongr
          _ = |x-2|^2 * ‖x-2‖ := by
            rw [Real.norm_eq_abs]
            ring
    · have hc : Continuous (fun x : ℝ ↦ |x-2|^2) := by fun_prop
      have h2 := hc.tendsto 2
      simp only [show |(2:ℝ)-2|^2 = 0 by norm_num] at h2
      exact h2.mono_left nhdsWithin_le_nhds
  · rw [show gipsCexF' x = 0 by simp [gipsCexF', min_eq_right (by linarith : (0:ℝ) ≤ x - 2)]]
    have hev : gipsCexF =ᶠ[𝓝 x] (fun _ ↦ 0) := by
      filter_upwards [eventually_gt_nhds h] with y hy
      simp [gipsCexF, min_eq_right (by linarith : (0:ℝ) ≤ y - 2)]
    exact (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq hev

lemma gipsCexF'_hasDerivAt (x : ℝ) : HasDerivAt gipsCexF' (gipsCexF'' x) x := by
  rcases lt_trichotomy x 2 with h | h | h
  · rw [show gipsCexF'' x = 6*(x-2) by simp [gipsCexF'', min_eq_left (by linarith : x - 2 ≤ 0)]]
    have hev : gipsCexF' =ᶠ[𝓝 x] (fun x ↦ 3*(x-2)^2) := by
      filter_upwards [eventually_lt_nhds h] with y hy
      simp [gipsCexF', min_eq_left (by linarith : y - 2 ≤ 0)]
    have hd : HasDerivAt (fun x : ℝ ↦ 3*(x-2)^2) (6*(x-2)) x := by
      have h := (((hasDerivAt_id x).sub_const 2).pow 2).const_mul (3:ℝ)
      simp only [id] at h
      convert h using 1
      ring
    exact hd.congr_of_eventuallyEq hev
  · subst h
    rw [show gipsCexF'' 2 = 0 by simp [gipsCexF'']]
    rw [hasDerivAt_iff_tendsto_slope]
    apply squeeze_zero_norm (a := fun x : ℝ ↦ 3*|x - 2|)
    · intro x
      rw [slope_def_field, norm_div]
      rcases eq_or_ne x 2 with rfl | hx
      · simp [gipsCexF']
      · rw [div_le_iff₀ (by simp [sub_ne_zero, hx])]
        have heq : ‖gipsCexF' x - gipsCexF' 2‖ = 3*|min (x-2) 0|^2 := by
          simp only [gipsCexF']
          norm_num [Real.norm_eq_abs, abs_mul, abs_pow]
        rw [heq]
        have hmin : |min (x-2) 0| ≤ |x-2| := by
          rcases le_or_gt (x-2) 0 with h | h
          · rw [min_eq_left h]
          · rw [min_eq_right h.le]
            simp
        calc 3*|min (x-2) 0|^2 ≤ 3*|x-2|^2 := by gcongr
          _ = 3*|x-2| * ‖x-2‖ := by
            rw [Real.norm_eq_abs]
            ring
    · have hc : Continuous (fun x : ℝ ↦ 3*|x-2|) := by fun_prop
      have h2 := hc.tendsto 2
      simp only [show (3:ℝ)*|(2:ℝ)-2| = 0 by norm_num] at h2
      exact h2.mono_left nhdsWithin_le_nhds
  · rw [show gipsCexF'' x = 0 by simp [gipsCexF'', min_eq_right (by linarith : (0:ℝ) ≤ x - 2)]]
    have hev : gipsCexF' =ᶠ[𝓝 x] (fun _ ↦ 0) := by
      filter_upwards [eventually_gt_nhds h] with y hy
      simp [gipsCexF', min_eq_right (by linarith : (0:ℝ) ≤ y - 2)]
    exact (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq hev

lemma gipsCexF_contDiff : ContDiff ℝ 2 gipsCexF := by
  have hderiv1 : deriv gipsCexF = gipsCexF' := funext fun x ↦ (gipsCexF_hasDerivAt x).deriv
  have hderiv2 : deriv gipsCexF' = gipsCexF'' := funext fun x ↦ (gipsCexF'_hasDerivAt x).deriv
  rw [show (2:WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x ↦ (gipsCexF_hasDerivAt x).differentiableAt, by simp, ?_⟩
  rw [hderiv1, contDiff_one_iff_deriv]
  refine ⟨fun x ↦ (gipsCexF'_hasDerivAt x).differentiableAt, ?_⟩
  rw [hderiv2]
  unfold gipsCexF''
  fun_prop

lemma gipsCexF_iterDeriv (x : ℝ) (hx : x ∈ Ici (1:ℝ)) :
    iteratedDerivWithin 2 gipsCexF (Ici 1) x = gipsCexF'' x := by
  have hu : ∀ y ∈ Ici (1:ℝ), UniqueDiffWithinAt ℝ (Ici 1) y :=
    fun y hy ↦ (uniqueDiffOn_Ici 1) y hy
  have hd1 : EqOn (derivWithin gipsCexF (Ici 1)) gipsCexF' (Ici 1) :=
    fun y hy ↦ (gipsCexF_hasDerivAt y).hasDerivWithinAt.derivWithin (hu y hy)
  rw [show (2:ℕ) = 1+1 from rfl, iteratedDerivWithin_succ, iteratedDerivWithin_one]
  rw [derivWithin_congr hd1 (hd1 hx)]
  exact (gipsCexF'_hasDerivAt x).hasDerivWithinAt.derivWithin (hu x hx)

lemma gipsCexF''_mono : Monotone gipsCexF'' := by
  intro a b hab
  simp only [gipsCexF'']
  have : min (a-2) 0 ≤ min (b-2) 0 := min_le_min (by linarith) le_rfl
  linarith

lemma gipsCexF_mono_iter : MonotoneOn (iteratedDerivWithin 2 gipsCexF (Ici 1)) (Ici 1) := by
  intro a ha b hb hab
  rw [gipsCexF_iterDeriv a ha, gipsCexF_iterDeriv b hb]
  exact gipsCexF''_mono hab

lemma gipsCexF_tends : Tendsto (iteratedDerivWithin 2 gipsCexF (Ici 1)) atTop (𝓝 0) := by
  apply Tendsto.congr' (f₁ := fun _ : ℝ ↦ (0:ℝ)) _ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
  rw [gipsCexF_iterDeriv x (Set.mem_Ici.mpr (by linarith))]
  simp [gipsCexF'', min_eq_right (by linarith : (0:ℝ) ≤ x - 2)]

lemma gipsCexF_int (t : ℤ) : ∃ m : ℤ, gipsCexF (t:ℝ) = (m:ℝ) := by
  refine ⟨(min (t-2) 0)^3, ?_⟩
  simp only [gipsCexF]
  rcases le_or_gt ((t:ℝ)-2) 0 with h | h
  · rw [min_eq_left h, min_eq_left (show t - 2 ≤ 0 by exact_mod_cast h)]
    push_cast
    ring
  · rw [min_eq_right h.le, min_eq_right (show (0:ℤ) ≤ t - 2 by exact_mod_cast h.le)]
    push_cast
    ring

lemma gipsCexF_nonpoly (p : Polynomial ℝ) (_hp : p.natDegree ≤ 2) :
    ∃ x ∈ Ici (1:ℝ), gipsCexF x ≠ p.eval x := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ x : ℝ, 2 ≤ x → p.eval x = 0 := by
    intro x hx
    have := hcon x (Set.mem_Ici.mpr (by linarith))
    rw [← this]
    simp [gipsCexF, min_eq_right (by linarith : (0:ℝ) ≤ x - 2)]
  have hpz : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Ici (2:ℝ))
    · intro x hx
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot]
      exact hzero x hx
    · exact Ici_infinite 2
  have h1 := hcon 1 (by simp)
  rw [hpz] at h1
  simp only [gipsCexF] at h1
  norm_num at h1

/-- **The `monotone/antitone + tends-to-0` fix of `graph_integer_points_sublinear_false`
is still false.**

There is a `C²` function `f` on `[1, ∞)` (namely `f x = (min (x - 2) 0)^3`) whose second
derivative is (weakly) monotone and tends to `0` at infinity, and which is not a polynomial
of degree `≤ 2`, yet `f` takes an integer value at *every* integer `t` — so the count of
integers `1 ≤ t ≤ N` with `f t ∈ ℤ` is exactly `N`, which is not `O(N^α)` for any `α < 1`.

Hence merely requiring the `k`-th derivative to be monotone/antitone and to tend to `0` is
insufficient; strictness (of the monotonicity) is needed, as in the corrected
`graph_integer_points_sublinear` below. -/
theorem graph_integer_points_sublinear_still_false :
    ∃ (f : ℝ → ℝ) (k : ℕ), 2 ≤ k ∧ ContDiffOn ℝ k f (Set.Ici (1 : ℝ)) ∧
      (MonotoneOn (iteratedDerivWithin k f (Set.Ici 1)) (Set.Ici 1) ∨
        AntitoneOn (iteratedDerivWithin k f (Set.Ici 1)) (Set.Ici 1)) ∧
      Filter.Tendsto (iteratedDerivWithin k f (Set.Ici 1)) Filter.atTop (nhds 0) ∧
      (∀ p : Polynomial ℝ, p.natDegree ≤ k → ∃ x ∈ Set.Ici (1 : ℝ), f x ≠ p.eval x) ∧
      ¬ (∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
          (Set.ncard {t : ℤ | (1 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (N : ℝ) ∧
              ∃ m : ℤ, f (t : ℝ) = (m : ℝ)} : ℝ) ≤ C * (N : ℝ) ^ α) := by
  refine ⟨gipsCexF, 2, le_refl 2, gipsCexF_contDiff.contDiffOn, Or.inl gipsCexF_mono_iter,
    gipsCexF_tends, gipsCexF_nonpoly, ?_⟩
  rintro ⟨C, α, hC, hα0, hα1, hbound⟩
  have hset : ∀ N : ℕ, {t : ℤ | (1 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (N : ℝ) ∧
      ∃ m : ℤ, gipsCexF (t : ℝ) = (m : ℝ)} = Set.Icc (1:ℤ) (N:ℤ) := by
    intro N
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩
      refine ⟨?_, ?_⟩
      · exact_mod_cast h1
      · exact_mod_cast h2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_, gipsCexF_int t⟩
      · exact_mod_cast h1
      · exact_mod_cast h2
  have hcard : ∀ N : ℕ, (Set.ncard {t : ℤ | (1 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (N : ℝ) ∧
      ∃ m : ℤ, gipsCexF (t : ℝ) = (m : ℝ)} : ℝ) = (N:ℝ) := by
    intro N
    rw [hset N, show Set.Icc (1:ℤ) (N:ℤ) = ↑(Finset.Icc (1:ℤ) (N:ℤ)) by simp,
      Set.ncard_coe_finset, Int.card_Icc]
    simp
  have hkey : ∀ N : ℕ, 0 < N → (N:ℝ) ≤ C * (N:ℝ)^α := by
    intro N hN
    calc (N:ℝ) = _ := (hcard N).symm
      _ ≤ C * (N:ℝ)^α := hbound N hN
  have hlim : Tendsto (fun N : ℕ ↦ (N:ℝ)^(1-α)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM1, hM2⟩ := ((hlim.eventually_gt_atTop C).and (eventually_gt_atTop 0)).exists
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM2
  have hle : (M:ℝ)^(1-α) ≤ C := by
    rw [Real.rpow_sub hMpos, Real.rpow_one, div_le_iff₀ (by positivity)]
    exact hkey M hM2
  linarith

end GraphIntegerPointsCounterexample

/- **Bombieri–Pila / finite-difference core (integer points on a smooth non-polynomial
arc).**

Corrected statement.  As `graph_integer_points_sublinear_false` (the `sin (π x)`
counterexample) and `graph_integer_points_sublinear_still_false` (a `C²`, eventually-zero
second derivative) show, neither smoothness + non-polynomiality alone, nor the addition of
a *weakly* monotone `k`-th derivative tending to `0`, is enough.  The genuine theorem
requires the `k`-th derivative `iteratedDerivWithin k f (Ici 1)` to be **strictly** monotone
(equivalently, of one strict sign, since it also tends to `0`), so that no tail of `f` is a
polynomial — precisely the behaviour of a real Puiseux branch of an algebraic function at
infinity, which is what feeds `int_root_locus_large_cover`.

Under that hypothesis the set of integers `1 ≤ t ≤ N` at which `f` takes an integer value
grows sublinearly: its cardinality is `O(N^α)` for some `α < 1`.

This is the genuinely deep analytic input (the one-variable Bombieri–Pila determinant
method / Jarník's theorem on integer points on convex arcs).  It is now **proved** (as
`graph_integer_points_sublinear` below) from the elementary divided-difference development
in `InverseGalois/NumberTheory/IntegerPointsSublinear.lean`, under the honest hypothesis `HasKDerivDecay`
(a polynomial decay rate `|f⁽ᵏ⁾(x)| ≤ C₀·x^(-β)` on `f⁽ᵏ⁾`).  A *fixed* power saving
`O(Nᵅ)` genuinely requires such a rate: with only `f⁽ᵏ⁾ → 0` the count is `o(N)` but not
`O(Nᵅ)` for any fixed `α < 1`.  Every real algebraic Puiseux branch at infinity satisfies
the rate. -/
/-- **A polynomial decay rate on the `k`-th derivative.**  `|f⁽ᵏ⁾(x)| ≤ C₀·x^(-β)` on
`[1, ∞)` for some `β > 0`.  This is the (genuine) hypothesis under which a fixed power
saving `O(Nᵅ)` holds; it is satisfied by every real algebraic Puiseux branch at infinity
(whose `k`-th derivative behaves like `c·x^{r-k}`). -/
def HasKDerivDecay (f : ℝ → ℝ) (k : ℕ) : Prop :=
  ∃ C₀ β : ℝ, 0 < β ∧ ∀ x : ℝ, (1 : ℝ) ≤ x →
    |iteratedDerivWithin k f (Set.Ici 1) x| ≤ C₀ * x ^ (-β)

lemma graph_integer_points_sublinear
    (f : ℝ → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hf : ContDiffOn ℝ k f (Set.Ici (1 : ℝ)))
    (hmono : StrictMonoOn (iteratedDerivWithin k f (Set.Ici 1)) (Set.Ici 1) ∨
        StrictAntiOn (iteratedDerivWithin k f (Set.Ici 1)) (Set.Ici 1))
    (hrate : HasKDerivDecay f k) :
    ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard {t : ℤ | (1 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (N : ℝ) ∧
          ∃ m : ℤ, f (t : ℝ) = (m : ℝ)} : ℝ) ≤ C * (N : ℝ) ^ α := by
  obtain ⟨C₀, β, hβ, hr⟩ := hrate
  exact IntegerPointsSublinear.integerValue_count_sublinear f k hk hf hmono C₀ β hβ hr

/-! ### Decomposition of `int_root_locus_large_cover`

The large-root cover is assembled from three geometrically distinct pieces of the
integer-root locus:

* the **positive-`t` branches** (`posBranchesUnion`): for `t ≥ T₀` every integer root is a
  value `y = gⱼ(t)` of one of finitely many real algebraic branches `gⱼ` at `+∞`;
* the **negative-`t` branches** (`negBranchesUnion`): symmetrically for `t ≤ -T₀`, via
  branches `hⱼ(-t)`;
* the **bounded core** `|t| < T₀`, a fixed finite set independent of `N`. -/

/-- The union of the positive-`t` branch loci: integers `t` with `1 ≤ t ≤ N` at which some
branch function `g j` takes an integer value. -/
def posBranchesUnion (n : ℕ) (g : Fin n → ℝ → ℝ) (N : ℕ) : Set ℤ :=
  ⋃ j, {t : ℤ | (1 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (N : ℝ) ∧ ∃ m : ℤ, g j (t : ℝ) = (m : ℝ)}

/-- The union of the negative-`t` branch loci: integers `t` with `1 ≤ -t ≤ N` at which some
branch function `h j` takes an integer value at `-t`. -/
def negBranchesUnion (n : ℕ) (h : Fin n → ℝ → ℝ) (N : ℕ) : Set ℤ :=
  ⋃ j, {t : ℤ | (1 : ℝ) ≤ (-(t : ℝ)) ∧ (-(t : ℝ)) ≤ (N : ℝ) ∧
      ∃ m : ℤ, h j (-(t : ℝ)) = (m : ℝ)}

/-
**Reflected form of `graph_integer_points_sublinear`.**  Counting integers `t` with
`1 ≤ -t ≤ N` at which `f(-t)` is an integer is the same (after `t ↦ -t`) as counting
integer values of `f` on `[1, N]`, hence sublinear.
-/
lemma graph_integer_points_sublinear_neg
    (f : ℝ → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hf : ContDiffOn ℝ k f (Set.Ici (1 : ℝ)))
    (hmono : StrictMonoOn (iteratedDerivWithin k f (Set.Ici 1)) (Set.Ici 1) ∨
        StrictAntiOn (iteratedDerivWithin k f (Set.Ici 1)) (Set.Ici 1))
    (hrate : HasKDerivDecay f k) :
    ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard {t : ℤ | (1 : ℝ) ≤ (-(t : ℝ)) ∧ (-(t : ℝ)) ≤ (N : ℝ) ∧
          ∃ m : ℤ, f (-(t : ℝ)) = (m : ℝ)} : ℝ) ≤ C * (N : ℝ) ^ α := by
  obtain ⟨C, α, hC, hα, hα', h⟩ := graph_integer_points_sublinear f k hk hf hmono hrate
  refine ⟨C, α, hC, hα, hα', fun N hN ↦ ?_⟩
  convert h N hN using 1
  rw [← Set.ncard_image_of_injective _ neg_injective]
  congr
  ext
  simp

/-
**A locus contained in a fixed integer interval is sublinear** (indeed bounded).
Used for the bounded core `|t| < T₀`, whose size does not depend on `N`.
-/
lemma ncard_inter_Icc_sublinear (a b : ℤ) (S : ℕ → Set ℤ)
    (hsub : ∀ N, S N ⊆ Set.Icc a b) :
    ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard (S N) : ℝ) ≤ C * (N : ℝ) ^ α := by
  refine ⟨1 + (Set.ncard (Set.Icc a b) : ℝ), 0, ?_, ?_, ?_, ?_⟩ <;> norm_num
  · positivity
  · intro N hN
    norm_cast
    exact le_add_of_nonneg_of_le zero_le_one (Set.ncard_le_ncard (hsub N))

/-
**Combining three sublinear finite covers into one `Fin`-indexed cover.**
If `S N ⊆ A N ∪ B N ∪ D N` and each of `A, B, D` is finite and sublinear, then `S` is
covered by the three-element family `![A, B, D]`.
-/
lemma three_cover (S A B D : ℕ → Set ℤ)
    (hcov : ∀ N, S N ⊆ A N ∪ B N ∪ D N)
    (hAf : ∀ N, (A N).Finite) (hBf : ∀ N, (B N).Finite) (hDf : ∀ N, (D N).Finite)
    (hA : ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
        (Set.ncard (A N) : ℝ) ≤ C * (N : ℝ) ^ α)
    (hB : ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
        (Set.ncard (B N) : ℝ) ≤ C * (N : ℝ) ^ α)
    (hD : ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
        (Set.ncard (D N) : ℝ) ≤ C * (N : ℝ) ^ α) :
    ∃ (n : ℕ) (T : Fin n → ℕ → Set ℤ),
      (∀ N : ℕ, S N ⊆ ⋃ j, T j N) ∧
      (∀ (j : Fin n) (N : ℕ), (T j N).Finite) ∧
      (∀ j : Fin n, ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
          (Set.ncard (T j N) : ℝ) ≤ C * (N : ℝ) ^ α) := by
  refine ⟨3, fun j N ↦ if j = 0 then A N else if j = 1 then B N else D N, ?_, ?_, ?_⟩ <;> simp [Fin.forall_fin_succ]
  · intro N x hx
    specialize hcov N hx
    simp_all [Fin.exists_fin_succ]
    tauto
  · tauto
  · refine ⟨?_, ?_, ?_⟩
    · obtain ⟨C, α, hC, hα, hα', h⟩ := hA
      exact ⟨C, hC, α, hα, hα', h⟩
    · obtain ⟨C, α, hC, hα, hα', h⟩ := hB
      exact ⟨C, hC, α, hα, hα', h⟩
    · obtain ⟨C, α, hC, hα, hα', h⟩ := hD
      exact ⟨C, hC, α, hα, hα', h⟩

/-
**Positive branches are finite and grow sublinearly.**  Each branch locus is exactly a
`graph_integer_points_sublinear` set, and the finite union of sublinear sets is sublinear
(`sublinear_finite_cover`).
-/
lemma pos_branches_cover_sublinear (n k : ℕ) (hk : 2 ≤ k) (g : Fin n → ℝ → ℝ)
    (hg_cd : ∀ j, ContDiffOn ℝ k (g j) (Set.Ici (1 : ℝ)))
    (hg_mono : ∀ j, StrictMonoOn (iteratedDerivWithin k (g j) (Set.Ici 1)) (Set.Ici 1) ∨
        StrictAntiOn (iteratedDerivWithin k (g j) (Set.Ici 1)) (Set.Ici 1))
    (hg_rate : ∀ j, HasKDerivDecay (g j) k) :
    (∀ N, (posBranchesUnion n g N).Finite) ∧
    (∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard (posBranchesUnion n g N) : ℝ) ≤ C * (N : ℝ) ^ α) := by
  constructor
  · intro N
    apply Set.Finite.subset (Set.finite_Icc (1 : ℤ) (N : ℤ))
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    refine ⟨?_, ?_⟩
    · exact_mod_cast hj.1
    · exact_mod_cast hj.2.1
  · convert sublinear_finite_cover (posBranchesUnion n g)
      (fun j N ↦ {t : ℤ | (1 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ N ∧ ∃ m : ℤ, g j (t : ℝ) = (m : ℝ)})
      ?_ ?_ ?_ using 1
    · exact fun N ↦ Set.iUnion_subset fun j ↦
        Set.subset_iUnion
          (fun j ↦ {t : ℤ | 1 ≤ (t : ℝ) ∧ (t : ℝ) ≤ N ∧ ∃ m : ℤ, g j (t : ℝ) = m}) j
    · exact fun j N ↦ Set.Finite.subset (Set.finite_Icc (1 : ℤ) N) fun x hx ↦ ⟨mod_cast hx.1, mod_cast hx.2.1⟩
    · exact fun j ↦ graph_integer_points_sublinear (g j) k hk (hg_cd j) (hg_mono j) (hg_rate j)

/-
**Negative branches are finite and grow sublinearly.**  Same as
`pos_branches_cover_sublinear` using the reflected estimate
`graph_integer_points_sublinear_neg`.
-/
lemma neg_branches_cover_sublinear (n k : ℕ) (hk : 2 ≤ k) (h : Fin n → ℝ → ℝ)
    (hh_cd : ∀ j, ContDiffOn ℝ k (h j) (Set.Ici (1 : ℝ)))
    (hh_mono : ∀ j, StrictMonoOn (iteratedDerivWithin k (h j) (Set.Ici 1)) (Set.Ici 1) ∨
        StrictAntiOn (iteratedDerivWithin k (h j) (Set.Ici 1)) (Set.Ici 1))
    (hh_rate : ∀ j, HasKDerivDecay (h j) k) :
    (∀ N, (negBranchesUnion n h N).Finite) ∧
    (∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard (negBranchesUnion n h N) : ℝ) ≤ C * (N : ℝ) ^ α) := by
  constructor
  · intro N
    have h_finite : ∀ j, Set.Finite
        {t : ℤ | (1 : ℝ) ≤ (-(t : ℝ)) ∧ (-(t : ℝ)) ≤ (N : ℝ) ∧ ∃ m : ℤ, h j (-(t : ℝ)) = m} := by
      intro j
      apply Set.Finite.subset (Set.finite_Icc (-N : ℤ) (-1 : ℤ))
      intro t ht
      norm_num
      obtain ⟨ht₁, ht₂, m, hm⟩ := ht
      refine ⟨?_, ?_⟩
      · have h1 : (-N : ℝ) ≤ t := by linarith
        exact_mod_cast h1
      · have h2 : (t : ℝ) ≤ -1 := by linarith
        exact_mod_cast h2
    exact Set.finite_iUnion h_finite
  · convert sublinear_finite_cover (negBranchesUnion n h)
      (fun j N ↦ {t : ℤ | (1 : ℝ) ≤ (-(t : ℝ)) ∧ (-(t : ℝ)) ≤ N ∧ ∃ m : ℤ, h j (-(t : ℝ)) = (m : ℝ)})
      ?_ ?_ ?_ using 1
    · exact fun N ↦ Set.iUnion_subset fun j ↦
        Set.subset_iUnion
          (fun j ↦ {t : ℤ | (1 : ℝ) ≤ (-(t : ℝ)) ∧ (-(t : ℝ)) ≤ N ∧ ∃ m : ℤ, h j (-(t : ℝ)) = m}) j
    · intro j N
      apply Set.Finite.subset (Set.finite_Icc (-N : ℤ) (-1 : ℤ))
      intro t ht
      refine ⟨?_, ?_⟩
      · have h1 : (-N : ℝ) ≤ t := by linarith [ht.1, ht.2.1]
        exact_mod_cast h1
      · have h2 : (t : ℝ) ≤ -1 := by linarith [ht.1, ht.2.1]
        exact_mod_cast h2
    · exact fun j ↦ graph_integer_points_sublinear_neg (h j) k hk (hh_cd j) (hh_mono j) (hh_rate j)

/-
**Analytic package for a pure power branch `x ↦ c · x^r` (`r ∉ ℕ`).**

This is the model case of a real algebraic branch at infinity: a non-polynomial power
function. It supplies *exactly* the smoothness / strictly-monotone-decaying `k`-th
derivative structure required by `graph_integer_points_sublinear` (and hence packaged, for
the genuine algebraic branches, inside `large_root_branch_data`).

Concretely, for a nonzero constant `c`, a real exponent `r` that is **not** a natural number
(so no branch is a polynomial — the shadow of `P` having no rational root), and any
`k ≥ 2` with `r < k`, the function `f x = c · x^r` is `C^k` on `[1, ∞)`, its `k`-th
derivative
`iteratedDerivWithin k f [1,∞) x = c · (r)(r-1)⋯(r-k+1) · x^{r-k}`
is strictly monotone on `[1, ∞)` (the exponent `r - k < 0` and the falling factorial is
nonzero because `r ∉ ℕ`) and tends to `0` at `+∞`.

The key Mathlib inputs are `Real.iter_deriv_rpow_const` (closed form of the iterated
derivative of `x^r`) and `iteratedDerivWithin_eq_iteratedDeriv` (to transfer it to
`iteratedDerivWithin … (Ici 1)`).
-/
lemma rpow_mul_analytic_package (c r : ℝ) (k : ℕ)
    (_hk : 2 ≤ k) (hrk : r < (k : ℝ)) (hc : c ≠ 0)
    (hr : ∀ j : ℕ, r ≠ (j : ℝ)) :
    ContDiffOn ℝ k (fun x ↦ c * x ^ r) (Set.Ici (1 : ℝ)) ∧
    (StrictMonoOn (iteratedDerivWithin k (fun x ↦ c * x ^ r) (Set.Ici 1)) (Set.Ici 1) ∨
      StrictAntiOn (iteratedDerivWithin k (fun x ↦ c * x ^ r) (Set.Ici 1)) (Set.Ici 1)) ∧
    Filter.Tendsto (iteratedDerivWithin k (fun x ↦ c * x ^ r) (Set.Ici 1)) Filter.atTop
      (nhds 0) := by
  constructor
  · refine ContDiffOn.mul contDiffOn_const ?_
    refine ContDiffOn.rpow contDiffOn_id contDiffOn_const <| ?_
    intro x hx
    linarith [Set.mem_Ici.mp hx]
  · constructor
    -- The `k`-th derivative of `f` is `c · (descPochhammer ℝ k).eval r · x^(r-k)`.
    · have h_deriv : ∀ x ∈ Set.Ici 1, iteratedDerivWithin k (fun x ↦ c * x ^ r) (Set.Ici 1) x
          = c * (Polynomial.eval r (descPochhammer ℝ k)) * x ^ (r - k) := by
        intro x hx
        rw [iteratedDerivWithin_eq_iteratedDeriv]
        · have := @Real.iter_deriv_rpow_const r x k
          simp_all [mul_comm, mul_left_comm, iteratedDeriv_eq_iterate]
        · exact uniqueDiffOn_Ici _
        · exact ContDiffAt.mul contDiffAt_const
            (ContDiffAt.rpow contDiffAt_id contDiffAt_const <| by linarith [Set.mem_Ici.mp hx])
        · exact hx
      -- Since `c ≠ 0` and `r ∉ ℕ`, the factor `c · (descPochhammer ℝ k).eval r` is nonzero.
      have h_nonzero : c * (Polynomial.eval r (descPochhammer ℝ k)) ≠ 0 := by
        rw [descPochhammer_eval_eq_prod_range]
        exact mul_ne_zero hc <| Finset.prod_ne_zero_iff.mpr fun i hi ↦ sub_ne_zero_of_ne <| hr i
      cases lt_or_gt_of_ne h_nonzero <;> simp_all [StrictMonoOn, StrictAntiOn]
      · exact Or.inl fun a ha b hb hab ↦ by rw [Real.rpow_lt_rpow_iff_of_neg] <;> linarith
      · exact Or.inr fun a ha b hb hab ↦ by rw [Real.rpow_lt_rpow_iff_of_neg] <;> linarith
    -- The `k`-th derivative of `f` is `c · (∏ i ∈ range k, (r - i)) · x^(r-k)`.
    · have h_deriv : ∀ x ∈ Set.Ioi (1 : ℝ), iteratedDerivWithin k (fun x ↦ c * x ^ r) (Set.Ici 1) x
          = c * (∏ i ∈ Finset.range k, (r - i)) * x ^ (r - k) := by
        intro x hx
        convert iteratedDerivWithin_eq_iteratedDeriv _ _ _ using 1
        · simp [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
          rw [descPochhammer_eval_eq_prod_range]
          ring
        · exact uniqueDiffOn_Ici _
        · exact ContDiffAt.mul contDiffAt_const (ContDiffAt.rpow contDiffAt_id contDiffAt_const <| by linarith [hx.out])
        · exact hx.out.le
      rw [Filter.tendsto_congr' (Filter.eventuallyEq_of_mem (Filter.Ioi_mem_atTop 1) h_deriv)]
      simpa using tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (sub_pos.mpr hrk))

/-
**The pure power branch `x ↦ c·x^r` has a polynomial `k`-th-derivative decay rate**
(for `r < k`).  Its `k`-th derivative is `c·(descPochhammer r) · x^{r-k}`, so `|f⁽ᵏ⁾(x)| ≤
C₀·x^(-(k-r))` with `β = k - r > 0`.
-/
lemma rpow_mul_hasKDerivDecay (c r : ℝ) (k : ℕ) (_hk : 2 ≤ k) (hrk : r < (k : ℝ)) :
    HasKDerivDecay (fun x ↦ c * x ^ r) k := by
  refine ⟨|c * (Polynomial.eval r (descPochhammer ℝ k))|, (k : ℝ) - r, sub_pos.mpr hrk, fun x hx ↦ ?_⟩
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 1)]
  · have h_deriv : iteratedDeriv k (fun x ↦ c * x ^ r) x
        = c * (Polynomial.eval r (descPochhammer ℝ k)) * x ^ (r - k) := by
      have := @Real.iter_deriv_rpow_const
      convert congr_arg (fun y ↦ c * y) (this r x k) using 1 <;> norm_num [mul_assoc, iteratedDeriv_eq_iterate]
    rw [h_deriv, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    ring_nf
    norm_num
  · exact ContDiffAt.mul contDiffAt_const (ContDiffAt.rpow contDiffAt_id contDiffAt_const <| by positivity)
  · exact hx

/-
**Analytic package from a sign-definite `(k+1)`-th derivative.**

A convenient reduction of the smoothness / strictly-monotone-decaying `k`-th derivative
package required by `graph_integer_points_sublinear` (and produced, for the genuine
algebraic branches, by `large_root_branch_data`).  Instead of checking strict monotonicity
of the `k`-th derivative directly, it suffices to exhibit a *sign-definite* `(k+1)`-th
derivative on the interior `(1, ∞)` (together with the `k`-th derivative tending to `0`):
strict positivity of `f^{(k+1)}` makes `f^{(k)}` strictly increasing, strict negativity
makes it strictly decreasing.  This is exactly the shape one gets for a real algebraic
branch, whose `(k+1)`-th derivative behaves like a nonzero constant times `x^{r-k-1}`.
-/
lemma analytic_package_of_kSucc_deriv (f : ℝ → ℝ) (k : ℕ) (_hk : 2 ≤ k)
    (hf : ContDiffOn ℝ (k + 1) f (Set.Ici (1 : ℝ)))
    (hsign : (∀ x ∈ Set.Ioi (1 : ℝ), 0 < iteratedDerivWithin (k + 1) f (Set.Ici 1) x) ∨
             (∀ x ∈ Set.Ioi (1 : ℝ), iteratedDerivWithin (k + 1) f (Set.Ici 1) x < 0))
    (htend : Filter.Tendsto (iteratedDerivWithin k f (Set.Ici 1)) Filter.atTop (nhds 0)) :
    ContDiffOn ℝ k f (Set.Ici 1) ∧
    (StrictMonoOn (iteratedDerivWithin k f (Set.Ici 1)) (Set.Ici 1) ∨
      StrictAntiOn (iteratedDerivWithin k f (Set.Ici 1)) (Set.Ici 1)) ∧
    Filter.Tendsto (iteratedDerivWithin k f (Set.Ici 1)) Filter.atTop (nhds 0) := by
  refine ⟨hf.of_le ?_, ?_, htend⟩
  · exact_mod_cast Nat.le_succ _
  · cases' hsign with hsign hsign
    · refine Or.inl ?_
      apply strictMonoOn_of_deriv_pos
      · exact convex_Ici _
      · convert hf.continuousOn_iteratedDerivWithin _ _ using 1
        · norm_cast
          linarith
        · exact uniqueDiffOn_Ici _
      · intro x hx
        specialize hsign x
        simp_all [iteratedDerivWithin_succ]
        rwa [derivWithin_of_mem_nhds (Ici_mem_nhds hx)] at hsign
    · refine Or.inr (strictAntiOn_of_deriv_neg (convex_Ici 1) ?_ ?_)
      · apply ContDiffOn.continuousOn_iteratedDerivWithin hf _ (uniqueDiffOn_Ici _)
        norm_cast
        linarith
      · simp_all [iteratedDerivWithin_succ]
        intro x hx
        specialize hsign x hx
        rw [derivWithin_of_mem_nhds (Ici_mem_nhds hx)] at hsign
        linarith


end
