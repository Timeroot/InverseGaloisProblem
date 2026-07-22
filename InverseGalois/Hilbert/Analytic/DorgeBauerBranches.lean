/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Hilbert.Analytic.DorgeBauer

/-!
# Real algebraic branches for the Dörge–Bauer argument

This file develops the real-branch infrastructure used in the analytic counting stage of
Dörge–Bauer.  It contains reflection in the parameter, tail extensions, ordered real root
branches, polynomial growth, and eventual no-switching of a continuous root selection.

The foundational algebra, coefficient bounds, and counting lemmas remain in
`DorgeBauer.lean`; complex continuation and finite Puiseux computations are in
`DorgeBauerAnalytic.lean`.
-/

open Polynomial ResolventConstruction

noncomputable section

/-!
### Decomposition of `large_root_branch_data`

* `reflectT` and its four algebraic lemmas reduce the `-∞` direction to the `+∞`
  direction: `(reflectT P)(s, Y) = P(-s, Y)`, and monicity / `Y`-degree / the
  no-`ℚ(T)`-root hypothesis are all preserved.
* `dummyBranch` (the model branch `x ↦ √x`) carries the full analytic package for every
  `k ≥ 2`; it is used to pad the two branch families to a common size.
* `real_branches_sign_deriv_pos` is the *reduced analytic core*: it only has to produce
  the `+∞` branches together with a **sign-definite `(k+1)`-th derivative** (plus the
  `k`-th derivative tending to `0`) — the shape that `analytic_package_of_kSucc_deriv`
  turns into the strictly-monotone-decaying package.  It is stated `∀ k ≥ k₀` so that the
  `g`- and `h`-families can later be forced onto a common derivative order `k`.
* `branch_data_pos` assembles the full `+∞` package from the core via
  `analytic_package_of_kSucc_deriv`.
* `large_root_branch_data` finally glues the `+∞` package of `P` (the `g`'s) and the
  `+∞` package of `reflectT P` (the `h`'s), padding with `dummyBranch`. -/

/-- Reflection `T ↦ -T` of the base ring `ℤ[T]`, lifted coefficientwise to `ℤ[T][Y]`.
It satisfies `(reflectT P)(s, Y) = P(-s, Y)` (see `reflectT_evalRingHom`), which lets the
`-∞` branch analysis be reduced to the `+∞` analysis. -/
noncomputable def reflectT (P : Polynomial (Polynomial ℤ)) : Polynomial (Polynomial ℤ) :=
  P.map (Polynomial.aeval (-Polynomial.X : Polynomial ℤ)).toRingHom

/-- Evaluating the reflected polynomial at `T := s` is the same as evaluating the original
at `T := -s`. -/
lemma reflectT_evalRingHom (P : Polynomial (Polynomial ℤ)) (s : ℤ) :
    (reflectT P).map (Polynomial.evalRingHom s) = P.map (Polynomial.evalRingHom (-s)) := by
  rw [reflectT, Polynomial.map_map]
  congr 1
  apply Polynomial.ringHom_ext
  · intro n
    simp
  · simp

/-- Reflection preserves monicity in `Y`. -/
lemma reflectT_monic {P : Polynomial (Polynomial ℤ)} (hP : P.Monic) : (reflectT P).Monic :=
  hP.map _

/-- Reflection preserves the `Y`-degree. -/
lemma reflectT_natDegree (P : Polynomial (Polynomial ℤ)) :
    (reflectT P).natDegree = P.natDegree := by
  rw [reflectT]
  apply natDegree_map_eq_of_injective
  have hinv : ∀ p : Polynomial ℤ,
      (Polynomial.aeval (-Polynomial.X : Polynomial ℤ)).toRingHom
        ((Polynomial.aeval (-Polynomial.X : Polynomial ℤ)).toRingHom p) = p := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | monomial n a _ => simp
  exact Function.LeftInverse.injective hinv

/-
Reflection preserves the "no root in `ℚ(T)`" hypothesis.
-/
lemma reflectT_no_root {P : Polynomial (Polynomial ℤ)}
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) :
    ∀ a : FractionRing (Polynomial ℚ), ¬ ((reflectT P).map toRatFunc).IsRoot a := by
  -- Choose any `a` in the fraction field of `ℚ[X]`.
  intro a
  by_contra h_contra
  -- Let's obtain the ℚ[T]-automorphism `hσ` induced by `X ↦ -X`.
  obtain ⟨hσ, hσ_inv⟩ : ∃ hσ : Polynomial ℚ ≃+* Polynomial ℚ, ∀ p : Polynomial ℚ, hσ p = p.comp (-Polynomial.X) := by
    refine ⟨?_, ?_⟩
    · refine' { Equiv.ofBijective (fun p ↦ p.comp (-Polynomial.X)) ⟨fun p q h ↦ _, fun p ↦ _⟩ with .. }
      any_goals
        intros
        simp
      · exact Polynomial.funext fun x ↦ by simpa using congr_arg (Polynomial.eval (-x)) h
      · exact ⟨p.comp (-Polynomial.X), by simp [Polynomial.comp_assoc]⟩
    · intro p
      simp
  -- Let's obtain the automorphism `τ` of the fraction field `K` induced by `hσ`.
  obtain ⟨τ, hτ⟩ :
      ∃ τ : FractionRing (Polynomial ℚ) ≃+* FractionRing (Polynomial ℚ),
        ∀ p : Polynomial ℚ,
          τ (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) p) =
            algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) (hσ p) :=
    ⟨IsFractionRing.ringEquivOfRingEquiv hσ, fun p ↦ IsFractionRing.ringEquivOfRingEquiv_algebraMap hσ p⟩
  -- The commutation `τ.toRingHom.comp toRatFunc = toRatFunc.comp σ`.
  have h_comm :
      τ.toRingHom.comp toRatFunc = toRatFunc.comp (Polynomial.aeval (-Polynomial.X : Polynomial ℤ)).toRingHom := by
    ext
    · simp [toRatFunc]
    · convert hτ (Polynomial.X) using 1
      · simp [toRatFunc]
      · simp [toRatFunc, hσ_inv]
  -- Rewrite `(reflectT P).map toRatFunc = P.map (τ.toRingHom.comp toRatFunc)`.
  have h_map : (reflectT P).map toRatFunc = P.map (τ.toRingHom.comp toRatFunc) := by
    unfold reflectT
    aesop
  -- Rewrite `(P.map (τ.toRingHom.comp toRatFunc)).eval a = τ ((P.map toRatFunc).eval (τ.symm a))`.
  have h_eval : (P.map (τ.toRingHom.comp toRatFunc)).eval a = τ ((P.map toRatFunc).eval (τ.symm a)) := by
    simp [Polynomial.eval_map]
    simp [Polynomial.eval₂_eq_sum_range]
  simp_all [Polynomial.IsRoot]

/-- A fixed model branch `x ↦ √x` used to pad the two branch families to a common size.
It carries the full analytic package for every `k ≥ 2`. -/
noncomputable def dummyBranch : ℝ → ℝ := fun x ↦ x ^ (1 / 2 : ℝ)

/-- The model branch `x ↦ √x` has the strictly-monotone-decaying `k`-th derivative
package for every `k ≥ 2`.  Immediate from `rpow_mul_analytic_package` with `c = 1`,
`r = 1/2`. -/
lemma dummyBranch_package (k : ℕ) (hk : 2 ≤ k) :
    ContDiffOn ℝ k dummyBranch (Set.Ici (1 : ℝ)) ∧
    (StrictMonoOn (iteratedDerivWithin k dummyBranch (Set.Ici 1)) (Set.Ici 1) ∨
      StrictAntiOn (iteratedDerivWithin k dummyBranch (Set.Ici 1)) (Set.Ici 1)) ∧
    Filter.Tendsto (iteratedDerivWithin k dummyBranch (Set.Ici 1)) Filter.atTop (nhds 0) ∧
    HasKDerivDecay dummyBranch k := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h := rpow_mul_analytic_package 1 (1 / 2) k hk
    (by linarith) (by norm_num)
    (by
      intro j hj
      have h1 : (1 : ℝ) = 2 * j := by linarith
      have h2 : (1 : ℤ) = 2 * j := by exact_mod_cast h1
      omega)
  have hrate := rpow_mul_hasKDerivDecay 1 (1 / 2) k hk (by linarith)
  have hfun : (fun x : ℝ ↦ (1 : ℝ) * x ^ (1 / 2 : ℝ)) = dummyBranch := by
    funext x
    simp [dummyBranch, one_mul]
  rw [hfun] at h hrate
  exact ⟨h.1, h.2.1, h.2.2, hrate⟩

/-- **Witness that the `∀ k`-uniform branch statement is unattainable.**

For the branch `φ(x) = x^{4/3} + x^{1/3}` of `P = Y³ - T·(T+1)³` (see the discussion in
`real_branches_sign_deriv_pos`), the third derivative
`φ'''(x) = (2/27)·x^{-8/3}·(5 - 4x)` is **positive** at `x = 11/10 > 1` and **negative**
at `x = 2`, so `φ'''` is not sign-definite on `(1,∞)`.  Since covering forces any branch
function to agree with `φ` at the integer roots (`t = s³ ↦ s⁴ + s = φ(t)`), no single
family can have a sign-definite `(k+1)`-th derivative on all of `(1,∞)` for `k = 2`; the
sign-change threshold only grows with `k`.  This is what makes the per-`k` choice of `T₀`
and `g` in `real_branches_sign_deriv_pos` necessary. -/
lemma dorge_branch_third_deriv_sign_change :
    (0 < iteratedDeriv 3 (fun x : ℝ ↦ x ^ (4/3:ℝ) + x ^ (1/3:ℝ)) (11/10)) ∧
      iteratedDeriv 3 (fun x : ℝ ↦ x ^ (4/3:ℝ) + x ^ (1/3:ℝ)) 2 < 0 := by
  have hcd : ∀ (r : ℝ) (x : ℝ), 0 < x → ContDiffAt ℝ 3 (fun x : ℝ ↦ x ^ r) x := by
    intro r x hx
    exact Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)
  have key : ∀ x : ℝ, 0 < x →
      iteratedDeriv 3 (fun x : ℝ ↦ x ^ (4/3:ℝ) + x ^ (1/3:ℝ)) x
        = x ^ (-(8:ℝ)/3) * ((2/27) * (5 - 4*x)) := by
    intro x hx
    rw [show (fun x : ℝ ↦ x ^ (4/3:ℝ) + x ^ (1/3:ℝ))
          = (fun x : ℝ ↦ x ^ (4/3:ℝ)) + (fun x : ℝ ↦ x ^ (1/3:ℝ)) from rfl]
    rw [iteratedDeriv_add (hcd _ x hx) (hcd _ x hx)]
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
        Real.iter_deriv_rpow_const, Real.iter_deriv_rpow_const,
        descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_prod_range]
    have he1 : ((4:ℝ)/3 - (3:ℕ)) = -(8:ℝ)/3 + 1 := by
      push_cast
      ring
    have h1 : x ^ ((4:ℝ)/3 - (3:ℕ)) = x ^ (-(8:ℝ)/3) * x := by
      rw [he1, Real.rpow_add hx, Real.rpow_one]
    have he2 : ((1:ℝ)/3 - (3:ℕ)) = -(8:ℝ)/3 := by
      push_cast
      ring
    have h2 : x ^ ((1:ℝ)/3 - (3:ℕ)) = x ^ (-(8:ℝ)/3) := by
      rw [he2]
    rw [h1, h2]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · rw [key _ (by norm_num)]
    apply mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    norm_num
  · rw [key _ (by norm_num)]
    apply mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos (by norm_num) _)
    norm_num

/-
**Finite-order gluing.**  If `f` is `C^n` on `[c,∞)` and all its within-derivatives up
to order `n` vanish at the endpoint `c`, then extending `f` by `0` to the left of `c` gives a
globally `C^n` function on `ℝ`.  Proved by induction on `n`, differentiating the extension
and recognising its derivative as the extension-by-zero of `derivWithin f (Ici c)`.
-/
lemma contDiff_extend_by_zero {n : ℕ} {c : ℝ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ n f (Set.Ici c))
    (hvanish : ∀ j ≤ n, iteratedDerivWithin j f (Set.Ici c) c = 0) :
    ContDiff ℝ n (fun x ↦ if c ≤ x then f x else 0) := by
  induction' n with n ih generalizing f c
  · simp_all [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = c
    · rw [Metric.continuousAt_iff]
      intro ε hε
      have := Metric.continuousOn_iff.mp hf c (by norm_num) ε hε
      simp_all [dist_eq_norm]
      obtain ⟨δ, hδ, H⟩ := this
      refine ⟨δ, hδ, fun x hx ↦ ?_⟩
      split_ifs <;> simp [*]
    · by_cases hx' : x < c
      · exact ContinuousAt.congr (continuousAt_const)
          (Filter.EventuallyEq.symm <|
            Filter.eventuallyEq_of_mem (Iio_mem_nhds hx') fun y hy ↦ if_neg hy.out.not_ge)
      · have hlt : c < x := lt_of_le_of_ne (le_of_not_gt hx') (Ne.symm hx)
        exact ContinuousAt.congr (hf.continuousAt <| Ici_mem_nhds hlt)
          (Filter.EventuallyEq.symm <| Filter.eventuallyEq_of_mem (Ioi_mem_nhds hlt) fun y hy ↦ if_pos hy.out.le)
  · have h_deriv :
        ∀ x, HasDerivAt (fun x ↦ if c ≤ x then f x else 0) (if c ≤ x then derivWithin f (Set.Ici c) x else 0) x := by
      intro x
      by_cases hx : c ≤ x
      · by_cases hx' : x = c
        · have hdz_f : HasDerivWithinAt f 0 (Set.Ici c) c := by
            have hdz_dw : derivWithin f (Set.Ici c) c = 0 := by
              simpa using hvanish 1 (by linarith)
            have hdz_diff : DifferentiableWithinAt ℝ f (Set.Ici c) c :=
              hf.differentiableOn (by norm_num) c (by norm_num)
            convert hdz_diff.hasDerivWithinAt using 1
            aesop
          have hdz_Ici : HasDerivWithinAt (fun x ↦ if c ≤ x then f x else 0) 0 (Set.Ici c) c := by
            apply hdz_f.congr (fun x hx ↦ by aesop)
            aesop
          have hdz_Iic : HasDerivWithinAt (fun x ↦ if c ≤ x then f x else 0) 0 (Set.Iic c) c := by
            rw [hasDerivWithinAt_iff_tendsto] at *
            rw [Metric.tendsto_nhdsWithin_nhds] at *
            intro ε hε
            use 1
            norm_num
            intro x hx₁ hx₂
            split_ifs <;> norm_num at *
            · norm_num [show x = c by linarith]
              linarith
            · specialize hvanish 0
              aesop
          have hdz_union : HasDerivWithinAt (fun x ↦ if c ≤ x then f x else 0) 0 (Set.Ici c ∪ Set.Iic c) c :=
            HasDerivWithinAt.union hdz_Ici hdz_Iic
          convert hdz_union.hasDerivAt _ using 1
          · rw [hx', if_pos le_rfl, derivWithin]
            exact HasDerivWithinAt.derivWithin hdz_f (uniqueDiffOn_Ici c c <| by norm_num)
          · exact Filter.mem_of_superset (Metric.ball_mem_nhds _ zero_lt_one)
              fun x hx ↦ by cases le_total x c <;> aesop
        · have hlt : c < x := lt_of_le_of_ne hx <| Ne.symm hx'
          convert HasDerivAt.congr_of_eventuallyEq
            ((hf.differentiableOn (by norm_num)).hasDerivAt (Ici_mem_nhds hlt))
            (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hlt) fun y hy ↦ if_pos hy.out.le) using 1
          rw [if_pos hx, derivWithin_of_mem_nhds (Ici_mem_nhds hlt)]
      · exact HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const _ _)
          (Filter.eventuallyEq_of_mem (Iio_mem_nhds (lt_of_not_ge hx)) fun y hy ↦ if_neg hy.out.not_ge)
          |> HasDerivAt.congr_deriv <| by aesop
    have := @ih c (derivWithin f (Set.Ici c)) ?_ ?_ <;> simp_all
    · rw [contDiff_succ_iff_deriv]
      refine ⟨fun x ↦ (h_deriv x).differentiableAt, ?_, ?_⟩
      · tauto
      · rw [show deriv _ = _ from funext fun x ↦ HasDerivAt.deriv (h_deriv x)]
        exact this
    · exact hf.derivWithin (uniqueDiffOn_Ici c) (by aesop)
    · intro j hj
      specialize hvanish (j + 1) (by linarith)
      simp_all [iteratedDerivWithin_succ']

/-
Iterated derivatives of a finite Taylor-type sum `∑_{j≤m} b j · (x-c)^j` at the base
point `c`: the `i`-th derivative (for `i ≤ m`) picks out `b i · i!`.
-/
lemma iteratedDeriv_pow_sub_sum_at (m : ℕ) (c : ℝ) (b : ℕ → ℝ) (i : ℕ) (hi : i ≤ m) :
    iteratedDeriv i (fun x ↦ ∑ j ∈ Finset.range (m + 1), b j * (x - c) ^ j) c
      = b i * (Nat.factorial i) := by
  rw [iteratedDeriv_eq_iterate]
  -- By induction on `i`, the `i`-th derivative of `f x = ∑ j ∈ range (m+1), b j (x-c)^j` at `x = c` is `b i · i!`.
  have h_ind :
      ∀ i ≤ m, deriv^[i] (fun x ↦ ∑ j ∈ Finset.range (m + 1), b j * (x - c) ^ j) =
        fun x ↦ ∑ j ∈ Finset.range (m + 1), b j * Nat.descFactorial j i * (x - c) ^ (j - i) := by
    intro i hi
    induction' i with i ih <;> simp_all [Function.iterate_succ_apply']
    rw [ih (Nat.le_of_lt hi)]
    ext
    norm_num [mul_assoc, mul_comm, mul_left_comm, tsub_add_eq_tsub_tsub]
  simp_all
  rw [Finset.sum_eq_single i] <;> simp_all [Nat.descFactorial_self]
  exact fun j hj hij ↦
    if h : j < i then Or.inl <| Or.inr h
    else Or.inr <| Nat.sub_ne_zero_of_lt <| lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hij)

/-
The top iterated derivative (order `m`) of the Taylor-type sum `∑_{j≤m} b j · (x-c)^j`
is the constant `b m · m!`, for every `x`.
-/
lemma iteratedDeriv_pow_sub_sum_top (m : ℕ) (c : ℝ) (b : ℕ → ℝ) (x : ℝ) :
    iteratedDeriv m (fun x ↦ ∑ j ∈ Finset.range (m + 1), b j * (x - c) ^ j) x
      = b m * (Nat.factorial m) := by
  -- Apply the linearity of the derivative and the power rule.
  have h_deriv :
      ∀ k ≤ m, iteratedDeriv k (fun x ↦ ∑ j ∈ Finset.range (m + 1), b j * (x - c) ^ j) =
        fun x ↦ ∑ j ∈ Finset.range (m + 1), b j * Nat.descFactorial j k * (x - c) ^ (j - k) := by
    intro k hk
    induction' k with k ih <;> simp_all [iteratedDeriv_succ]
    rw [ih (Nat.le_of_lt hk)]
    ext x
    norm_num [Nat.sub_sub]
    ring_nf
    ac_rfl
  simp_all [Finset.sum_range_succ]
  simp [Nat.descFactorial_self, Finset.sum_range, Nat.descFactorial_eq_zero_iff_lt.mpr]

/-
**Extension of a branch tail from `[T₀,∞)` to `[1,∞)`.**

Given a function `f` that is `C^{k+1}` on `[T₀,∞)` (with `1 ≤ T₀`), whose `(k+1)`-th
derivative is sign-definite on `(T₀,∞)` and whose `k`-th derivative tends to `0` at `+∞`,
there is a function `g` defined and `C^{k+1}` on all of `[1,∞)` that:
* agrees with `f` on `[T₁,∞)` for some `T₁ ≥ T₀`;
* has a sign-definite `(k+1)`-th derivative on `(1,∞)`;
* has a `k`-th derivative tending to `0` at `+∞`.

Construction: pick `c > T₀` with `f^{(k+1)}(c) ≠ 0` (possible since `f^{(k+1)}` is
strictly of one sign on `(T₀,∞)`), and let `g` be `f` on `[c,∞)` and the degree-`(k+1)`
Taylor polynomial of `f` at `c` on `[1,c)`.  The two pieces agree to order `k+1` at `c`,
so `g` is `C^{k+1}`, and `g^{(k+1)}` equals the (constant, nonzero) value `f^{(k+1)}(c)`
below `c` and `f^{(k+1)}` (same sign) above `c`, hence is sign-definite on `(1,∞)`.  Since
`g = f` on `[c,∞)`, the `k`-th derivative decay is inherited.  This isolates the elementary
extension step from the genuinely deep branch-existence content.
-/
set_option maxHeartbeats 1600000 in
lemma extend_to_Ici_one (f : ℝ → ℝ) (k : ℕ) (_hk : 2 ≤ k) (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hf : ContDiffOn ℝ (k + 1) f (Set.Ici T₀))
    (hsign : (∀ x ∈ Set.Ioi T₀, 0 < iteratedDerivWithin (k + 1) f (Set.Ici T₀) x) ∨
             (∀ x ∈ Set.Ioi T₀, iteratedDerivWithin (k + 1) f (Set.Ici T₀) x < 0))
    (htend : Filter.Tendsto (iteratedDerivWithin k f (Set.Ici T₀)) Filter.atTop (nhds 0)) :
    ∃ (T₁ : ℝ) (g : ℝ → ℝ), T₀ ≤ T₁ ∧
      ContDiffOn ℝ (k + 1) g (Set.Ici (1 : ℝ)) ∧
      ((∀ x ∈ Set.Ioi (1 : ℝ), 0 < iteratedDerivWithin (k + 1) g (Set.Ici 1) x) ∨
        (∀ x ∈ Set.Ioi (1 : ℝ), iteratedDerivWithin (k + 1) g (Set.Ici 1) x < 0)) ∧
      Filter.Tendsto (iteratedDerivWithin k g (Set.Ici 1)) Filter.atTop (nhds 0) ∧
      (∀ x, T₁ ≤ x → g x = f x) := by
  cases' hsign with hsign_pos hsign_neg
  · -- Set `c := T₀ + 1`, so `1 < c`, `T₀ < c`, and `c ∈ Set.Ioi T₀`.
    set c := T₀ + 1 with hc_def
    have hc_pos : 1 < c := by
      linarith
    have hc_gt_T₀ : T₀ < c := by
      linarith
    have hc_mem_Ioi : c ∈ Set.Ioi T₀ := hc_gt_T₀
    -- Define the Taylor coefficients `b : ℕ → ℝ := fun j ↦ iteratedDeriv j f c / (Nat.factorial j)`, the polynomial `p : ℝ → ℝ := fun x ↦ ∑ j ∈ Finset.range (k+2), b j * (x - c)^j`, the correction `e : ℝ → ℝ := fun x ↦ if c ≤ x then (f x - p x) else 0`, and `g := fun x ↦ p x + e x`.
    set b : ℕ → ℝ := fun j ↦ iteratedDeriv j f c / (Nat.factorial j)
    set p : ℝ → ℝ := fun x ↦ ∑ j ∈ Finset.range (k + 2), b j * (x - c) ^ j
    set e : ℝ → ℝ := fun x ↦ if c ≤ x then (f x - p x) else 0
    set g : ℝ → ℝ := fun x ↦ p x + e x
    -- Show that `g` is `C^{k+1}` on `[1,∞)`.
    have hg_contDiff : ContDiff ℝ (k + 1) g := by
      apply_rules [ContDiff.add, contDiff_extend_by_zero]
      · exact ContDiff.sum fun _ _ ↦
          ContDiff.mul (contDiff_const) (ContDiff.pow (contDiff_id.sub contDiff_const) _)
      · apply ContDiffOn.sub
        · exact hf.mono (Set.Ici_subset_Ici.mpr hc_gt_T₀.le)
        · exact ContDiff.contDiffOn
            (ContDiff.sum fun _ _ ↦
              ContDiff.mul (contDiff_const) (ContDiff.pow (contDiff_id.sub contDiff_const) _))
      · intro j hj
        rw [iteratedDerivWithin_eq_iteratedDeriv]
        · have h_sub : iteratedDeriv j (fun x ↦ f x - p x) c = iteratedDeriv j f c - iteratedDeriv j p c := by
            apply iteratedDeriv_sub
            · exact (hf.contDiffAt (Ici_mem_nhds hc_gt_T₀)).of_le (mod_cast hj)
            · fun_prop
          have h_p_val : iteratedDeriv j p c = b j * (Nat.factorial j) :=
            iteratedDeriv_pow_sub_sum_at (k + 1) c b j (Nat.le_trans hj (Nat.le_refl _))
          rw [h_sub, h_p_val, div_mul_cancel₀ _ (by positivity), sub_self]
        · exact uniqueDiffOn_Ici _
        · apply ContDiffAt.sub
          · exact (hf.contDiffAt (Ici_mem_nhds hc_mem_Ioi)).of_le (mod_cast hj)
          · fun_prop
        · norm_num
    refine ⟨c, g, by linarith, hg_contDiff.contDiffOn, ?_, ?_, ?_⟩
    · -- For `x ∈ Set.Ioi 1`, `iteratedDerivWithin (k + 1) g (Set.Ici 1) x = iteratedDeriv (k + 1) g x`.
      have h_iteratedDerivWithin_eq_iteratedDeriv :
          ∀ x ∈ Set.Ioi 1, iteratedDerivWithin (k + 1) g (Set.Ici 1) x = iteratedDeriv (k + 1) g x := by
        intro x hx
        rw [iteratedDerivWithin_eq_iteratedDeriv]
        · exact uniqueDiffOn_Ici _
        · exact hg_contDiff.contDiffAt.of_le (by norm_num)
        · exact hx.out.le
      -- For `x < c`, `iteratedDeriv (k + 1) g x = iteratedDeriv (k + 1) p x = V`.
      have h_iteratedDeriv_g_lt_c : ∀ x ∈ Set.Iio c, iteratedDeriv (k + 1) g x = iteratedDeriv (k + 1) f c := by
        intros x hx
        have h_eq : ∀ y ∈ Set.Iio c, g y = p y := by
          grind
        have h_gp : iteratedDeriv (k + 1) g x = iteratedDeriv (k + 1) p x := by
          apply Filter.EventuallyEq.iteratedDeriv_eq
          filter_upwards [Iio_mem_nhds hx] with y hy using h_eq y hy
        rw [h_gp, iteratedDeriv_pow_sub_sum_top]
        rw [div_mul_cancel₀ _ (by positivity)]
      -- For `x > c`, `iteratedDeriv (k + 1) g x = iteratedDeriv (k + 1) f x`.
      have h_iteratedDeriv_g_gt_c : ∀ x ∈ Set.Ioi c, iteratedDeriv (k + 1) g x = iteratedDeriv (k + 1) f x := by
        intro x hx
        have h_eq : ∀ y ∈ Set.Ioi c, g y = f y := by
          grind
        rw [Filter.EventuallyEq.iteratedDeriv_eq]
        filter_upwards [Ioi_mem_nhds hx] with y hy using h_eq y hy
      -- For `x = c`, `iteratedDeriv (k + 1) g x = iteratedDeriv (k + 1) f c`.
      have h_iteratedDeriv_g_eq_c : iteratedDeriv (k + 1) g c = iteratedDeriv (k + 1) f c := by
        have h_tendsto_g :
            Filter.Tendsto (fun x ↦ iteratedDeriv (k + 1) g x)
              (nhdsWithin c (Set.Iio c)) (nhds (iteratedDeriv (k + 1) g c)) := by
          have h_cont : Continuous (iteratedDeriv (k + 1) g) := by
            apply_rules [ContDiff.continuous_iteratedDeriv]
            norm_cast
          exact h_cont.continuousWithinAt
        exact tendsto_nhds_unique h_tendsto_g
          (Filter.Tendsto.congr'
            (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx ↦ by rw [h_iteratedDeriv_g_lt_c x hx])
            tendsto_const_nhds)
      left
      intro x hx
      by_cases hx' : x < c <;> by_cases hx'' : x = c <;> simp_all
      · convert hsign_pos (T₀ + 1) (by linarith) using 1
        rw [iteratedDerivWithin_eq_iteratedDeriv]
        · exact uniqueDiffOn_Ici _
        · exact hf.contDiffAt (Ici_mem_nhds (by linarith))
        · norm_num
      · convert hsign_pos (T₀ + 1) (by linarith) using 1
        rw [iteratedDerivWithin_eq_iteratedDeriv]
        · exact uniqueDiffOn_Ici _
        · exact hf.contDiffAt (Ici_mem_nhds (by linarith))
        · norm_num
      · rw [h_iteratedDeriv_g_gt_c x (lt_of_le_of_ne hx' (Ne.symm hx''))]
        convert hsign_pos x (by linarith) using 1
        rw [iteratedDerivWithin_eq_iteratedDeriv]
        · exact uniqueDiffOn_Ici _
        · exact hf.contDiffAt (Ici_mem_nhds <| by linarith)
        · exact Set.mem_Ici.mpr (by linarith)
    · -- For `x > c`, `iteratedDerivWithin k g (Set.Ici 1) x = iteratedDeriv k g x = iteratedDeriv k f x = iteratedDerivWithin k f (Set.Ici T₀) x`.
      have h_eq : ∀ x > c, iteratedDerivWithin k g (Set.Ici 1) x = iteratedDerivWithin k f (Set.Ici T₀) x := by
        intros x hx_gt_c
        have h_deriv_eq : ∀ j ≤ k, iteratedDeriv j g x = iteratedDeriv j f x := by
          intros j hj_le_k
          have h_gf : ∀ y ∈ Set.Ioi c, g y = f y := by
            grind
          rw [Filter.EventuallyEq.iteratedDeriv_eq]
          filter_upwards [lt_mem_nhds hx_gt_c] with y hy using h_gf y hy
        convert h_deriv_eq k le_rfl using 1
        · rw [iteratedDerivWithin_eq_iteratedDeriv]
          · exact uniqueDiffOn_Ici _
          · exact hg_contDiff.contDiffAt.of_le (by norm_num)
          · exact Set.mem_Ici.mpr (by linarith)
        · rw [iteratedDerivWithin_eq_iteratedDeriv]
          · exact uniqueDiffOn_Ici _
          · exact (hf.contDiffAt (Ici_mem_nhds <| by linarith)).of_le (by norm_num)
          · exact Set.mem_Ici.mpr (by linarith)
      apply htend.congr'
      filter_upwards [Filter.eventually_gt_atTop c] with x hx using h_eq x hx ▸ rfl
    · grind
  · obtain ⟨c, hc⟩ : ∃ c > T₀, iteratedDerivWithin (k + 1) f (Set.Ici T₀) c < 0 := by
      refine ⟨T₀ + 1, by linarith, hsign_neg _ ?_⟩
      norm_num
    obtain ⟨g, hg⟩ :
        ∃ g : ℝ → ℝ, ContDiff ℝ (k + 1) g ∧
          (∀ x, c ≤ x → g x = f x) ∧
          (∀ x, x < c → g x = ∑ j ∈ Finset.range (k + 2), (iteratedDeriv j f c / (Nat.factorial j)) * (x - c) ^ j) := by
      obtain ⟨g, hg⟩ :
          ∃ g : ℝ → ℝ, ContDiff ℝ (k + 1) g ∧
            (∀ x, c ≤ x →
              g x = f x - ∑ j ∈ Finset.range (k + 2), (iteratedDeriv j f c / (Nat.factorial j)) * (x - c) ^ j) ∧
            (∀ x, x < c → g x = 0) := by
        have := @contDiff_extend_by_zero (k + 1) c
          (fun x ↦ f x - ∑ j ∈ Finset.range (k + 2),
            iteratedDeriv j f c / (j.factorial : ℝ) * (x - c) ^ j) ?_ ?_
        · exact ⟨_, this, fun x hx ↦ if_pos hx, fun x hx ↦ if_neg hx.not_ge⟩
        · apply ContDiffOn.sub
          · exact hf.mono (Set.Ici_subset_Ici.mpr hc.1.le)
          · exact ContDiffOn.sum fun _ _ ↦
              ContDiffOn.mul (contDiffOn_const) (ContDiffOn.pow (contDiffOn_id.sub contDiffOn_const) _)
        · intro j hj
          have h_dw :
              iteratedDerivWithin j
                  (fun x ↦ f x - ∑ j ∈ Finset.range (k + 2),
                    iteratedDeriv j f c / (j.factorial : ℝ) * (x - c) ^ j) (Set.Ici c) c =
                iteratedDeriv j
                  (fun x ↦ f x - ∑ j ∈ Finset.range (k + 2),
                    iteratedDeriv j f c / (j.factorial : ℝ) * (x - c) ^ j) c := by
            rw [iteratedDerivWithin_eq_iteratedDeriv]
            · exact uniqueDiffOn_Ici _
            · apply ContDiffAt.sub
              · exact (hf.contDiffAt (Ici_mem_nhds hc.1)).of_le (mod_cast by linarith)
              · fun_prop
            · norm_num
          have h_dsub :
              iteratedDeriv j
                  (fun x ↦ f x - ∑ j ∈ Finset.range (k + 2),
                    iteratedDeriv j f c / (j.factorial : ℝ) * (x - c) ^ j) c =
                iteratedDeriv j f c - iteratedDeriv j
                  (fun x ↦ ∑ j ∈ Finset.range (k + 2),
                    iteratedDeriv j f c / (j.factorial : ℝ) * (x - c) ^ j) c := by
            apply iteratedDeriv_sub
            · exact (hf.contDiffAt (Ici_mem_nhds hc.1)).of_le (mod_cast by linarith)
            · fun_prop
          have h_dpoly :
              iteratedDeriv j
                  (fun x ↦ ∑ j ∈ Finset.range (k + 2),
                    iteratedDeriv j f c / (j.factorial : ℝ) * (x - c) ^ j) c = iteratedDeriv j f c := by
            convert iteratedDeriv_pow_sub_sum_at (k + 1) c
              (fun j ↦ iteratedDeriv j f c / (j.factorial : ℝ)) j hj using 1
            rw [div_mul_cancel₀ _ (by positivity)]
          linarith
      use fun x ↦ g x + ∑ j ∈ Finset.range (k + 2), (iteratedDeriv j f c / (Nat.factorial j)) * (x - c) ^ j
      refine ⟨?_, ?_, ?_⟩
      · exact hg.1.add <| ContDiff.sum fun _ _ ↦
          ContDiff.mul (contDiff_const) <| ContDiff.pow (contDiff_id.sub contDiff_const) _
      · exact fun x hx ↦ by simp [hg.2.1 x hx]
      · exact fun x hx ↦ by simp [hg.2.2 x hx]
    refine ⟨c, g, by linarith, hg.1.contDiffOn, ?_, ?_, ?_⟩ <;> norm_num [hg.2]
    · have hdn_split :
          ∀ x, iteratedDeriv (k + 1) g x =
            if x < c then iteratedDeriv (k + 1) g c else iteratedDerivWithin (k + 1) f (Set.Ici T₀) x := by
        intro x
        split_ifs <;> simp_all
        · have hdn_lt :
              ∀ x, x < c → iteratedDeriv (k + 1) g x =
                iteratedDeriv (k + 1) (fun x ↦ ∑ j ∈ Finset.range (k + 2),
                  (iteratedDeriv j f c / (Nat.factorial j)) * (x - c) ^ j) x := by
            intro x hx
            rw [Filter.EventuallyEq.iteratedDeriv_eq]
            filter_upwards [Iio_mem_nhds hx] with y hy
            aesop
          have hdn_poly_const :
              ∀ x, iteratedDeriv (k + 1) (fun x ↦ ∑ j ∈ Finset.range (k + 2),
                    (iteratedDeriv j f c / (Nat.factorial j)) * (x - c) ^ j) x =
                iteratedDeriv (k + 1) (fun x ↦ ∑ j ∈ Finset.range (k + 2),
                    (iteratedDeriv j f c / (Nat.factorial j)) * (x - c) ^ j) c := by
            intro x
            rw [iteratedDeriv_pow_sub_sum_top, iteratedDeriv_pow_sub_sum_top]
          have hdn_gc :
              iteratedDeriv (k + 1) g c =
                iteratedDeriv (k + 1) (fun x ↦ ∑ j ∈ Finset.range (k + 2),
                    (iteratedDeriv j f c / (Nat.factorial j)) * (x - c) ^ j) c := by
            have hdn_tendsto :
                Filter.Tendsto (fun x ↦ iteratedDeriv (k + 1) g x)
                  (nhdsWithin c (Set.Iio c)) (nhds (iteratedDeriv (k + 1) g c)) := by
              have hdn_cont : ContinuousAt (iteratedDeriv (k + 1) g) c := by
                have hdn_cd : ContDiff ℝ (k + 1 - (k + 1)) (iteratedDeriv (k + 1) g) := by
                  convert hg.1.continuous_iteratedDeriv (k + 1) using 1
                  norm_num [contDiff_iff_continuous_differentiable]
                exact hdn_cd.continuous.continuousAt
              exact hdn_cont.mono_left inf_le_left
            exact tendsto_nhds_unique hdn_tendsto
              (Filter.Tendsto.congr'
                (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx ↦ by aesop) tendsto_const_nhds)
          grind +ring
        · rw [iteratedDerivWithin_eq_iteratedDeriv]
          · have hdn_gt : ∀ x, c < x → iteratedDeriv (k + 1) g x = iteratedDeriv (k + 1) f x := by
              intro x hx
              apply Filter.EventuallyEq.iteratedDeriv_eq
              filter_upwards [lt_mem_nhds hx] with y hy using hg.2.1 y hy.le
            cases lt_or_eq_of_le ‹_› <;> simp_all
            have hdn_tg :
                Filter.Tendsto (fun y ↦ iteratedDeriv (k + 1) g y)
                  (nhdsWithin x (Set.Ioi x)) (nhds (iteratedDeriv (k + 1) g x)) := by
              have hdn_cg : ContinuousAt (iteratedDeriv (k + 1) g) x := by
                have hdn_cdg : ContDiff ℝ (↑k + 1) g := hg.1
                fun_prop
              exact hdn_cg.mono_left inf_le_left
            have hdn_tf :
                Filter.Tendsto (fun y ↦ iteratedDeriv (k + 1) f y)
                  (nhdsWithin x (Set.Ioi x)) (nhds (iteratedDeriv (k + 1) f x)) := by
              have hdn_cdf : ContDiffOn ℝ (↑(k + 1 - (k + 1))) (iteratedDeriv (k + 1) f) (Set.Ioi T₀) := by
                have hdn_cf : ContDiffOn ℝ (↑(k + 1)) f (Set.Ioi T₀) :=
                  hf.mono Set.Ioi_subset_Ici_self
                have hdn_cdm : ∀ m ≤ k + 1, ContDiffOn ℝ (↑(k + 1 - m)) (iteratedDeriv m f) (Set.Ioi T₀) := by
                  intro m hm
                  induction' m with m ih <;> simp_all [iteratedDeriv_succ]
                  have := ih (by linarith)
                  convert this.deriv_of_isOpen isOpen_Ioi _ using 1
                  norm_cast
                  omega
                exact hdn_cdm _ le_rfl
              exact hdn_cdf.continuousOn.continuousAt (Ioi_mem_nhds hc.1)
                |> fun h ↦ h.mono_left inf_le_left
            exact tendsto_nhds_unique ‹_›
              (hdn_tf.congr' <| Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun y hy ↦ by aesop)
          · exact uniqueDiffOn_Ici _
          · exact (hf.contDiffAt (Ici_mem_nhds (by linarith))).of_le (by norm_num)
          · exact le_trans hc.1.le ‹_›
      have hdn_within : ∀ x, 1 < x → iteratedDerivWithin (k + 1) g (Set.Ici 1) x = iteratedDeriv (k + 1) g x := by
        intro x hx
        rw [iteratedDerivWithin_eq_iteratedDeriv]
        · exact uniqueDiffOn_Ici _
        · exact hg.1.contDiffAt.of_le (by norm_num)
        · exact hx.le
      grind
    · have h_tendsto : Filter.Tendsto (fun x ↦ iteratedDerivWithin k g (Set.Ici 1) x) Filter.atTop (nhds 0) := by
        have key : ∀ j, ∀ y ∈ Set.Ioi c,
            iteratedDerivWithin j g (Set.Ici 1) y = iteratedDerivWithin j f (Set.Ici T₀) y := by
          intro j
          induction' j with j ih <;> intro y hy
          · simp only [iteratedDerivWithin_zero]
            exact hg.2.1 y hy.out.le
          · simp only [iteratedDerivWithin_succ]
            rw [Filter.EventuallyEq.derivWithin_eq]
            any_goals exact fun x ↦ iteratedDerivWithin j f (Set.Ici T₀) x
            · rw [derivWithin_of_mem_nhds (Ici_mem_nhds <| by linarith [hy.out]),
                derivWithin_of_mem_nhds (Ici_mem_nhds <| by linarith [hy.out])]
            · filter_upwards [self_mem_nhdsWithin,
                mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hy)]
                with z hz₁ hz₂ using ih z hz₂
            · exact ih y hy
        have h_eq : ∀ x > c, iteratedDerivWithin k g (Set.Ici 1) x = iteratedDerivWithin k f (Set.Ici T₀) x :=
          fun x hx ↦ key k x hx
        exact Filter.Tendsto.congr'
          (Filter.eventuallyEq_of_mem (Filter.Ioi_mem_atTop c) fun x hx ↦ by rw [h_eq x hx]) htend
      exact h_tendsto
    · exact hg.2.1

/-
**Analytic package from a leading derivative asymptotic.**

This is the clean, self-contained analytic step behind `real_branches_on_tail`.  Suppose a
function `f` has, for every derivative order `m ≥ m₀`, the leading power asymptotic
`f⁽ᵐ⁾(x) ∼ c · (descPochhammer ℝ m).eval s · x^{s−m}`  (as `x → +∞`),
with a nonzero constant `c` and an exponent `s` that is **not** a natural number (so the
falling factorial `∏_{i<m}(s−i)` never vanishes).  This is exactly the behaviour of a real
Puiseux branch of an algebraic function at infinity whose leading non-polynomial exponent
is `s`.

Then for every large `k` (namely `k ≥ k₀` for a suitable `k₀ ≥ 2`) the `k`-th derivative
tends to `0` (because `s − k < 0`) and the `(k+1)`-th derivative is *sign-definite* on a
tail `(T₁, ∞)` (because its leading coefficient `c · ∏_{i≤k}(s−i)` is nonzero and
`x^{s−k−1} > 0`).  This is precisely the shape consumed by `real_branches_on_tail`.
-/
lemma asymptotic_deriv_analytic_package
    (f : ℝ → ℝ) (s c : ℝ) (hc : c ≠ 0) (hs : ∀ i : ℕ, s ≠ (i : ℝ)) (m₀ : ℕ)
    (hasymp : ∀ m : ℕ, m₀ ≤ m →
        Filter.Tendsto (fun x ↦ iteratedDeriv m f x / x ^ (s - (m : ℝ)))
          Filter.atTop (nhds (c * Polynomial.eval s (descPochhammer ℝ m)))) :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k, k₀ ≤ k → ∃ T₁ : ℝ,
      ((∀ x, T₁ < x → 0 < iteratedDeriv (k + 1) f x) ∨
        (∀ x, T₁ < x → iteratedDeriv (k + 1) f x < 0)) ∧
      Filter.Tendsto (iteratedDeriv k f) Filter.atTop (nhds 0) := by
  refine ⟨m₀ + ⌈s⌉₊ + 2, ?_, fun k hk ↦ ?_⟩
  · linarith
  · -- For the `(k+1)`-th derivative, since `c · ∏_{i≤k}(s-i) ≠ 0`, the sign of `c · ∏_{i≤k}(s-i) · x^(s-(k+1))` is constant for large `x`.
    have h_sign : ∃ T₁ : ℝ, (∀ x > T₁, 0 < iteratedDeriv (k + 1) f x) ∨ (∀ x > T₁, iteratedDeriv (k + 1) f x < 0) := by
      have h_sign :
          Filter.Tendsto (fun x ↦ iteratedDeriv (k + 1) f x / x ^ (s - (k + 1)))
            Filter.atTop (nhds (c * (descPochhammer ℝ (k + 1)).eval s)) := by
        exact_mod_cast hasymp _ (by linarith)
      have h_sign_ne_zero : c * (descPochhammer ℝ (k + 1)).eval s ≠ 0 := by
        simp_all [descPochhammer_eval_eq_prod_range]
        exact Finset.prod_ne_zero_iff.mpr fun i hi ↦ sub_ne_zero_of_ne <| hs i
      cases lt_or_gt_of_ne h_sign_ne_zero <;> simp_all [div_eq_mul_inv]
      · have := h_sign.eventually (gt_mem_nhds ‹_›)
        rw [Filter.eventually_atTop] at this
        rcases this with ⟨T₁, hT₁⟩
        refine ⟨Max.max T₁ 1, Or.inr fun x hx ↦ ?_⟩
        have := hT₁ x (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx))
        exact lt_of_not_ge fun h ↦ this.not_ge <| mul_nonneg h <|
          inv_nonneg.mpr <| Real.rpow_nonneg (by linarith [le_max_right T₁ 1]) _
      · have := h_sign.eventually (lt_mem_nhds ‹_›)
        rw [Filter.eventually_atTop] at this
        rcases this with ⟨T₁, hT₁⟩
        refine ⟨Max.max T₁ 1, Or.inl fun x hx ↦ ?_⟩
        have := hT₁ x (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx))
        have := inv_pos.mpr (Real.rpow_pos_of_pos (by linarith [le_max_right T₁ 1] : 0 < x) (s - (k + 1)))
        nlinarith
    have h_tendsto :
        Filter.Tendsto (fun x ↦ (iteratedDeriv k f x) / x ^ (s - k) * x ^ (s - k))
          Filter.atTop (nhds 0) := by
      have hks : 0 < (k : ℝ) - s := by
        have hkm : (k : ℝ) ≥ m₀ + ⌈s⌉₊ + 2 := by norm_cast
        linarith [Nat.le_ceil s]
      convert Filter.Tendsto.mul (hasymp k (by linarith))
        (tendsto_rpow_neg_atTop hks) using 2
      · ring_nf
      · ring
    refine ⟨h_sign.choose, h_sign.choose_spec, h_tendsto.congr' ?_⟩
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    rw [div_mul_cancel₀ _ <| ne_of_gt <| Real.rpow_pos_of_pos hx _]

/-- `dummyBranch = x ↦ √x` is `C^∞` on any positive tail `[T₀,∞)` (`T₀ ≥ 1`). -/
lemma dummyBranch_contDiffOn_top (T₀ : ℤ) (hT₀ : 1 ≤ T₀) :
    ContDiffOn ℝ ⊤ dummyBranch (Set.Ici (T₀ : ℝ)) := by
  unfold dummyBranch
  apply ContDiffOn.rpow contDiffOn_id contDiffOn_const
  intro x hx
  have : (1 : ℝ) ≤ (T₀ : ℝ) := by exact_mod_cast hT₀
  simp only [Set.mem_Ici] at hx
  simp only [id]
  linarith

/-- The pure-power model branch `dummyBranch = x ↦ √x` has the exact leading derivative
asymptotic with `c = 1` and `s = 1/2` (indeed the ratio is *constant* on the positive
tail).  This lets `dummyBranch` be used to pad the branch family in
`branch_leading_asymptotics`. -/
lemma dummyBranch_deriv_asymptotic (m : ℕ) :
    Filter.Tendsto (fun x ↦ iteratedDeriv m dummyBranch x / x ^ ((1 / 2 : ℝ) - (m : ℝ)))
      Filter.atTop (nhds (1 * Polynomial.eval (1 / 2 : ℝ) (descPochhammer ℝ m))) := by
  unfold dummyBranch
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, one_mul,
    mul_div_assoc, div_self (by positivity), mul_one]

/-- Real specialization `T ↦ x` of a `ℤ[T]`-coefficient polynomial, as a ring hom
`ℤ[T] →+* ℝ`.  Used to talk about real roots `P(x, y) = 0` of the family. -/
noncomputable def evalIntPolyReal (x : ℝ) : Polynomial ℤ →+* ℝ :=
  (Polynomial.evalRingHom x).comp (Polynomial.mapRingHom (Int.castRingHom ℝ))

/-- An integer root of the integer specialization `P(t, ·)` is a real root of the real
specialization `P(x, ·)` at `x = t`.  This bridges the integer covering statement to the
real branches. -/
lemma isRoot_evalIntPolyReal_of_isRoot_evalRingHom
    (P : Polynomial (Polynomial ℤ)) (t : ℤ) (y : ℤ)
    (h : (P.map (Polynomial.evalRingHom t)).IsRoot y) :
    (P.map (evalIntPolyReal (t : ℝ))).IsRoot (y : ℝ) := by
  have hev : (evalIntPolyReal (t : ℝ)) = (Int.castRingHom ℝ).comp (Polynomial.evalRingHom t) := by
    ext c <;> simp [evalIntPolyReal]
  unfold Polynomial.IsRoot at h ⊢
  rw [hev, ← Polynomial.map_map, Polynomial.eval_map,
    show ((y : ℤ) : ℝ) = (Int.castRingHom ℝ) y from rfl, eval₂_at_apply, h, map_zero]

/-
**Rationality from integer values (Lagrange interpolation).**

A real polynomial `q` that takes an integer value at infinitely many integers has rational
coefficients: `q = q'.map (ℚ → ℝ)` for some `q' ∈ ℚ[X]`.  Indeed `q` is the Lagrange
interpolant through any `q.natDegree + 1` of those integer nodes with integer (hence
rational) data, so it agrees with the rational interpolant mapped into `ℝ`.
-/
lemma realPoly_ratl_of_infinite_int_values (q : Polynomial ℝ)
    (hinf : {t : ℤ | ∃ z : ℤ, q.eval (t : ℝ) = (z : ℝ)}.Infinite) :
    ∃ q' : Polynomial ℚ, q'.map (algebraMap ℚ ℝ) = q := by
  -- Let `d = q.natDegree`.
  set d := q.natDegree with hd
  -- Choose `d + 1` distinct integers `t₀, t₁, …, t_d` from the infinite set.
  obtain ⟨t, ht_distinct, ht_mem⟩ :
      ∃ t : Fin (d + 1) → ℤ, Function.Injective t ∧ ∀ i, ∃ z : ℤ, q.eval (t i : ℝ) = z := by
    have := hinf.exists_subset_card_eq (d + 1)
    obtain ⟨t, ht₁, ht₂⟩ := this
    refine ⟨fun i ↦ t.orderEmbOfFin (by aesop) i, ?_, fun i ↦ ht₁ <| by aesop⟩
    aesop_cat
  choose z hz using ht_mem
  -- By Lagrange interpolation, there is a unique polynomial `q'` of degree at most `d` with `q'(t i) = z i` for all `i`.
  obtain ⟨q', hq'⟩ : ∃ q' : Polynomial ℚ, q'.degree ≤ d ∧ ∀ i, q'.eval (t i : ℚ) = z i := by
    use Finset.sum Finset.univ fun i ↦
      Polynomial.C (z i : ℚ) * Finset.prod (Finset.erase Finset.univ i) fun j ↦
        Polynomial.C (1 / (t i - t j : ℚ)) * (Polynomial.X - Polynomial.C (t j : ℚ))
    refine ⟨le_trans (Polynomial.degree_sum_le _ _) ?_, ?_⟩
    · simp [Polynomial.degree_prod]
      exact fun i ↦ le_trans
        (add_le_add (Polynomial.degree_C_le)
          (Finset.sum_le_sum fun j hj ↦
            add_le_add (Polynomial.degree_C_le) (Polynomial.degree_X_sub_C_le _)))
        (by norm_num)
    · intro i
      rw [Polynomial.eval_finset_sum, Finset.sum_eq_single i] <;>
        simp_all [Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, ht_distinct.eq_iff]
      · rw [Finset.prod_eq_one fun j hj ↦ by
          rw [inv_mul_cancel₀]
          exact sub_ne_zero_of_ne <| mod_cast ht_distinct.ne <| by aesop]
        norm_num
      · exact fun j hj ↦ Or.inr ⟨i, Ne.symm hj, Or.inr rfl⟩
  use q'
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq
    (Finset.image (fun i : Fin (d + 1) ↦ (t i : ℝ)) Finset.univ) ?_ ?_
  · apply lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
    have hinj : Function.Injective (fun i : Fin (d + 1) ↦ (t i : ℝ)) :=
      fun i j hij ↦ by simpa [ht_distinct.eq_iff] using hij
    simp_all [Finset.card_image_of_injective _ hinj]
    exact ⟨lt_of_le_of_lt hq'.1 (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _)),
      lt_of_le_of_lt (Polynomial.degree_le_natDegree) (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _))⟩
  · simp_all [Polynomial.eval_map]

/-
**A rational eventual root of `P` gives a root in `ℚ(T)`.** -/
lemma ratl_eventual_root_gives_ratFunc_root
    (P : Polynomial (Polynomial ℤ)) (T₀ : ℝ) (q' : Polynomial ℚ)
    (hroot : ∀ x : ℝ, T₀ ≤ x →
      (P.map (evalIntPolyReal x)).eval ((q'.map (algebraMap ℚ ℝ)).eval x) = 0) :
    ∃ a : FractionRing (Polynomial ℚ), (P.map toRatFunc).IsRoot a := by
  -- Let Ψ := eval q' PQ. By hypothesis, Ψ.map φ = 0.
  set Ψ : Polynomial ℚ := Polynomial.eval q' (P.map (Polynomial.mapRingHom (Int.castRingHom ℚ)))
  have hΨ : Polynomial.map (algebraMap ℚ ℝ) Ψ = 0 := by
    -- The pushforward `Ψ.map (algebraMap ℚ ℝ)` is a polynomial in `ℝ[X]`.
    have hΨ_poly : ∀ x : ℝ, T₀ ≤ x → (Ψ.map (algebraMap ℚ ℝ)).eval x = 0 := by
      intro x hx
      have h_eval :
          Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ) Ψ) =
            Polynomial.eval (Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ) q'))
              (Polynomial.map (evalIntPolyReal x) P) := by
        simp [Ψ]
        simp [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
        simp [evalIntPolyReal, Polynomial.aeval_def, Polynomial.eval_map]
        simp [Polynomial.eval₂_map]
        congr! 2
      rw [h_eval]
      exact hroot x hx
    have hΨ_inf_roots : Set.Infinite {x : ℝ | (Ψ.map (algebraMap ℚ ℝ)).eval x = 0} :=
      Set.Infinite.mono hΨ_poly (Set.Ici_infinite T₀)
    exact Classical.not_not.1 fun h ↦
      hΨ_inf_roots <| Set.Finite.subset
        (Polynomial.map (algebraMap ℚ ℝ) Ψ |> Polynomial.roots |> Multiset.toFinset |> Finset.finite_toSet)
        fun x hx ↦ by aesop
  simp_all [Polynomial.ext_iff]
  -- Since Ψ is the zero polynomial, we have that P(q') = 0 in ℚ(T).
  use (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))) q'
  convert congr_arg (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
    (show Ψ = 0 from Polynomial.ext hΨ) using 1
  · unfold Ψ toRatFunc
    simp [Polynomial.eval_map]
    simp [Polynomial.eval₂_eq_sum_range]
  · norm_num

/-- The real specialization `P.map (evalIntPolyReal x)` is monic (for `P` monic), since
`evalIntPolyReal x` is a ring hom sending the leading coefficient `1` to `1`. -/
lemma evalIntPolyReal_map_monic (P : Polynomial (Polynomial ℤ)) (hP : P.Monic) (x : ℝ) :
    (P.map (evalIntPolyReal x)).Monic :=
  hP.map _

/-- The real specialization preserves the `Y`-degree (for `P` monic). -/
lemma evalIntPolyReal_map_natDegree (P : Polynomial (Polynomial ℤ)) (hP : P.Monic) (x : ℝ) :
    (P.map (evalIntPolyReal x)).natDegree = P.natDegree :=
  hP.natDegree_map _

/-
The two-variable evaluation map `(x, y) ↦ P.map (evalIntPolyReal x) |>.eval y` is a
polynomial in `(x, y)` (its coefficients are polynomial functions of `x` and it is
polynomial in `y`), hence `C^∞` on all of `ℝ²`.  This is the smooth ambient function whose
zero set carries the real root branches, and is the natural input to the implicit function
theorem.
-/
lemma evalIntPolyReal_eval_contDiff (P : Polynomial (Polynomial ℤ)) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ ↦ (P.map (evalIntPolyReal p.1)).eval p.2) := by
  unfold evalIntPolyReal
  simp [Polynomial.eval_map]
  rw [Polynomial.as_sum_range_C_mul_X_pow P]
  simp [Polynomial.eval₂_finset_sum]
  refine ContDiff.sum fun i hi ↦ ContDiff.mul ?_ ?_
  · simp [Polynomial.eval_eq_sum_range]
    exact ContDiff.sum fun _ _ ↦ ContDiff.mul (contDiff_const) (contDiff_fst.pow _)
  · exact contDiff_snd.pow i

/-
**Local implicit-function branch at a simple real root.**  If `y₀` is a *simple* real
root of the specialization `P.map (evalIntPolyReal x₀)` (root with nonzero derivative),
then there is a `C^∞` real function `φ` near `x₀` with `φ x₀ = y₀` that is a genuine real
root of the family in a neighborhood of `x₀`: `P.map (evalIntPolyReal x) |>.eval (φ x) = 0`.

This is the pure implicit-function-theorem step of the branch construction, applied to the
smooth ambient map `evalIntPolyReal_eval_contDiff`.  It is the local, reusable core toward
`real_root_branches_cover`.
-/
lemma real_branch_at_simple_root (P : Polynomial (Polynomial ℤ)) (x₀ y₀ : ℝ)
    (hroot : (P.map (evalIntPolyReal x₀)).eval y₀ = 0)
    (hsimple : (P.map (evalIntPolyReal x₀)).derivative.eval y₀ ≠ 0) :
    ∃ φ : ℝ → ℝ, φ x₀ = y₀ ∧ ContDiffAt ℝ ⊤ φ x₀ ∧
      ∀ᶠ x : ℝ in nhds x₀, (P.map (evalIntPolyReal x)).eval (φ x) = 0 := by
  -- Define the function F : ℝ × ℝ → ℝ by F(x, y) = P(x, y).
  set F : ℝ × ℝ → ℝ := fun p ↦ (P.map (evalIntPolyReal p.1)).eval p.2
  -- Apply the implicit function theorem to F at the point (x₀, y₀).
  obtain ⟨φ, hφ⟩ :
      ∃ φ : ℝ → ℝ, HasFDerivAt F (fderiv ℝ F (x₀, y₀)) (x₀, y₀) ∧ ContDiffAt ℝ ⊤ φ x₀ ∧
        φ x₀ = y₀ ∧ ∀ᶠ x in nhds x₀, F (x, φ x) = F (x₀, y₀) := by
    have h_implicit : IsContDiffImplicitAt ⊤ F (fderiv ℝ F (x₀, y₀)) (x₀, y₀) := by
      constructor
      · exact DifferentiableAt.hasFDerivAt
          ((evalIntPolyReal_eval_contDiff P).differentiable (by norm_num) _)
      · exact evalIntPolyReal_eval_contDiff P |> ContDiff.contDiffAt
      · have hL :
            ∀ x, (fderiv ℝ F (x₀, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) x =
              (Polynomial.derivative (P.map (evalIntPolyReal x₀))).eval y₀ * x := by
          intro x
          have hL_mid :
              (fderiv ℝ F (x₀, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) x =
                deriv (fun y ↦ (P.map (evalIntPolyReal x₀)).eval y) y₀ * x := by
            have hL_one :
                deriv (fun y ↦ (P.map (evalIntPolyReal x₀)).eval y) y₀ =
                  (fderiv ℝ F (x₀, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) 1 := by
              convert HasDerivAt.deriv _ using 1
              have hdiff := (evalIntPolyReal_eval_contDiff P).differentiable (by norm_num) (x₀, y₀)
              have hFderiv : HasFDerivAt F (fderiv ℝ F (x₀, y₀)) (x₀, y₀) :=
                DifferentiableAt.hasFDerivAt (by convert hdiff using 1)
              convert HasFDerivAt.hasDerivAt
                (HasFDerivAt.comp y₀ hFderiv
                  (HasFDerivAt.prodMk (hasFDerivAt_const _ _) (hasFDerivAt_id _))) using 1
            rw [hL_one, mul_comm]
            convert (ContinuousLinearMap.map_smul
              ((fderiv ℝ F (x₀, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) x 1) using 1
            norm_num
          convert hL_mid using 1
          norm_num [Polynomial.derivative_eval]
        constructor
        · exact fun x y hxy ↦ mul_left_cancel₀ hsimple <| by aesop
        · exact fun x ↦
            ⟨x / (Polynomial.eval y₀ (Polynomial.derivative (Polynomial.map (evalIntPolyReal x₀) P))),
              by rw [hL, mul_div_cancel₀ _ hsimple]⟩
      · decide +revert
    refine ⟨h_implicit.implicitFunction, ?_, ?_, ?_, ?_⟩
    · exact h_implicit.hasFDerivAt
    · exact h_implicit.contDiffAt_implicitFunction
    · convert h_implicit.eventually_implicitFunction_apply_eq.self_of_nhds using 1
      aesop
    · exact h_implicit.apply_implicitFunction
  grind

/-- The `Y`-derivative of the real specialization is the specialization of the
`Y`-derivative: `(P.map (evalIntPolyReal x)).derivative = P.derivative.map (evalIntPolyReal x)`.
This lets the *simple-root* condition on the specialization `Q_x = P.map (evalIntPolyReal x)`
be read off from `P`'s formal `Y`-derivative. -/
lemma evalIntPolyReal_map_derivative (P : Polynomial (Polynomial ℤ)) (x : ℝ) :
    (P.map (evalIntPolyReal x)).derivative = P.derivative.map (evalIntPolyReal x) := by
  rw [Polynomial.derivative_map]

/-- A separable real polynomial has only *simple* roots: the derivative is nonzero at every
root.  This is exactly the hypothesis `real_branch_at_simple_root` needs, so on a tail where
the specialization `Q_x` is separable every real root extends to a smooth branch. -/
lemma eval_derivative_ne_zero_of_separable {p : Polynomial ℝ} (hsep : p.Separable) {y : ℝ}
    (hy : p.IsRoot y) : p.derivative.eval y ≠ 0 := by
  have h := hsep.aeval_derivative_ne_zero (x := y)
    (by simpa [aeval_def, eval_map, IsRoot] using hy)
  simpa [aeval_def, eval_map] using h

/-- **Local branch at a root of a separable specialization.**  If the specialization
`Q_{x₀} = P.map (evalIntPolyReal x₀)` is *separable* and `y₀` is a real root of it, then
`y₀` extends to a local `C^∞` genuine-root branch `φ` of the family near `x₀`.  This packages
the local implicit-function step (`real_branch_at_simple_root`) with the separability ⇒
simple-root bridge (`eval_derivative_ne_zero_of_separable`), which is the natural local input
for the global branch construction on a separable tail. -/
lemma real_branch_at_root_of_separable (P : Polynomial (Polynomial ℤ)) (x₀ y₀ : ℝ)
    (hsep : (P.map (evalIntPolyReal x₀)).Separable)
    (hroot : (P.map (evalIntPolyReal x₀)).eval y₀ = 0) :
    ∃ φ : ℝ → ℝ, φ x₀ = y₀ ∧ ContDiffAt ℝ ⊤ φ x₀ ∧
      ∀ᶠ x : ℝ in nhds x₀, (P.map (evalIntPolyReal x)).eval (φ x) = 0 :=
  real_branch_at_simple_root P x₀ y₀ hroot
    (eval_derivative_ne_zero_of_separable hsep hroot)

/-- **Reduction to a smooth separable family with the same real roots (squarefree part).**

For `P` monic in `Y` of `Y`-degree `≥ 2`, there is a `C^∞` family `R x` of monic real
polynomials of some fixed degree `d ≥ 1` which, on a tail `[T₀, ∞)`, is *separable* and has
*exactly the same real roots* as the specialization `Q_x = P.map (evalIntPolyReal x)`.

This is the elementary algebraic reduction underlying the classical branch construction: `R`
is the *squarefree part* (radical) of `P` in `Y`, whose coefficients are rational functions
of `x` with finitely many poles; past the finitely many real zeros of its discriminant and
those poles it is a smooth separable family with the same (distinct) real roots as `Q_x`.
Passing to the squarefree part is exactly what makes the discriminant nonvanishing on a
tail, so that the analytic core `SmoothRootBranches.smooth_separable_family_root_branches`
applies. -/
lemma exists_smooth_separable_reduction
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree) :
    ∃ (d : ℕ) (R : ℝ → Polynomial ℝ) (T₀ : ℤ), 1 ≤ T₀ ∧ 1 ≤ d ∧
      (∀ x, (R x).Monic) ∧ (∀ x, (R x).natDegree = d) ∧
      ContDiff ℝ ⊤ (fun p : ℝ × ℝ ↦ (R p.1).eval p.2) ∧
      (∀ x : ℝ, (T₀ : ℝ) ≤ x → (R x).Separable) ∧
      (∀ x : ℝ, (T₀ : ℝ) ≤ x → ∀ y : ℝ,
        (R x).eval y = 0 ↔ (P.map (evalIntPolyReal x)).eval y = 0) := by
  -- Push `P` down to a real bivariate polynomial `Fbar ∈ ℝ[x][Y]` and apply the real
  -- squarefree reduction, using `P.map (evalIntPolyReal x) = Fbar.map (evalRingHom x)`.
  set Fbar : Polynomial (Polynomial ℝ) := P.map (Polynomial.mapRingHom (Int.castRingHom ℝ)) with hFbar
  have hFbar_monic : Fbar.Monic := hP_monic.map _
  have hFbar_deg : 2 ≤ Fbar.natDegree := by
    rw [hFbar, hP_monic.natDegree_map]
    exact hP_deg
  have hbridge : ∀ x : ℝ, P.map (evalIntPolyReal x) = Fbar.map (evalRingHom x) := by
    intro x
    rw [hFbar, Polynomial.map_map]
    rfl
  obtain ⟨d, R, T₀r, hT₀r, hd, hRmon, hRdeg, hRsmooth, hRsep, hRroots⟩ :=
    SmoothSeparableReduction.exists_smooth_separable_reduction_real Fbar hFbar_monic hFbar_deg
  refine ⟨d, R, ⌈T₀r⌉, ?_, hd, hRmon, hRdeg, hRsmooth, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ (⌈T₀r⌉ : ℝ) := le_trans hT₀r (Int.le_ceil T₀r)
    exact_mod_cast h1
  · intro x hx
    exact hRsep x (le_trans (Int.le_ceil T₀r) hx)
  · intro x hx y
    rw [hbridge x]
    exact hRroots x (le_trans (Int.le_ceil T₀r) hx) y

/-- **Construction of the smooth real root branches covering integer roots.**

For `P` monic in `Y` of `Y`-degree `≥ 2`, there are finitely many `C^∞` branch functions
`g j` on a tail `[T₀, ∞)`, each a genuine real root of `P` there, together covering every
integer root of `P(t, ·)` for integer `t ≥ T₀`. -/
lemma real_root_branches_cover
    (P : Polynomial (Polynomial ℤ))
    (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree) :
    ∃ (n : ℕ) (T₀ : ℤ) (g : Fin n → ℝ → ℝ),
      1 ≤ T₀ ∧
      (∀ j, ContDiffOn ℝ ⊤ (g j) (Set.Ici (T₀ : ℝ))) ∧
      (∀ j, ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g j x) = 0) ∧
      (∀ t : ℤ, T₀ ≤ t → ∀ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y →
          ∃ j, g j (t : ℝ) = (y : ℝ)) := by
  obtain ⟨d, R, T₀, hT₀, hd, hRmon, hRdeg, hRsmooth, hRsep, hRroots⟩ :=
    exists_smooth_separable_reduction P hP_monic hP_deg
  obtain ⟨n, g, hcd, hgroot, hcov, _hinj⟩ :=
    SmoothRootBranches.smooth_separable_family_root_branches R (T₀ : ℝ) d hd hRmon hRdeg
      hRsmooth hRsep
  refine ⟨n, T₀, g, hT₀, hcd, ?_, ?_⟩
  · intro j x hx
    exact (hRroots x hx (g j x)).mp (hgroot j x hx)
  · intro t ht y hy
    have hr : (P.map (evalIntPolyReal (t : ℝ))).eval (y : ℝ) = 0 :=
      isRoot_evalIntPolyReal_of_isRoot_evalRingHom P t y hy
    have hR0 : (R (t : ℝ)).eval (y : ℝ) = 0 :=
      (hRroots (t : ℝ) (by exact_mod_cast ht) (y : ℝ)).mpr hr
    exact hcov (t : ℝ) (by exact_mod_cast ht) (y : ℝ) hR0

/-
Elementary bound on the absolute value of a real polynomial evaluated at `x`, in terms
of the sum of the absolute values of its coefficients and `(1 + |x|)` raised to the degree.
This is the crude estimate underlying the uniform Cauchy root bound along an algebraic
branch.
-/
lemma real_poly_eval_abs_le (p : Polynomial ℝ) (x : ℝ) :
    |p.eval x| ≤ (∑ j ∈ Finset.range (p.natDegree + 1), |p.coeff j|) * (1 + |x|) ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  norm_num [abs_mul, Finset.sum_mul _ _ _]
  exact Finset.sum_le_sum fun i hi ↦
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg x]) _ |> le_trans <|
        pow_le_pow_right₀ (by linarith [abs_nonneg x]) <| Finset.mem_range_succ_iff.mp hi)
      (abs_nonneg _)

/-
**Polynomial growth of an algebraic branch.**  A real root `g x` of the monic
specialization `P(x, ·)` grows at most polynomially in `x`: there are constants `C ≥ 0` and
`N` (depending only on `P`) with `|g x| ≤ C · (1 + |x|) ^ N` for all `x ≥ T₀`.  This is the
uniform Cauchy root bound applied along the branch, and is the first step (bounding the
leading Puiseux exponent) toward `real_root_branch_classify`.
-/
lemma real_root_branch_poly_growth
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic) (hP_deg : 1 ≤ P.natDegree)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ x : ℝ, (T₀ : ℝ) ≤ x → |g x| ≤ C * (1 + |x|) ^ N := by
  -- Choose the constant and exponent uniformly.
  set d := P.natDegree
  set N := (Finset.range d).sup (fun i ↦ ((P.coeff i).map (Int.castRingHom ℝ)).natDegree) with hN_def
  set S := (Finset.range d).sup' ⟨_, Finset.mem_range.mpr hP_deg⟩
    (fun i ↦ ∑ j ∈ Finset.range (((P.coeff i).map (Int.castRingHom ℝ)).natDegree + 1),
      |((P.coeff i).map (Int.castRingHom ℝ)).coeff j|) with hS_def
  -- By real_poly_eval_abs_le, for each i, |c_i| ≤ S * (1+|x|)^N.
  have h_coeff_bound : ∀ x : ℝ, ∀ i < d, |((P.map (evalIntPolyReal x)).coeff i)| ≤ S * (1 + |x|) ^ N := by
    intros x i hi
    have h_coeff_bound_i :
        |((P.map (evalIntPolyReal x)).coeff i)| ≤
          (∑ j ∈ Finset.range (((P.coeff i).map (Int.castRingHom ℝ)).natDegree + 1),
            |((P.coeff i).map (Int.castRingHom ℝ)).coeff j|) *
            (1 + |x|) ^ (((P.coeff i).map (Int.castRingHom ℝ)).natDegree) := by
      convert real_poly_eval_abs_le (Polynomial.map (Int.castRingHom ℝ) (P.coeff i)) x using 1
      unfold evalIntPolyReal
      aesop
    refine le_trans h_coeff_bound_i ?_
    gcongr
    · exact le_trans (by positivity)
        (Finset.le_sup'
          (fun i ↦ ∑ j ∈ Finset.range ((map (Int.castRingHom ℝ) (P.coeff i)).natDegree + 1),
            |(map (Int.castRingHom ℝ) (P.coeff i)).coeff j|) (Finset.mem_range.mpr hi))
    · exact Finset.le_sup'
        (fun i ↦ ∑ j ∈ Finset.range ((map (Int.castRingHom ℝ) (P.coeff i) |> Polynomial.natDegree) + 1),
          |(map (Int.castRingHom ℝ) (P.coeff i) |> Polynomial.coeff) j|) (Finset.mem_range.mpr hi)
    · linarith [abs_nonneg x]
    · exact Finset.le_sup (f := fun i ↦ Polynomial.natDegree (Polynomial.map (Int.castRingHom ℝ) (P.coeff i)))
        (Finset.mem_range.mpr hi)
  -- Apply cauchy_root_bound_max to qc with the bound B(x): ‖(g x : ℂ)‖ ≤ 1 + d * B(x).
  have h_cauchy_bound : ∀ x : ℝ, ↑T₀ ≤ x → ‖(g x : ℂ)‖ ≤ 1 + d * S * (1 + |x|) ^ N := by
    intro x hx
    set qc := (P.map (evalIntPolyReal x)).map (algebraMap ℝ ℂ) with hqc_def
    have hqc_root : qc.IsRoot (g x : ℂ) := by
      simp_all [Polynomial.eval_map]
      convert congr_arg (algebraMap ℝ ℂ) (hroot x hx) using 1
      simp [Polynomial.eval₂_map]
      simp [Polynomial.eval₂_eq_sum_range]
    have hqc_monic : qc.Monic :=
      Polynomial.Monic.map _ (evalIntPolyReal_map_monic _ hP_monic _)
    have hqc_deg : qc.natDegree = d := by
      rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero, Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;>
        norm_num [hP_monic, hP_deg]
      intro h
      simp_all [Polynomial.Monic.def]
    have hqc_coeff_bound : ∀ i < d, ‖qc.coeff i‖ ≤ S * (1 + |x|) ^ N := by
      intro i hi
      specialize h_coeff_bound x i hi
      simp_all [Polynomial.coeff_map]
    have := cauchy_root_bound_max hqc_monic hqc_root (by linarith)
      (fun i hi ↦ hqc_coeff_bound i (by linarith [hqc_deg ▸ hi]))
    simp_all [mul_assoc]
  refine ⟨1 + d * S, N, ?_, ?_⟩
  · have hS_nonneg : (0 : ℝ) ≤ S :=
      le_trans (by norm_num)
        (Finset.le_sup'
          (fun i ↦ ∑ j ∈ Finset.range ((map (Int.castRingHom ℝ) (P.coeff i) |> Polynomial.natDegree) + 1),
            |(map (Int.castRingHom ℝ) (P.coeff i) |> Polynomial.coeff) j|)
          (Finset.mem_range.mpr hP_deg) |> le_trans (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
    exact add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hS_nonneg)
  · intro x hx
    specialize h_cauchy_bound x hx
    norm_num at h_cauchy_bound ⊢
    have h1x : (1 : ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
    have := pow_le_pow_right₀ h1x (Nat.zero_le N)
    nlinarith

/-
**A continuous real root selection eventually coincides with a single smooth branch.**

For `P` monic in `Y` of `Y`-degree `≥ 2`, let `g` be *any* continuous function on a tail
`[T₀, ∞)` that is a genuine real root of the specialization `P(x, ·)` there.  Then there is a
tail `[T₁, ∞)` and a finite family of `C^∞` root branches `b i` (the ordered real-root
branches of the squarefree family, from `SmoothRootBranches`) such that `g` agrees on
`[T₁, ∞)` with a *single* branch `b j`.

This is the elementary "no branch switching" step: the ordered branches are pairwise
distinct on the tail, so the closed sets `{x | g x = b i x}` are disjoint and cover the
connected tail; hence exactly one of them is the whole tail.  It reduces the classification
of an arbitrary smooth real root selection to that of one of the finitely many constructed
branches.
-/
lemma real_root_branch_eq_ordered_branch
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0) :
    ∃ (n : ℕ) (b : Fin n → ℝ → ℝ) (T₁ : ℝ) (j : Fin n),
      (T₀ : ℝ) ≤ T₁ ∧
      (∀ i, ContDiffOn ℝ ⊤ (b i) (Set.Ici T₁)) ∧
      (∀ i x, T₁ ≤ x → (P.map (evalIntPolyReal x)).eval (b i x) = 0) ∧
      (∀ x, T₁ ≤ x → g x = b j x) := by
  obtain ⟨d, R, Tr, hTr, hd, hRmon, hRdeg, hRsmooth, hRsep, hRroots⟩ :=
    exists_smooth_separable_reduction P hP_monic hP_deg
  -- Apply `SmoothRootBranches.smooth_separable_family_root_branches` to get the branches `b`.
  obtain ⟨n, b, hb⟩ :=
    SmoothRootBranches.smooth_separable_family_root_branches R (Tr : ℝ) d hd hRmon hRdeg hRsmooth hRsep
  -- Define the index function `f : S → Fin n` by `f x = the unique i with g x = b i x`.
  obtain ⟨f, hf⟩ : ∃ f : ℝ → Fin n, ∀ x : ℝ, (max T₀ Tr : ℝ) ≤ x → g x = b (f x) x := by
    have hf_exists : ∀ x : ℝ, (max T₀ Tr : ℝ) ≤ x → ∃ j : Fin n, g x = b j x := by
      intro x hx
      obtain ⟨j, hj⟩ := hb.2.2.1 x (le_trans (le_max_right _ _) hx) (g x)
        (hRroots x (le_trans (le_max_right _ _) hx) _ |>.2 (hroot x (le_trans (le_max_left _ _) hx)))
      exact ⟨j, hj.symm⟩
    refine ⟨fun x ↦ if hx : max (T₀ : ℝ) Tr ≤ x then Classical.choose (hf_exists x hx) else ⟨0, ?_⟩, ?_⟩
    · cases n <;> norm_num at *
      linarith [hf_exists (Max.max (T₀ : ℝ) Tr) (le_max_left _ _), le_max_right (T₀ : ℝ) Tr]
    · exact fun x hx ↦ by simpa [hx] using Classical.choose_spec (hf_exists x hx)
  -- Show that `f` is locally constant on `S`.
  have hf_loc_const :
      ∀ x : ℝ, (max T₀ Tr : ℝ) ≤ x → ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, (max T₀ Tr : ℝ) ≤ y → f y = f x := by
    intro x hx
    have h_cont_exists :
        ∀ i : Fin n, i ≠ f x → ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, (max T₀ Tr : ℝ) ≤ y → b i y ≠ g y := by
      intro i hi_ne_fx
      have h_cont_bg : ContinuousOn (fun y ↦ b i y - g y) (Set.Ici (max T₀ Tr : ℝ)) :=
        ContinuousOn.sub
          ((hb.1 i).continuousOn.mono <| Set.Ici_subset_Ici.mpr <| by norm_num)
          (hg.mono <| Set.Ici_subset_Ici.mpr <| by norm_num)
      have := Metric.continuousOn_iff.mp h_cont_bg x hx
      have hne : b i x ≠ g x := by
        intro h
        have := hb.2.2.2 x (by linarith [le_max_right (T₀ : ℝ) Tr])
        exact hi_ne_fx <| this <| by aesop
      obtain ⟨δ, δ_pos, H⟩ := this (|b i x - g x|) (abs_pos.mpr (sub_ne_zero.mpr hne))
      refine ⟨Metric.ball x δ, Metric.isOpen_ball, Metric.mem_ball_self δ_pos, fun y hy₁ hy₂ hy₃ ↦ ?_⟩
      have := H y hy₂ hy₁
      cases abs_cases (b i x - g x) <;> linarith [abs_lt.mp this]
    choose! U hU₁ hU₂ hU₃ using h_cont_exists
    use ⋂ i ∈ Finset.univ.erase (f x), U i
    simp_all [Finset.mem_erase, Finset.mem_univ, Set.mem_iInter]
    constructor
    · exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun hi ↦ hU₁ i hi
    · grind
  -- Since `S` is preconnected and `f` is locally constant on `S`, `f` is constant on `S`.
  have hf_const : ∀ x y : ℝ, (max T₀ Tr : ℝ) ≤ x → (max T₀ Tr : ℝ) ≤ y → f x = f y := by
    intros x y hx hy
    have h_preconn : IsPreconnected (Set.Ici (max T₀ Tr : ℝ)) := isPreconnected_Ici
    have h_const : IsLocallyConstant (fun x : Set.Ici (max T₀ Tr : ℝ) ↦ f x) := by
      intro x
      rw [isOpen_iff_mem_nhds]
      intro y hy
      obtain ⟨U, hU₁, hU₂, hU₃⟩ := hf_loc_const y y.2
      filter_upwards
        [IsOpen.mem_nhds (show IsOpen (Subtype.val ⁻¹' U) from hU₁.preimage continuous_subtype_val) hU₂]
        with z hz using by aesop
    have huniv : IsPreconnected (Set.univ : Set (Set.Ici (max (T₀ : ℝ) Tr))) := by
      convert ‹IsPreconnected (Set.Ici (max (T₀ : ℝ) Tr)) ›.image
        (fun x : ℝ ↦ (⟨Max.max (T₀ : ℝ) Tr + Max.max (0 : ℝ) (x - Max.max (T₀ : ℝ) Tr), by norm_num⟩ :
          ↥(Set.Ici (max (T₀ : ℝ) Tr))))
        (by fun_prop)
      grind
    have := h_const.apply_eq_of_isPreconnected huniv (Set.mem_univ ⟨x, hx⟩) (Set.mem_univ ⟨y, hy⟩)
    aesop
  refine ⟨n, b, max T₀ Tr, f (max T₀ Tr), ?_, ?_, ?_, ?_⟩ <;> norm_num
  · exact fun i ↦ (hb.1 i).mono <| Set.Ici_subset_Ici.mpr <| le_max_right _ _
  · exact fun i x hx₁ hx₂ ↦ hRroots x hx₂ _ |>.1 (hb.2.1 i x hx₂)
  · intro x hx₁ hx₂
    have hmx : max (T₀ : ℝ) Tr ≤ x := by cases max_cases (T₀ : ℝ) Tr <;> linarith
    rw [hf x hmx, hf_const x (max (T₀ : ℝ) Tr) hmx le_rfl]




end
