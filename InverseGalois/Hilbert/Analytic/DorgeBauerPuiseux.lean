import InverseGalois.Hilbert.Analytic.PuiseuxTail

/-!
# Dörge–Bauer density estimate (assembled after the Puiseux tail bound) -/

open Polynomial ResolventConstruction

noncomputable section

section PuiseuxDataComputation
open Filter Topology

/-- **Deep Newton–Puiseux input (branch-continuation form).** -/
lemma real_branch_full_holomorphic_continuation
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (hnp : ¬ ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x) :
    ∃ (poly : Polynomial ℝ) (I : Finset ℝ) (a : ℝ → ℝ) (s s' A T : ℝ) (H : ℂ → ℂ),
      s ∈ I ∧ (∀ σ ∈ I, σ ≤ s) ∧ (∀ i : ℕ, s ≠ (i : ℝ)) ∧ a s ≠ 0 ∧ s' < s ∧
      0 ≤ A ∧ (2 * (T₀ : ℝ)) ≤ T ∧ (2 : ℝ) ≤ T ∧
      (∀ x : ℝ, T ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2))) ∧
      (∀ y : ℝ, T / 2 ≤ y → H (y : ℂ) = (g y : ℂ)) ∧
      (∀ x : ℝ, T ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
        ‖H z - (poly.map (algebraMap ℝ ℂ)).eval z - ∑ σ ∈ I, (a σ : ℂ) * z ^ (σ : ℂ)‖
          ≤ A * x ^ s') := by
  -- `P` has positive `Y`-degree: otherwise `P = C 1`, whose specialization has no root,
  -- contradicting `hroot`.
  have hP_deg : 1 ≤ P.natDegree := by
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
    · exfalso
      have hPC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
      have hc0 : P.coeff 0 = 1 := by
        have h : P.leadingCoeff = 1 := hP_monic
        rwa [Polynomial.leadingCoeff, h0] at h
      have hr := hroot (T₀ : ℝ) le_rfl
      rw [hPC, hc0] at hr
      simp [evalIntPolyReal] at hr
    · exact hpos
  -- Separable radical reduction of the family over `ℂ`.
  obtain ⟨Q, B, hQmonic, hQdvd, hB, hQsep, hQsame⟩ :=
    ComplexSeparableReduction.exists_complex_separable_reduction P hP_monic hP_deg
  -- `g` is also a branch root of `Q`, since `Q` and `P` share complex specialisation roots.
  have hrootQ : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (Q.map (evalIntPolyReal x)).eval (g x) = 0 := by
    intro x hx
    have hPc : (P.map (evalIntPolyComplex (x : ℂ))).eval ((g x : ℂ)) = 0 := by
      rw [evalIntPolyComplex_ofReal, hroot x hx]; norm_num
    have hQc : (Q.map (evalIntPolyComplex (x : ℂ))).eval ((g x : ℂ)) = 0 :=
      (hQsame (x : ℂ) ((g x : ℂ))).mpr hPc
    rw [evalIntPolyComplex_ofReal] at hQc
    exact_mod_cast hQc

  -- and the Newton–Puiseux tail bound (`sphere_bound_of_continuation`) in `PuiseuxTail`.
  exact DorgeBauer.real_branch_full_holomorphic_continuation_of_sep
    Q hQmonic T₀ g B hg hrootQ hnp hQsep

/-- **Deep Newton–Puiseux input (holomorphic-representation form).**

This is the single genuinely deep analytic input.  It packages the convergent Newton–Puiseux
/ Staudt expansion of the real algebraic branch `g` at infinity together with its complex
holomorphic continuation.  For a smooth non-polynomial real branch `g` of the monic family
`P(x, ·)` on a tail `[T₀, ∞)`, it asserts the existence of: -/
lemma real_branch_holomorphic_puiseux_representation
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (hnp : ¬ ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x) :
    ∃ (poly : Polynomial ℝ) (I : Finset ℝ) (a : ℝ → ℝ) (s s' A T : ℝ) (G : ℂ → ℂ),
      s ∈ I ∧ (∀ σ ∈ I, σ ≤ s) ∧ (∀ i : ℕ, s ≠ (i : ℝ)) ∧ a s ≠ 0 ∧ s' < s ∧
      0 ≤ A ∧ (2 * (T₀ : ℝ)) ≤ T ∧ (2 : ℝ) ≤ T ∧
      (∀ x : ℝ, T ≤ x → DiffContOnCl ℂ G (Metric.ball (x : ℂ) (x / 2))) ∧
      (∀ y : ℝ, T / 2 ≤ y →
        G (y : ℂ) = ((g y - poly.eval y - ∑ σ ∈ I, a σ * y ^ σ : ℝ) : ℂ)) ∧
      (∀ x : ℝ, T ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2), ‖G z‖ ≤ A * x ^ s') := by
  -- Take the deep branch continuation `H` and subtract the explicit principal part.
  obtain ⟨poly, I, a, s, s', A, T, H, hsI, hstop, hsnat, has, hss', hA, hT0, hT2,
      hHdc, hHag, hHb⟩ :=
    real_branch_full_holomorphic_continuation P hP_monic T₀ g hg hroot hnp
  refine ⟨poly, I, a, s, s', A, T,
    (fun z => H z - (poly.map (algebraMap ℝ ℂ)).eval z - ∑ σ ∈ I, (a σ : ℂ) * z ^ (σ : ℂ)),
    hsI, hstop, hsnat, has, hss', hA, hT0, hT2, ?_, ?_, ?_⟩
  · -- Holomorphy of the remainder: `H` minus the (holomorphic) principal part.
    intro x hx
    have h1 := hHdc x hx
    have h2 := puiseux_principal_part_diffContOnCl x (le_trans hT2 hx)
      (poly.map (algebraMap ℝ ℂ)) I (fun σ => (a σ : ℂ))
    simpa [sub_sub] using h1.sub h2
  · -- Agreement with the real remainder on the real axis (`cpow = rpow` for `y > 0`).
    intro y hy
    have hypos : (0 : ℝ) ≤ y := by linarith [hT2, hy]
    show H (y : ℂ) - (poly.map (algebraMap ℝ ℂ)).eval (y : ℂ)
        - ∑ σ ∈ I, (a σ : ℂ) * (y : ℂ) ^ (σ : ℂ)
      = ((g y - poly.eval y - ∑ σ ∈ I, a σ * y ^ σ : ℝ) : ℂ)
    rw [hHag y hy]
    have hpe : (poly.map (algebraMap ℝ ℂ)).eval (y : ℂ) = ((poly.eval y : ℝ) : ℂ) := by
      rw [Polynomial.eval_map, show (y : ℂ) = algebraMap ℝ ℂ y from rfl,
        Polynomial.eval₂_at_apply]
      simp
    rw [hpe]
    have hcpow : ∀ σ : ℝ, (a σ : ℂ) * (y : ℂ) ^ (σ : ℂ) = (((a σ) * y ^ σ : ℝ) : ℂ) := by
      intro σ; rw [Complex.ofReal_mul, Complex.ofReal_cpow hypos]
    rw [Finset.sum_congr rfl (fun σ _ => hcpow σ)]
    push_cast; ring
  · -- The sphere bound is exactly the deep input's bound.
    intro x hx z hz
    exact hHb x hx z hz

/- -/
lemma real_root_branch_puiseux_remainder_bound
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (hnp : ¬ ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x) :
    ∃ (poly : Polynomial ℝ) (I : Finset ℝ) (a : ℝ → ℝ) (s s' : ℝ),
      s ∈ I ∧ (∀ σ ∈ I, σ ≤ s) ∧ (∀ i : ℕ, s ≠ (i : ℝ)) ∧ a s ≠ 0 ∧ s' < s ∧
      ∃ T : ℝ, ∀ m : ℕ, ∃ C : ℝ, ∀ x : ℝ, T ≤ x →
        |iteratedDeriv m (fun y => g y - poly.eval y - ∑ σ ∈ I, a σ * y ^ σ) x|
          ≤ C * x ^ (s' - (m : ℝ)) := by
  have := @real_branch_holomorphic_puiseux_representation P hP_monic T₀ g hg hroot hnp;
  obtain ⟨ poly, I, a, s, s', A, T, G, hsI, hstop, hsnat, has, hss', hA, hT1, hT2, hDC, hagree, hbound ⟩ := this; use poly, I, a, s, s', hsI, hstop, hsnat, has, hss'; use T;
  intro m
  use (m.factorial : ℝ) * A * 2 ^ m;
  intro x hx
  have h_cont_diff : ContDiffOn ℝ ⊤ (fun y => g y - poly.eval y - ∑ σ ∈ I, a σ * y ^ σ) (Set.Ioo (x - x / 2) (x + x / 2)) := by
    refine' ContDiffOn.sub ( ContDiffOn.sub ( hg.mono _ ) _ ) _;
    · exact fun y hy => show ( T₀ : ℝ ) ≤ y by linarith [ hy.1, hy.2, show ( T₀ : ℝ ) ≤ T / 2 by linarith ] ;
    · exact ContDiff.contDiffOn ( by simpa only [ Polynomial.eval_eq_sum_range ] using ContDiff.sum fun i hi => ContDiff.mul ( contDiff_const ) ( contDiff_id.pow i ) );
    · refine' ContDiffOn.sum fun σ hσ => ContDiffOn.mul _ _;
      · exact contDiffOn_const;
      · exact ContDiffOn.rpow contDiffOn_id contDiffOn_const <| by intro y hy; exact ne_of_gt <| by linarith [ hy.1, hy.2 ] ;
  have := abs_iteratedDeriv_le_of_holo_extension ( fun y => g y - poly.eval y - ∑ σ ∈ I, a σ * y ^ σ ) G x ( x / 2 ) ( A * x ^ s' ) m ( by linarith ) ( hDC x hx ) h_cont_diff ( fun y hy => hagree y ( by linarith [ hy.1, hy.2 ] ) ) ( fun z hz => hbound x hx z hz );
  convert this using 1 ; norm_num [ Real.rpow_sub ( by linarith : 0 < x ) ] ; ring;
  norm_num

/-- **Deep Newton–Puiseux input (principal-part form).**  The `Tendsto … 0` remainder form of
the finite Puiseux principal part; it is now *proved* from the explicit-rate deep input
`real_root_branch_puiseux_remainder_bound` by an elementary squeeze (`s' − s < 0`).  For a
smooth non-polynomial real branch `g` of the monic family `P(x, ·)` on a tail, there is a
polynomial part `poly` and a finite non-integer Puiseux part `F = ∑_{σ ∈ I} a σ · x^σ` with
non-natural top exponent `s := max I` and nonzero leading coefficient `a s ≠ 0`, whose
remainder `g − poly − F` decays faster than the leading term in every derivative order. -/
lemma real_root_branch_puiseux_principal_part
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (hnp : ¬ ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x) :
    ∃ (poly : Polynomial ℝ) (I : Finset ℝ) (a : ℝ → ℝ) (s : ℝ),
      s ∈ I ∧ (∀ σ ∈ I, σ ≤ s) ∧ (∀ i : ℕ, s ≠ (i : ℝ)) ∧ a s ≠ 0 ∧
      ∀ m : ℕ, Filter.Tendsto
        (fun x => iteratedDeriv m
            (fun y => g y - poly.eval y - ∑ σ ∈ I, a σ * y ^ σ) x / x ^ (s - (m : ℝ)))
        Filter.atTop (nhds 0) := by
  -- Deep input in explicit-rate form: the remainder derivatives are bounded by `x^{s'-m}`
  -- with `s' < s`.  The `Tendsto … 0` conclusion is then an elementary squeeze.
  obtain ⟨poly, I, a, s, s', hsI, hstop, hsnat, has, hss', T, hbound⟩ :=
    real_root_branch_puiseux_remainder_bound P hP_monic T₀ g hg hroot hnp
  refine ⟨poly, I, a, s, hsI, hstop, hsnat, has, fun m => ?_⟩
  obtain ⟨C, hC⟩ := hbound m
  -- Squeeze: `|R⁽ᵐ⁾(x) / x^{s-m}| ≤ C · x^{s'-s}` on the tail, and `C · x^{s'-s} → 0`.
  apply squeeze_zero_norm' (a := fun x => C * x ^ (s' - s))
  · filter_upwards [eventually_ge_atTop (max T 1)] with x hxm
    have hx : T ≤ x := le_trans (le_max_left _ _) hxm
    have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hxm
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
    have hxpow : (0 : ℝ) < x ^ (s - (m : ℝ)) := Real.rpow_pos_of_pos hx0 _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hxpow, div_le_iff₀ hxpow]
    calc |iteratedDeriv m (fun y => g y - poly.eval y - ∑ σ ∈ I, a σ * y ^ σ) x|
          ≤ C * x ^ (s' - (m : ℝ)) := hC x hx
      _ = C * x ^ (s' - s) * x ^ (s - (m : ℝ)) := by
            rw [mul_assoc, ← Real.rpow_add hx0,
              show s' - s + (s - (m : ℝ)) = s' - (m : ℝ) from by ring]
  · have h0 : Filter.Tendsto (fun x : ℝ => x ^ (s' - s)) Filter.atTop (nhds 0) := by
      have := tendsto_rpow_neg_atTop (y := s - s') (by linarith)
      simpa [neg_sub] using this
    simpa using h0.const_mul C

/-- **Deep Newton–Puiseux input: leading derivative asymptotic of a non-polynomial real
algebraic branch.**

This isolates the single genuinely analytic input behind `real_root_branch_classify`.  If a
smooth real branch `g` of the monic family `P(x, ·)` on a tail `[T₀, ∞)` is *not* eventually
equal to a real polynomial, then it carries a Newton–Puiseux leading derivative asymptotic
`g⁽ᵐ⁾(x) ∼ c · (descPochhammer ℝ m).eval s · x^{s−m}` for all high `m`, with a nonzero
coefficient `c ≠ 0` and a non-natural exponent `s ∉ ℕ`. -/
lemma real_root_branch_puiseux_data
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (hnp : ¬ ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x) :
    ∃ (s c : ℝ) (m₀ : ℕ), c ≠ 0 ∧ (∀ i : ℕ, s ≠ (i : ℝ)) ∧
      ∀ m : ℕ, m₀ ≤ m →
        Filter.Tendsto (fun x => iteratedDeriv m g x / x ^ (s - (m : ℝ)))
          Filter.atTop (nhds (c * Polynomial.eval s (descPochhammer ℝ m))) := by
  -- Deep input: the polynomial part `poly` and the finite non-integer Puiseux part
  -- `F = ∑ a σ x^σ` (top exponent `s`, non-natural, nonzero coefficient).
  obtain ⟨poly, I, a, s, hsI, hstop, hsnat, has, hrem⟩ :=
    real_root_branch_puiseux_principal_part P hP_monic T₀ g hg hroot hnp
  -- Beyond the degree of the polynomial part, `poly` no longer contributes to the
  -- derivative, so the leading behaviour is governed by the non-integer part.
  refine ⟨s, a s, poly.natDegree + 1, has, hsnat, fun m hm => ?_⟩
  -- Combine the remainder decay with the leading-term computation.
  have hadd := (hrem m).add (finite_puiseux_deriv_asymptotic I a s hsI hstop m)
  rw [zero_add] at hadd
  apply hadd.congr'
  filter_upwards [eventually_gt_atTop (max (T₀ : ℝ) 0)] with x hx
  simp only [max_lt_iff] at hx
  obtain ⟨hxT, hx0⟩ := hx
  have hgat : ContDiffAt ℝ (m:ℕ) g x := (hg.contDiffAt (Ici_mem_nhds hxT)).of_le le_top
  have hFat : ContDiffAt ℝ (m:ℕ) (fun y => ∑ σ ∈ I, a σ * y ^ σ) x := by
    apply ContDiffAt.sum
    intro σ hσ
    have : ContDiffAt ℝ (m:ℕ∞) (fun y : ℝ => y ^ σ) x :=
      Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx0)
    exact (contDiffAt_const).mul (by exact_mod_cast this)
  have hPat : ContDiffAt ℝ (m:ℕ) (fun y => poly.eval y) x := by
    have heq : (fun y : ℝ => (aeval y) poly) = (fun y => poly.eval y) := by
      funext y; simp [Polynomial.aeval_def, Polynomial.eval₂_id]
    rw [← heq]
    exact (contDiff_aeval (𝕜 := ℝ) poly (n := (⊤ : WithTop ℕ∞))).contDiffAt.of_le le_top
  -- The polynomial part vanishes in the `m`-th derivative once `m > deg poly`.
  have hqzero : iteratedDeriv m (fun y => poly.eval y) x = 0 :=
    iteratedDeriv_polynomial_eval_zero poly m (by omega) x
  have hsub : ContDiffAt ℝ (m:ℕ) (fun y => g y - poly.eval y - ∑ σ ∈ I, a σ * y ^ σ) x :=
    (hgat.sub hPat).sub hFat
  have hfeq : ((fun y => g y - poly.eval y - ∑ σ ∈ I, a σ * y ^ σ)
      + (fun y => poly.eval y) + fun y => ∑ σ ∈ I, a σ * y ^ σ) = g := by
    funext y; simp only [Pi.add_apply]; ring
  have h12cd : ContDiffAt ℝ (m:ℕ)
      ((fun y => g y - poly.eval y - ∑ σ ∈ I, a σ * y ^ σ) + fun y => poly.eval y) x :=
    hsub.add hPat
  have key : iteratedDeriv m g x
      = iteratedDeriv m (fun y => g y - poly.eval y - ∑ σ ∈ I, a σ * y ^ σ) x
        + iteratedDeriv m (fun y => poly.eval y) x
        + iteratedDeriv m (fun y => ∑ σ ∈ I, a σ * y ^ σ) x := by
    conv_lhs => rw [← hfeq]
    rw [iteratedDeriv_add h12cd hFat, iteratedDeriv_add hsub hPat]
  rw [key, hqzero]
  ring

end PuiseuxDataComputation

lemma real_root_branch_classify
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0) :
    (∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x) ∨
    (∃ (s c : ℝ) (m₀ : ℕ), c ≠ 0 ∧ (∀ i : ℕ, s ≠ (i : ℝ)) ∧
      ∀ m : ℕ, m₀ ≤ m →
        Filter.Tendsto (fun x => iteratedDeriv m g x / x ^ (s - (m : ℝ)))
          Filter.atTop (nhds (c * Polynomial.eval s (descPochhammer ℝ m)))) := by
  -- The dichotomy is a case split on whether `g` is eventually a polynomial; the
  -- non-polynomial case is exactly the deep Newton–Puiseux input
  -- `real_root_branch_puiseux_data`.
  by_cases hpoly : ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x
  · exact Or.inl hpoly
  · exact Or.inr (real_root_branch_puiseux_data P hP_monic T₀ g hg hroot hpoly)

/-- **Newton–Puiseux existence of the real algebraic branches at infinity (deep analytic
core).**

This is the cleaned-up analytic core behind `real_algebraic_branches`.  For `P` monic in
`Y` of `Y`-degree `≥ 2` with no root in `ℚ(T)`, there are finitely many real branch
functions `g j`, `C^∞` on a tail `[T₀, ∞)`, tagged `good`/`bad` (`kind`), such that:

* **good branches** carry the Newton–Puiseux leading derivative asymptotic with `c j ≠ 0`
  and a non-natural exponent `s j ∉ ℕ` (this includes negative-integer leading exponents,
  which are `∉ ℕ`);
* **bad branches** are *exactly a real polynomial* `q` on the tail (`g j = q` there) and are
  genuine real roots of `P` there (`P(x, q(x)) = 0`).  This is the honest Newton–Puiseux
  dichotomy: a branch either has a surviving non-integer exponent (good) or has only
  non-negative integer exponents, i.e. is a polynomial (bad);
* together the branches cover every integer root of `P(t, ·)` for `t ≥ T₀`.

Unlike the packaged `real_algebraic_branches`, this core does *not* assert finiteness of the
integer values of the bad branches: that number-theoretic step is discharged in
`real_algebraic_branches` from this core using `realPoly_ratl_of_infinite_int_values` and
`ratl_eventual_root_gives_ratFunc_root`. -/
lemma real_branches_puiseux
    (P : Polynomial (Polynomial ℤ))
    (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree)
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) :
    ∃ (n : ℕ) (T₀ : ℤ) (g : Fin n → ℝ → ℝ) (kind : Fin n → Prop)
      (s c : Fin n → ℝ) (m₀ : Fin n → ℕ),
      1 ≤ T₀ ∧
      (∀ j, ContDiffOn ℝ ⊤ (g j) (Set.Ici (T₀ : ℝ))) ∧
      (∀ j, kind j → c j ≠ 0) ∧
      (∀ j, kind j → ∀ i : ℕ, s j ≠ (i : ℝ)) ∧
      (∀ j, kind j → ∀ m : ℕ, m₀ j ≤ m →
          Filter.Tendsto (fun x => iteratedDeriv m (g j) x / x ^ (s j - (m : ℝ)))
            Filter.atTop (nhds (c j * Polynomial.eval (s j) (descPochhammer ℝ m)))) ∧
      (∀ j, ¬ kind j → ∃ q : Polynomial ℝ,
          (∀ x : ℝ, (T₀ : ℝ) ≤ x → g j x = q.eval x) ∧
          (∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (q.eval x) = 0)) ∧
      (∀ t : ℤ, T₀ ≤ t → ∀ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y →
          ∃ j, g j (t : ℝ) = (y : ℝ)) := by
  classical
  -- Construction kernel: smooth real root branches covering all integer roots.
  obtain ⟨n, T₀, g, hT₀, hcd, hroot, hcov⟩ := real_root_branches_cover P hP_monic hP_deg
  -- A branch is `good` (`kind j`) exactly when it is NOT eventually a polynomial.
  set kind : Fin n → Prop :=
    fun j => ¬ ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g j x = q.eval x with hkind
  -- Classification kernel supplies the good-branch asymptotic data whenever `kind j`.
  have hgood : ∀ j, kind j → ∃ (s c : ℝ) (m₀ : ℕ), c ≠ 0 ∧ (∀ i : ℕ, s ≠ (i : ℝ)) ∧
      ∀ m : ℕ, m₀ ≤ m →
        Filter.Tendsto (fun x => iteratedDeriv m (g j) x / x ^ (s - (m : ℝ)))
          Filter.atTop (nhds (c * Polynomial.eval s (descPochhammer ℝ m))) := by
    intro j hj
    rcases real_root_branch_classify P hP_monic T₀ (g j) (hcd j) (hroot j) with hbad | hgood
    · exact absurd hbad hj
    · exact hgood
  choose! s c m₀ hgood' using hgood
  refine ⟨n, T₀, g, kind, s, c, m₀, hT₀, hcd, ?_, ?_, ?_, ?_, hcov⟩
  · exact fun j hj => (hgood' j hj).1
  · exact fun j hj => (hgood' j hj).2.1
  · exact fun j hj => (hgood' j hj).2.2
  · intro j hj
    have hq : ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g j x = q.eval x := not_not.mp hj
    obtain ⟨q, hq⟩ := hq
    exact ⟨q, hq, fun x hx => by rw [← hq x hx]; exact hroot j x hx⟩

/-
**Existence of the real algebraic branches at infinity, split into good and bad
branches (deep analytic input).**

For `P ∈ ℤ[T][Y]` monic in `Y` of `Y`-degree `≥ 2` with no root in `ℚ(T)`, there are
finitely many real branch functions `g j` defined and `C^∞` on a tail `[T₀, ∞)`, together
covering every integer root of `P(t, ·)` for `t ≥ T₀`.  Each branch is tagged by a
predicate `kind j`:

* **good branches** (`kind j`) carry the genuine Newton–Puiseux leading derivative
  asymptotic for all high-order derivatives
  `(g j)⁽ᵐ⁾(x) ∼ c j · (descPochhammer ℝ m).eval (s j) · x^{s j − m}`  (`m ≥ m₀ j`),
  with nonzero coefficient `c j ≠ 0` and a non-natural exponent `s j ∉ ℕ`;
* **bad branches** (`¬ kind j`) are the branches that are eventually a polynomial with an
  irrational coefficient (a rational one would be a `ℚ(T)`-root, excluded by
  `hP_no_root`); such a polynomial takes an integer value at only finitely many integers,
  so on a large enough tail `[T₀,∞)` a bad branch never takes an integer value:
  `¬ ∃ z : ℤ, g j t = z`. -/
lemma real_algebraic_branches
    (P : Polynomial (Polynomial ℤ))
    (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree)
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) :
    ∃ (n : ℕ) (T₀ : ℤ) (g : Fin n → ℝ → ℝ) (kind : Fin n → Prop)
      (s c : Fin n → ℝ) (m₀ : Fin n → ℕ),
      1 ≤ T₀ ∧
      (∀ j, ContDiffOn ℝ ⊤ (g j) (Set.Ici (T₀ : ℝ))) ∧
      (∀ j, kind j → c j ≠ 0) ∧
      (∀ j, kind j → ∀ i : ℕ, s j ≠ (i : ℝ)) ∧
      (∀ j, kind j → ∀ m : ℕ, m₀ j ≤ m →
          Filter.Tendsto (fun x => iteratedDeriv m (g j) x / x ^ (s j - (m : ℝ)))
            Filter.atTop (nhds (c j * Polynomial.eval (s j) (descPochhammer ℝ m)))) ∧
      (∀ j, ¬ kind j → ∀ t : ℤ, T₀ ≤ t → ¬ ∃ z : ℤ, g j (t : ℝ) = (z : ℝ)) ∧
      (∀ t : ℤ, T₀ ≤ t → ∀ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y →
          ∃ j, g j (t : ℝ) = (y : ℝ)) := by
  obtain ⟨ n, T₀, g, kind, s, c, m₀, hT₀, hcd, hc, hs, hasymp, hbadpoly, hcov ⟩ := real_branches_puiseux P hP_monic hP_deg hP_no_root;
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℤ, T₀ ≤ T₁ ∧ ∀ j : Fin n, ¬ kind j → ∀ t : ℤ, T₁ ≤ t → ¬∃ z : ℤ, g j (t : ℝ) = (z : ℝ) := by
    have hT₁_exists : ∀ j : Fin n, ¬ kind j → ∃ T₁ : ℤ, T₀ ≤ T₁ ∧ ∀ t : ℤ, T₁ ≤ t → ¬∃ z : ℤ, g j (t : ℝ) = (z : ℝ) := by
      intro j hj
      obtain ⟨q, hq⟩ := hbadpoly j hj
      have hq_inf : Set.Finite {t : ℤ | ∃ z : ℤ, q.eval (t : ℝ) = (z : ℝ)} := by
        by_contra h_inf_int_roots
        obtain ⟨q', hq'⟩ := realPoly_ratl_of_infinite_int_values q h_inf_int_roots
        obtain ⟨a, ha⟩ := ratl_eventual_root_gives_ratFunc_root P (T₀ : ℝ) q' (by
        aesop);
        exact hP_no_root a ha;
      obtain ⟨ T₁, hT₁ ⟩ := hq_inf.bddAbove;
      exact ⟨ Max.max T₀ ( T₁ + 1 ), le_max_left _ _, fun t ht ⟨ z, hz ⟩ => by linarith [ hT₁ ⟨ z, by rw [ hq.1 t ( by exact_mod_cast le_trans ( le_max_left _ _ ) ht ) ] at hz; exact hz ⟩, le_max_right T₀ ( T₁ + 1 ) ] ⟩;
    choose! T₁ hT₁₁ hT₁₂ using hT₁_exists;
    use sSup (Set.range T₁) ⊔ T₀;
    exact ⟨ le_max_right _ _, fun j hj t ht => hT₁₂ j hj t <| le_trans ( le_csSup ( Set.finite_range T₁ |> Set.Finite.bddAbove ) <| Set.mem_range_self j ) <| le_trans ( le_max_left _ _ ) ht ⟩;
  use n, T₁, g, kind, s, c, m₀;
  exact ⟨ by linarith, fun j => hcd j |> ContDiffOn.mono <| Set.Ici_subset_Ici.mpr <| mod_cast by linarith, hc, hs, hasymp, hT₁.2, fun t ht y hy => hcov t ( by linarith ) y hy ⟩

/-- **Existence of the real Puiseux branches at infinity with leading derivative
asymptotics.**

This is the shape consumed by `real_branches_on_tail`: finitely many real branch functions
`g j`, `C^∞` on a tail `[T₀, ∞)`, *each* carrying the leading power asymptotic
`(g j)⁽ᵐ⁾(x) ∼ c j · (descPochhammer ℝ m).eval (s j) · x^{s j − m}` with `c j ≠ 0` and
`s j ∉ ℕ`, and together covering every integer root of `P(t, ·)` for `t ≥ T₀`. -/
lemma branch_leading_asymptotics
    (P : Polynomial (Polynomial ℤ))
    (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree)
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) :
    ∃ (n : ℕ) (T₀ : ℤ) (g : Fin n → ℝ → ℝ) (s c : Fin n → ℝ) (m₀ : Fin n → ℕ),
      1 ≤ T₀ ∧
      (∀ j, ContDiffOn ℝ ⊤ (g j) (Set.Ici (T₀ : ℝ))) ∧
      (∀ j, c j ≠ 0) ∧
      (∀ j, ∀ i : ℕ, s j ≠ (i : ℝ)) ∧
      (∀ j, ∀ m : ℕ, m₀ j ≤ m →
          Filter.Tendsto (fun x => iteratedDeriv m (g j) x / x ^ (s j - (m : ℝ)))
            Filter.atTop (nhds (c j * Polynomial.eval (s j) (descPochhammer ℝ m)))) ∧
      (∀ t : ℤ, T₀ ≤ t → ∀ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y →
          ∃ j, g j (t : ℝ) = (y : ℝ)) := by
  classical
  obtain ⟨n, T₀, g, kind, s, c, m₀, hT₀, hcd, hc, hs, hasymp, hbad, hcov⟩ :=
    real_algebraic_branches P hP_monic hP_deg hP_no_root
  refine ⟨n, T₀,
    fun j => if kind j then g j else dummyBranch,
    fun j => if kind j then s j else (1 / 2 : ℝ),
    fun j => if kind j then c j else 1,
    fun j => if kind j then m₀ j else 0,
    hT₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hk : kind j
    · simpa only [if_pos hk] using hcd j
    · simpa only [if_neg hk] using dummyBranch_contDiffOn_top T₀ hT₀
  · intro j
    by_cases hk : kind j
    · simpa only [if_pos hk] using hc j hk
    · simp only [if_neg hk]; norm_num
  · intro j i
    by_cases hk : kind j
    · simpa only [if_pos hk] using hs j hk i
    · simp only [if_neg hk]
      intro hi
      have h1 : (1 : ℝ) = 2 * i := by linarith
      have h2 : (1 : ℤ) = 2 * i := by exact_mod_cast h1
      omega
  · intro j m hm
    by_cases hk : kind j
    · simp only [if_pos hk] at hm ⊢; exact hasymp j hk m hm
    · simp only [if_neg hk] at hm ⊢; exact dummyBranch_deriv_asymptotic m
  · intro t ht y hy
    obtain ⟨j, hj⟩ := hcov t ht y hy
    have hkj : kind j := by
      by_contra hk
      exact hbad j hk t ht ⟨y, hj⟩
    exact ⟨j, by simp only [if_pos hkj]; exact hj⟩

lemma real_branches_on_tail
    (P : Polynomial (Polynomial ℤ))
    (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree)
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) :
    ∃ (n k₀ : ℕ),
      2 ≤ k₀ ∧
      ∀ k, k₀ ≤ k → ∃ (T₀ : ℤ) (g : Fin n → ℝ → ℝ),
        1 ≤ T₀ ∧
        (∀ j,
          ContDiffOn ℝ (k + 1) (g j) (Set.Ici (T₀ : ℝ)) ∧
          ((∀ x ∈ Set.Ioi (T₀ : ℝ), 0 < iteratedDerivWithin (k + 1) (g j) (Set.Ici (T₀ : ℝ)) x) ∨
            (∀ x ∈ Set.Ioi (T₀ : ℝ), iteratedDerivWithin (k + 1) (g j) (Set.Ici (T₀ : ℝ)) x < 0)) ∧
          Filter.Tendsto (iteratedDerivWithin k (g j) (Set.Ici (T₀ : ℝ))) Filter.atTop (nhds 0) ∧
          (∃ sj Lj : ℝ, sj < (k : ℝ) ∧
            Filter.Tendsto (fun x => iteratedDeriv k (g j) x / x ^ (sj - (k : ℝ)))
              Filter.atTop (nhds Lj))) ∧
        (∀ t : ℤ, T₀ ≤ t → ∀ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y →
            ∃ j, g j (t : ℝ) = (y : ℝ)) := by
  obtain ⟨ n, T₀, g, s, c, m₀, hT₀, hcd, hc, hs, hasymp, hcov ⟩ := branch_leading_asymptotics P hP_monic hP_deg hP_no_root;
  choose k₀ hk₀ using fun j => asymptotic_deriv_analytic_package ( g j ) ( s j ) ( c j ) ( hc j ) ( hs j ) ( m₀ j ) ( hasymp j );
  refine' ⟨ n, Finset.univ.sup k₀ ⊔ 2 ⊔ Finset.univ.sup (fun j => m₀ j + ⌈s j⌉₊ + 1), _, _ ⟩;
  · exact le_trans ( le_max_right _ _ ) ( le_max_left _ _ );
  · intro k hk;
    have hkk₀ : ∀ j, k₀ j ≤ k := fun j =>
      le_trans ( Finset.le_sup ( f := k₀ ) ( Finset.mem_univ j ) )
        ( le_trans ( le_max_left _ 2 ) ( le_trans ( le_max_left _ _ ) hk ) );
    have hkB : ∀ j, m₀ j + ⌈s j⌉₊ + 1 ≤ k := fun j =>
      le_trans ( Finset.le_sup ( f := fun j => m₀ j + ⌈s j⌉₊ + 1 ) ( Finset.mem_univ j ) )
        ( le_trans ( le_max_right _ _ ) hk );
    have hkm₀ : ∀ j, m₀ j ≤ k := fun j => by have := hkB j; omega;
    have hkss : ∀ j, (s j) < (k : ℝ) := fun j => by
      have h1 : (s j) ≤ (⌈s j⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ⌈s j⌉₊ + 1 ≤ k := by have := hkB j; omega
      have h2' : ((⌈s j⌉₊ : ℝ)) + 1 ≤ (k : ℝ) := by exact_mod_cast h2
      linarith;
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ j : Fin n, ∃ T₁ : ℝ, T₁ ≤ M ∧ ((∀ x, T₁ < x → 0 < iteratedDeriv (k + 1) (g j) x) ∨ (∀ x, T₁ < x → iteratedDeriv (k + 1) (g j) x < 0)) ∧ Filter.Tendsto (iteratedDeriv k (g j)) Filter.atTop (nhds 0) := by
      choose! T₁ hT₁ using fun j => hk₀ j |>.2 k ( hkk₀ j );
      exact ⟨ ⨆ j, T₁ j, fun j => ⟨ T₁ j, le_ciSup ( Finite.bddAbove_range T₁ ) j, hT₁ j ⟩ ⟩;
    refine' ⟨ ⌈M⌉₊ + T₀ ^ 2, g, _, _, _ ⟩ <;> norm_num;
    · exact le_add_of_nonneg_of_le ( Nat.cast_nonneg _ ) ( by nlinarith );
    · intro j; have hM' := hM j; rcases hM' with ⟨ T₁, hT₁₁, hT₁₂, hT₁₃ ⟩ ; refine' ⟨ _, _, _, _ ⟩;
      · exact ContDiffOn.mono ( hcd j ) ( Set.Ici_subset_Ici.mpr <| by nlinarith [ Nat.le_ceil M, show ( T₀ : ℝ ) ≥ 1 by norm_cast ] ) |> ContDiffOn.of_le <| by norm_num;
      · refine' Or.imp ( fun h => fun x hx => _ ) ( fun h => fun x hx => _ ) hT₁₂;
        · rw [ iteratedDerivWithin_eq_iteratedDeriv ];
          · exact h x ( by nlinarith [ Nat.le_ceil M, show ( T₀ : ℝ ) ≥ 1 by norm_cast ] );
          · exact uniqueDiffOn_Ici _;
          · have := hcd j;
            exact this.contDiffAt ( Ici_mem_nhds <| by nlinarith [ Nat.le_ceil M, show ( T₀ : ℝ ) ≥ 1 by norm_cast ] ) |> ContDiffAt.of_le <| by norm_num;
          · exact le_of_lt hx;
        · convert h x _ using 1;
          · rw [ iteratedDerivWithin_eq_iteratedDeriv ];
            · exact uniqueDiffOn_Ici _;
            · have := hcd j;
              exact this.contDiffAt ( Ici_mem_nhds <| by nlinarith [ Nat.le_ceil M, show ( T₀ : ℝ ) ≥ 1 by norm_cast ] ) |> ContDiffAt.of_le <| by norm_num;
            · exact le_of_lt hx;
          · nlinarith [ Nat.le_ceil M, show ( T₀ : ℝ ) ≥ 1 by norm_cast ];
      · refine' hT₁₃.congr' _;
        filter_upwards [ Filter.eventually_gt_atTop ( ⌈M⌉₊ + T₀ ^ 2 : ℝ ) ] with x hx;
        rw [ iteratedDerivWithin_eq_iteratedDeriv ];
        · exact uniqueDiffOn_Ici _;
        · exact hcd j |> fun h => h.contDiffAt ( Ici_mem_nhds <| by nlinarith [ Nat.le_ceil M, show ( T₀ : ℝ ) ≥ 1 by norm_cast ] ) |> ContDiffAt.of_le <| by norm_num;
        · exact le_of_lt hx;
      · refine ⟨ s j, hkss j, c j * Polynomial.eval ( s j ) ( descPochhammer ℝ k ), ?_ ⟩
        exact hasymp j k ( hkm₀ j )
    · exact fun t ht y hy => hcov t ( by nlinarith [ Nat.le_ceil M ] ) y hy

/-
**Power-decay of a branch from its leading asymptotic ratio.**

If a smooth function `g` on `[1,∞)` agrees, on a tail `[T₁,∞)`, with a branch `f` whose
`k`-th derivative has a *bounded* leading ratio
`f⁽ᵏ⁾(x) / x^{s-k} → L` at infinity, and `s < k`, then `g` satisfies `HasKDerivDecay g k`:
`|g⁽ᵏ⁾(x)| ≤ C₀·x^{-(k-s)}` on `[1,∞)` with `k - s > 0`.  On the tail the bound comes from
the convergent ratio (`|f⁽ᵏ⁾(x)| ≤ (|L|+1)·x^{s-k}` eventually, transported to `g` via the
agreement and `iteratedDerivWithin = iteratedDeriv` on the interior); on the compact initial
segment `[1,T*]` it comes from continuity of `g⁽ᵏ⁾` (from `ContDiffOn`).
-/
lemma hasKDerivDecay_of_agree_ratio
    (g f : ℝ → ℝ) (k : ℕ) (s L T₁ : ℝ)
    (hks : s < (k : ℝ))
    (hcd : ContDiffOn ℝ (k + 1) g (Set.Ici (1 : ℝ)))
    (hagree : ∀ x, T₁ ≤ x → g x = f x)
    (hratio : Filter.Tendsto (fun x => iteratedDeriv k f x / x ^ (s - (k : ℝ)))
      Filter.atTop (nhds L)) :
    HasKDerivDecay g k := by
  obtain ⟨Tstar, hTstar⟩ : ∃ Tstar : ℝ, 1 ≤ Tstar ∧ ∀ x ≥ Tstar, |iteratedDerivWithin k g (Set.Ici 1) x| ≤ (|L| + 1) * x ^ (s - k : ℝ) := by
    have h_eventually : ∃ Tstar : ℝ, ∀ x ≥ Tstar, |iteratedDeriv k f x| ≤ (|L| + 1) * x ^ (s - k : ℝ) := by
      obtain ⟨Tstar, hTstar⟩ : ∃ Tstar : ℝ, ∀ x ≥ Tstar, |(iteratedDeriv k f x) / x ^ (s - k : ℝ)| ≤ |L| + 1 := by
        exact Filter.eventually_atTop.mp ( hratio.abs.eventually ( ge_mem_nhds <| by linarith ) ) |> fun ⟨ Tstar, hTstar ⟩ ↦ ⟨ Tstar, fun x hx ↦ hTstar x hx ⟩;
      exact ⟨ Max.max Tstar 1, fun x hx => by have := hTstar x ( le_trans ( le_max_left _ _ ) hx ) ; rw [ abs_div, abs_of_nonneg ( Real.rpow_nonneg ( by linarith [ le_max_right Tstar 1 ] ) _ ) ] at this; rwa [ div_le_iff₀ ( Real.rpow_pos_of_pos ( by linarith [ le_max_right Tstar 1 ] ) _ ) ] at this ⟩;
    obtain ⟨Tstar, hTstar⟩ := h_eventually
    use max Tstar (max T₁ 1) + 1
    simp [hTstar];
    intro x hx
    have h_eq : iteratedDerivWithin k g (Set.Ici 1) x = iteratedDeriv k g x := by
      rw [ iteratedDerivWithin_eq_iteratedDeriv ];
      · exact uniqueDiffOn_Ici _;
      · exact hcd.contDiffAt ( Ici_mem_nhds <| by linarith [ le_max_left Tstar ( max T₁ 1 ), le_max_right Tstar ( max T₁ 1 ), le_max_left T₁ 1, le_max_right T₁ 1 ] ) |> ContDiffAt.of_le <| by norm_num;
      · grind
    have h_eq_f : iteratedDeriv k g x = iteratedDeriv k f x := by
      apply_rules [ Filter.EventuallyEq.iteratedDeriv_eq ];
      filter_upwards [ lt_mem_nhds ( show x > T₁ by linarith [ le_max_left Tstar ( max T₁ 1 ), le_max_right Tstar ( max T₁ 1 ), le_max_left T₁ 1, le_max_right T₁ 1 ] ) ] with y hy using hagree y hy.le
    rw [h_eq, h_eq_f]
    exact hTstar x (by linarith [le_max_left Tstar (max T₁ 1)]);
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ Set.Icc 1 Tstar, |iteratedDerivWithin k g (Set.Ici 1) x| ≤ M := by
    have h_cont : ContinuousOn (fun x => iteratedDerivWithin k g (Set.Ici 1) x) (Set.Icc 1 Tstar) := by
      refine' hcd.continuousOn_iteratedDerivWithin _ _ |> ContinuousOn.mono <| Set.Icc_subset_Ici_self;
      · norm_num;
      · exact uniqueDiffOn_Ici _;
    exact IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc ) h_cont;
  -- Choose $\beta = k - s > 0$.
  use max (|L| + 1) (M * Tstar ^ ((k : ℝ) - s)), (k : ℝ) - s;
  refine' ⟨ by linarith, fun x hx => _ ⟩;
  by_cases hx' : x ≤ Tstar;
  · refine' le_trans ( hM x ⟨ hx, hx' ⟩ ) _;
    rw [ Real.rpow_neg ( by linarith ) ];
    rw [ ← div_eq_mul_inv, le_div_iff₀ ( by positivity ) ];
    exact le_max_of_le_right ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow ( by linarith ) hx' ( by linarith ) ) ( show 0 ≤ M by exact le_trans ( abs_nonneg _ ) ( hM 1 ⟨ by norm_num, by linarith ⟩ ) ) );
  · exact le_trans ( hTstar.2 x ( le_of_not_ge hx' ) ) ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( Real.rpow_nonneg ( by linarith ) _ ) ) |> le_trans <| by ring_nf; norm_num;

/-- **Reduced analytic core.**  Proved from `real_branches_on_tail` by extending each
branch from its tail `[T₀,∞)` down to `[1,∞)` with `extend_to_Ici_one`, then raising the
common integer threshold above all the (finitely many) per-branch matching points. -/
lemma real_branches_sign_deriv_pos
    (P : Polynomial (Polynomial ℤ))
    (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree)
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) :
    ∃ (n k₀ : ℕ),
      2 ≤ k₀ ∧
      ∀ k, k₀ ≤ k → ∃ (T₀ : ℤ) (g : Fin n → ℝ → ℝ),
        1 ≤ T₀ ∧
        (∀ j,
          ContDiffOn ℝ (k + 1) (g j) (Set.Ici (1 : ℝ)) ∧
          ((∀ x ∈ Set.Ioi (1 : ℝ), 0 < iteratedDerivWithin (k + 1) (g j) (Set.Ici 1) x) ∨
            (∀ x ∈ Set.Ioi (1 : ℝ), iteratedDerivWithin (k + 1) (g j) (Set.Ici 1) x < 0)) ∧
          Filter.Tendsto (iteratedDerivWithin k (g j) (Set.Ici 1)) Filter.atTop (nhds 0) ∧
          HasKDerivDecay (g j) k) ∧
        (∀ t : ℤ, T₀ ≤ t → ∀ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y →
            ∃ j, g j (t : ℝ) = (y : ℝ)) := by
  obtain ⟨n, k₀, hk₀, htail⟩ := real_branches_on_tail P hP_monic hP_deg hP_no_root
  refine ⟨n, k₀, hk₀, ?_⟩
  intro k hk
  obtain ⟨T₀, f, hT₀, hpack, hcov⟩ := htail k hk
  have hk2 : 2 ≤ k := le_trans hk₀ hk
  have hT₀R : (1 : ℝ) ≤ (T₀ : ℝ) := by exact_mod_cast hT₀
  have hext : ∀ j, ∃ (T₁ : ℝ) (g : ℝ → ℝ), (T₀ : ℝ) ≤ T₁ ∧
      ContDiffOn ℝ (k + 1) g (Set.Ici (1 : ℝ)) ∧
      ((∀ x ∈ Set.Ioi (1 : ℝ), 0 < iteratedDerivWithin (k + 1) g (Set.Ici 1) x) ∨
        (∀ x ∈ Set.Ioi (1 : ℝ), iteratedDerivWithin (k + 1) g (Set.Ici 1) x < 0)) ∧
      Filter.Tendsto (iteratedDerivWithin k g (Set.Ici 1)) Filter.atTop (nhds 0) ∧
      (∀ x, T₁ ≤ x → g x = f j x) := by
    intro j
    obtain ⟨hcd, hsign, htend, _⟩ := hpack j
    exact extend_to_Ici_one (f j) k hk2 (T₀ : ℝ) hT₀R hcd hsign htend
  choose T₁ g _hT₁ hcd hsign htend hagree using hext
  obtain ⟨M, hM⟩ := Finite.exists_le T₁
  set N : ℤ := max T₀ ⌈M⌉
  have hT₀N : T₀ ≤ N := le_max_left _ _
  have hNR : ∀ j, T₁ j ≤ (N : ℝ) := by
    intro j
    have h1 : T₁ j ≤ M := hM j
    have h2 : M ≤ (⌈M⌉ : ℝ) := Int.le_ceil M
    have h3 : (⌈M⌉ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_right T₀ ⌈M⌉
    linarith
  have hbranch_rate : ∀ j, HasKDerivDecay (g j) k := by
    -- Genuine Puiseux content: a real algebraic branch `g j ~ c·x^s` at infinity has
    -- `k`-th derivative `~ c'·x^{s-k}`, so `|g_j⁽ᵏ⁾(x)| ≤ C₀·x^{-(k-s)}` with `k - s > 0`.
    -- This power-decay is now derived from the leading asymptotic ratio threaded through
    -- `real_branches_on_tail`, via `hasKDerivDecay_of_agree_ratio`.
    intro j
    obtain ⟨-, -, -, sj, Lj, hsj, hratio⟩ := hpack j
    exact hasKDerivDecay_of_agree_ratio (g j) (f j) k sj Lj (T₁ j) hsj (hcd j)
      (hagree j) hratio
  refine ⟨N, g, le_trans hT₀ hT₀N, fun j => ⟨hcd j, hsign j, htend j, hbranch_rate j⟩, ?_⟩
  intro t htN y hy
  obtain ⟨j, hj⟩ := hcov t (le_trans hT₀N htN) y hy
  refine ⟨j, ?_⟩
  have htR : (N : ℝ) ≤ (t : ℝ) := by exact_mod_cast htN
  rw [hagree j (t : ℝ) (le_trans (hNR j) htR), hj]

/-- **Full `+∞` branch package (assembled glue).**

Upgrades `real_branches_sign_deriv_pos` to the strictly-monotone-decaying `k`-th
derivative package (for every `k ≥ k₀`, with the per-`k` threshold and branch family)
via `analytic_package_of_kSucc_deriv`. -/
lemma branch_data_pos
    (P : Polynomial (Polynomial ℤ))
    (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree)
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) :
    ∃ (n k₀ : ℕ),
      2 ≤ k₀ ∧
      ∀ k, k₀ ≤ k → ∃ (T₀ : ℤ) (g : Fin n → ℝ → ℝ),
        1 ≤ T₀ ∧
        (∀ j, ContDiffOn ℝ k (g j) (Set.Ici (1 : ℝ))) ∧
        (∀ j, StrictMonoOn (iteratedDerivWithin k (g j) (Set.Ici 1)) (Set.Ici 1) ∨
            StrictAntiOn (iteratedDerivWithin k (g j) (Set.Ici 1)) (Set.Ici 1)) ∧
        (∀ j, HasKDerivDecay (g j) k) ∧
        (∀ t : ℤ, T₀ ≤ t → ∀ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y →
            ∃ j, g j (t : ℝ) = (y : ℝ)) := by
  obtain ⟨n, k₀, hk₀, hcore⟩ :=
    real_branches_sign_deriv_pos P hP_monic hP_deg hP_no_root
  refine ⟨n, k₀, hk₀, ?_⟩
  intro k hk
  obtain ⟨T₀, g, hT₀, hpack, hcov⟩ := hcore k hk
  have hk2 : 2 ≤ k := le_trans hk₀ hk
  refine ⟨T₀, g, hT₀, fun j => ?_, fun j => ?_, fun j => ?_, hcov⟩
  · obtain ⟨hcd, hsign, htend, _⟩ := hpack j
    exact (analytic_package_of_kSucc_deriv (g j) k hk2 hcd hsign htend).1
  · obtain ⟨hcd, hsign, htend, _⟩ := hpack j
    exact (analytic_package_of_kSucc_deriv (g j) k hk2 hcd hsign htend).2.1
  · obtain ⟨hcd, hsign, htend, hrate⟩ := hpack j
    exact hrate

/-- **Existence of the real algebraic branches at infinity (deep analytic input).** -/
lemma large_root_branch_data
    (P : Polynomial (Polynomial ℤ))
    (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree)
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) :
    ∃ (n k : ℕ) (T₀ : ℤ) (g h : Fin n → ℝ → ℝ),
      2 ≤ k ∧ 1 ≤ T₀ ∧
      (∀ j, ContDiffOn ℝ k (g j) (Set.Ici (1 : ℝ))) ∧
      (∀ j, StrictMonoOn (iteratedDerivWithin k (g j) (Set.Ici 1)) (Set.Ici 1) ∨
          StrictAntiOn (iteratedDerivWithin k (g j) (Set.Ici 1)) (Set.Ici 1)) ∧
      (∀ j, HasKDerivDecay (g j) k) ∧
      (∀ j, ContDiffOn ℝ k (h j) (Set.Ici (1 : ℝ))) ∧
      (∀ j, StrictMonoOn (iteratedDerivWithin k (h j) (Set.Ici 1)) (Set.Ici 1) ∨
          StrictAntiOn (iteratedDerivWithin k (h j) (Set.Ici 1)) (Set.Ici 1)) ∧
      (∀ j, HasKDerivDecay (h j) k) ∧
      (∀ t : ℤ, T₀ ≤ t → ∀ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y →
          ∃ j, g j (t : ℝ) = (y : ℝ)) ∧
      (∀ t : ℤ, t ≤ -T₀ → ∀ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y →
          ∃ j, h j (-(t : ℝ)) = (y : ℝ)) := by
  -- `+∞` branches of `P` (the `g`'s) and of `reflectT P` (the `h`'s).
  obtain ⟨n1, k1, hk1, hgcore⟩ :=
    branch_data_pos P hP_monic hP_deg hP_no_root
  obtain ⟨n2, k2, hk2, hhcore⟩ :=
    branch_data_pos (reflectT P) (reflectT_monic hP_monic)
      (by rw [reflectT_natDegree]; exact hP_deg) (reflectT_no_root hP_no_root)
  -- Common derivative order; instantiate both families at it.
  have hkmax : 2 ≤ max k1 k2 := le_trans hk1 (le_max_left _ _)
  obtain ⟨T1, g, hT1, hg_cd, hg_mono, hg_rate, hgcov⟩ := hgcore (max k1 k2) (le_max_left _ _)
  obtain ⟨T2, h0, hT2, hh_cd, hh_mono, hh_rate, hhcov⟩ := hhcore (max k1 k2) (le_max_right _ _)
  -- Common threshold, padded family size.
  refine ⟨n1 + n2, max k1 k2, max T1 T2,
    Fin.append g (fun _ => dummyBranch),
    Fin.append (fun _ : Fin n1 => dummyBranch) h0,
    hkmax, le_trans hT1 (le_max_left _ _), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `g`-family: smoothness
    intro J
    refine Fin.addCases (fun j => ?_) (fun j => ?_) J
    · rw [Fin.append_left]; exact hg_cd j
    · rw [Fin.append_right]; exact (dummyBranch_package _ hkmax).1
  · -- `g`-family: monotone/antitone `k`-th derivative
    intro J
    refine Fin.addCases (fun j => ?_) (fun j => ?_) J
    · rw [Fin.append_left]; exact hg_mono j
    · rw [Fin.append_right]; exact (dummyBranch_package _ hkmax).2.1
  · -- `g`-family: `k`-th derivative decay rate
    intro J
    refine Fin.addCases (fun j => ?_) (fun j => ?_) J
    · rw [Fin.append_left]; exact hg_rate j
    · rw [Fin.append_right]; exact (dummyBranch_package _ hkmax).2.2.2
  · -- `h`-family: smoothness
    intro J
    refine Fin.addCases (fun j => ?_) (fun j => ?_) J
    · rw [Fin.append_left]; exact (dummyBranch_package _ hkmax).1
    · rw [Fin.append_right]; exact hh_cd j
  · -- `h`-family: monotone/antitone `k`-th derivative
    intro J
    refine Fin.addCases (fun j => ?_) (fun j => ?_) J
    · rw [Fin.append_left]; exact (dummyBranch_package _ hkmax).2.1
    · rw [Fin.append_right]; exact hh_mono j
  · -- `h`-family: `k`-th derivative decay rate
    intro J
    refine Fin.addCases (fun j => ?_) (fun j => ?_) J
    · rw [Fin.append_left]; exact (dummyBranch_package _ hkmax).2.2.2
    · rw [Fin.append_right]; exact hh_rate j
  · -- positive-`t` covering: use the `g`-branches
    intro t ht y hy
    obtain ⟨j, hj⟩ := hgcov t (le_trans (le_max_left _ _) ht) y hy
    exact ⟨Fin.castAdd n2 j, by rw [Fin.append_left]; exact hj⟩
  · -- negative-`t` covering: use the `h`-branches of `reflectT P`
    intro t ht y hy
    have hs : ((reflectT P).map (Polynomial.evalRingHom (-t))).IsRoot y := by
      have h := reflectT_evalRingHom P (-t)
      rw [neg_neg] at h
      rw [Polynomial.IsRoot, h]; exact hy
    have hts : T2 ≤ -t := le_trans (le_max_right _ _) (by linarith [ht] : max T1 T2 ≤ -t)
    obtain ⟨j, hj⟩ := hhcov (-t) hts y hs
    refine ⟨Fin.natAdd n1 j, ?_⟩
    rw [Fin.append_right]
    have : ((-t : ℤ) : ℝ) = -(t : ℝ) := by push_cast; ring
    rw [this] at hj; exact hj

/-
**Finite branch cover of the large-root locus (analytic core, assembled).**

For `P ∈ ℤ[T][Y]` monic in `Y` of `Y`-degree `n ≥ 2` with no root in `ℚ(T)`, the
large-root locus `{t ∈ [-N, N] : ∃ y ∈ ℤ, N < y² ∧ P(t, y) = 0}` is covered, for every
`N`, by finitely many per-branch loci `T 0 N, …`, each of which is finite and grows
sublinearly. -/
lemma int_root_locus_large_cover
    (P : Polynomial (Polynomial ℤ))
    (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree)
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) :
    ∃ (n : ℕ) (T : Fin n → ℕ → Set ℤ),
      (∀ N : ℕ,
        ({t : ℤ | ∃ y : ℤ, (N : ℤ) < y ^ 2 ∧ (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩
          Set.Icc (-(N : ℤ)) (N : ℤ)) ⊆ ⋃ j, T j N) ∧
      (∀ (j : Fin n) (N : ℕ), (T j N).Finite) ∧
      (∀ j : Fin n, ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
          (Set.ncard (T j N) : ℝ) ≤ C * (N : ℝ) ^ α) := by
  obtain ⟨ n, k, T₀, g, h, hk, hT₀, hg_cd, hg_mono, hg_rate, hh_cd, hh_mono, hh_rate, hcov_pos, hcov_neg ⟩ := large_root_branch_data P hP_monic hP_deg hP_no_root;
  obtain ⟨hAfin, hAsub⟩ := pos_branches_cover_sublinear n k hk g hg_cd hg_mono hg_rate
  obtain ⟨hBfin, hBsub⟩ := neg_branches_cover_sublinear n k hk h hh_cd hh_mono hh_rate
  set S : ℕ → Set ℤ := fun N => {t : ℤ | ∃ y : ℤ, (N : ℤ) < y ^ 2 ∧ (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩ Set.Icc (-(N : ℤ)) (N : ℤ)
  set A : ℕ → Set ℤ := fun N => posBranchesUnion n g N
  set B : ℕ → Set ℤ := fun N => negBranchesUnion n h N
  set D : ℕ → Set ℤ := fun N => S N ∩ Set.Icc (-(T₀ - 1 : ℤ)) (T₀ - 1 : ℤ);
  have hDfin : ∀ N, (D N).Finite := by
    exact fun N => Set.Finite.subset ( Set.finite_Icc _ _ ) fun x hx => hx.2
  have hDsub : ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
    (Set.ncard (D N) : ℝ) ≤ C * (N : ℝ) ^ α := by
      apply ncard_inter_Icc_sublinear (-(T₀ - 1)) (T₀ - 1) D (fun N => Set.inter_subset_right)
  have hcov : ∀ N, S N ⊆ A N ∪ B N ∪ D N := by
    intro N t ht; rcases ht with ⟨ ⟨ y, hy₁, hy₂ ⟩, ht₁, ht₂ ⟩ ; by_cases h : t ≤ -T₀ <;> by_cases h' : t ≥ T₀ <;> simp_all [ Set.subset_def ] ;
    · linarith;
    · exact Or.inl <| Or.inr <| Set.mem_iUnion.mpr <| by obtain ⟨ j, hj ⟩ := hcov_neg t h y hy₂; exact ⟨ j, Set.mem_setOf.mpr ⟨ by linarith [ show ( 1 : ℝ ) ≤ -t by exact_mod_cast by linarith ], by linarith [ show ( -t : ℝ ) ≤ N by exact_mod_cast by linarith ], ⟨ y, hj ⟩ ⟩ ⟩ ;
    · obtain ⟨ j, hj ⟩ := hcov_pos t h' y hy₂; exact Or.inl <| Or.inl <| Set.mem_iUnion.mpr ⟨ j, ⟨ by norm_cast; linarith, by norm_cast, ⟨ y, hj ⟩ ⟩ ⟩ ;
    · exact Or.inr ⟨ ⟨ ⟨ y, hy₁, hy₂ ⟩, ht₁, ht₂ ⟩, ⟨ by linarith, by linarith ⟩ ⟩;
  exact three_cover S A B D hcov hAfin hBfin hDfin hAsub hBsub hDsub

/-- **Large-root part (the analytic core).** For `P ∈ ℤ[T][Y]` monic in `Y` of `Y`-degree
`≥ 2` with no root in `ℚ(T)`, the number of integers `t ∈ [-N, N]` for which `P(t, Y)` has
an *integer* root `y` with `y² > N` (equivalently `|y| > √N`, the "large" roots) is
`O(N^α)` for some `α < 1`. -/
lemma int_root_locus_large_sublinear
    (P : Polynomial (Polynomial ℤ))
    (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree)
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) :
    ∃ (C : ℝ) (α : ℝ), 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard ({t : ℤ | ∃ y : ℤ, (N : ℤ) < y ^ 2 ∧
          (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩
        Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) ≤ C * (N : ℝ) ^ α := by
  -- Assemble the per-branch sublinear estimates supplied by the finite branch cover.
  obtain ⟨n, T, hcover, hTfin, hsub⟩ :=
    int_root_locus_large_cover P hP_monic hP_deg hP_no_root
  exact sublinear_finite_cover
    (fun N => {t : ℤ | ∃ y : ℤ, (N : ℤ) < y ^ 2 ∧
        (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩ Set.Icc (-(N : ℤ)) (N : ℤ))
    T hcover hTfin hsub

/-- **Sparsity of integer points on a curve (the elementary analytic core).**

For an integer polynomial `P ∈ ℤ[T][Y]` monic in `Y` of `Y`-degree `≥ 2` that has *no
root* in the rational function field `ℚ(T) = Frac(ℚ[T])`, the set of integers `t` for which
the specialization `P(t, Y)` has an *integer* root grows sublinearly in `[-N, N]`:
there are constants `C > 0` and `0 ≤ α < 1` with
`#{t ∈ [-N, N] : ∃ y ∈ ℤ, P(t, y) = 0} ≤ C · N^α`.

The proof splits the integer roots by size: the *small* roots (`y² ≤ N`) are handled by the
elementary `int_root_locus_small_sublinear` (`O(N^{1/2})`), and the *large* roots (`y² > N`)
by `int_root_locus_large_sublinear`, the substantial analytic input behind the Dörge (1927)
proof of Hilbert's Irreducibility Theorem. See Serre, *Topics in Galois Theory*, Ch. 3. -/
lemma int_root_locus_sublinear
    (P : Polynomial (Polynomial ℤ))
    (hP_monic : P.Monic) (hP_deg : 2 ≤ P.natDegree)
    (hP_no_root : ∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) :
    ∃ (C : ℝ) (α : ℝ), 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard ({t : ℤ | ∃ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩
        Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) ≤ C * (N : ℝ) ^ α := by
  obtain ⟨Cs, hCs, hsmall⟩ := int_root_locus_small_sublinear P hP_no_root
  obtain ⟨Cl, αl, hCl, hαl, hαl', hlarge⟩ :=
    int_root_locus_large_sublinear P hP_monic hP_deg hP_no_root
  refine ⟨Cs + Cl, max (1/2) αl, by positivity, le_trans (by norm_num) (le_max_left _ _),
    max_lt (by norm_num) hαl', ?_⟩
  intro N hN
  set A := {t : ℤ | ∃ y : ℤ, y ^ 2 ≤ (N : ℤ) ∧ (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩
      Set.Icc (-(N : ℤ)) (N : ℤ) with hA
  set B := {t : ℤ | ∃ y : ℤ, (N : ℤ) < y ^ 2 ∧ (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩
      Set.Icc (-(N : ℤ)) (N : ℤ) with hB
  have hsub : ({t : ℤ | ∃ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩
      Set.Icc (-(N : ℤ)) (N : ℤ)) ⊆ A ∪ B := by
    rintro t ⟨⟨y, hy⟩, ht⟩
    rcases le_or_gt (y ^ 2) (N : ℤ) with h | h
    · exact Or.inl ⟨⟨y, h, hy⟩, ht⟩
    · exact Or.inr ⟨⟨y, h, hy⟩, ht⟩
  have hAfin : A.Finite := (Set.finite_Icc _ _).inter_of_right _
  have hBfin : B.Finite := (Set.finite_Icc _ _).inter_of_right _
  have hcard : (Set.ncard ({t : ℤ | ∃ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩
      Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) ≤ (A.ncard : ℝ) + (B.ncard : ℝ) := by
    have h1 : Set.ncard ({t : ℤ | ∃ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩
        Set.Icc (-(N : ℤ)) (N : ℤ)) ≤ (A ∪ B).ncard :=
      Set.ncard_le_ncard hsub (hAfin.union hBfin)
    have h2 : (A ∪ B).ncard ≤ A.ncard + B.ncard := Set.ncard_union_le A B
    exact_mod_cast le_trans h1 h2
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  calc (Set.ncard ({t : ℤ | ∃ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩
        Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ)
      ≤ (A.ncard : ℝ) + (B.ncard : ℝ) := hcard
    _ ≤ Cs * (N:ℝ) ^ (1/2:ℝ) + Cl * (N:ℝ) ^ αl := add_le_add (hsmall N hN) (hlarge N hN)
    _ ≤ Cs * (N:ℝ) ^ (max (1/2) αl) + Cl * (N:ℝ) ^ (max (1/2) αl) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)) hCs.le
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)) hCl.le
    _ = (Cs + Cl) * (N:ℝ) ^ (max (1/2) αl) := by ring

set_option maxHeartbeats 1600000 in
/-- **Resolvent construction.**

For `F ∈ ℤ[T][X]` monic in `X`, irreducible (hence irreducible over `ℚ(T)`) and absolutely
irreducible, of degree `d ≥ 2` in `X`, and `1 ≤ k < d`, there is an integer polynomial
`P ∈ ℤ[T][Y]` (a `k`-subset resolvent) with the following properties:

* `P` is monic in `Y` and has `Y`-degree `≥ 2` (in fact a divisor of `C(d, k)`);
* `P` has no root in `ℚ(T)`;
* whenever `F(t, X)` has a monic degree-`k` factor `g ∈ ℤ[X]`, the polynomial `P(t, Y)`
  has *some* integer root `y`.

Thus the reducible locus of `F` embeds into the integer-root locus of the resolvent `P`,
and `int_root_locus_sublinear` applies. -/

/-
Gauss's lemma for `ℤ[T] → ℚ(T)`: a monic irreducible `F ∈ ℤ[T][X]` stays irreducible as
a polynomial over the rational function field `ℚ(T) = Frac(ℚ[T])`.
-/
lemma FmapToRatFunc_irreducible
    (F : Polynomial (Polynomial ℤ))
    (hF_monic : F.Monic) (hF_irr : Irreducible F) :
    Irreducible (F.map toRatFunc) := by
  -- Let $fQ := F.map (mapRingHom (Int.castRingHom ℚ)) : (Polynomial ℚ)[X]$.
  set fQ : Polynomial (Polynomial ℚ) := F.map (mapRingHom (Int.castRingHom ℚ));
  -- By Gauss's lemma, $fQ$ is irreducible over $\mathbb{Q}[T]$.
  have hfQ_irr : Irreducible fQ := by
    -- By `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` (ℤ[T] is integrally closed), F is irreducible iff F.map (algebraMap ℤ[T] (FractionRing ℤ[T])) is irreducible.
    have hF_irr_iff_fQ_irr : Irreducible F ↔ Irreducible (F.map (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)))) := by
      apply Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map; assumption;
    have h_iso : ∃ (φ : FractionRing (Polynomial ℤ) ≃+* FractionRing (Polynomial ℚ)), ∀ x : Polynomial ℤ, φ (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)) x) = algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) (Polynomial.map (Int.castRingHom ℚ) x) := by
      have h_iso : ∃ (φ : FractionRing (Polynomial ℤ) →+* FractionRing (Polynomial ℚ)), ∀ x : Polynomial ℤ, φ (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)) x) = algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) (Polynomial.map (Int.castRingHom ℚ) x) := by
        have h_iso : ∃ (φ : Polynomial ℤ →+* FractionRing (Polynomial ℚ)), ∀ x : Polynomial ℤ, φ x = algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) (Polynomial.map (Int.castRingHom ℚ) x) := by
          exact ⟨ RingHom.comp ( algebraMap ( Polynomial ℚ ) ( FractionRing ( Polynomial ℚ ) ) ) ( Polynomial.mapRingHom ( Int.castRingHom ℚ ) ), fun x => rfl ⟩;
        obtain ⟨φ, hφ⟩ := h_iso;
        have h_iso : ∃ (φ' : FractionRing (Polynomial ℤ) →+* FractionRing (Polynomial ℚ)), ∀ x : Polynomial ℤ, φ' (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)) x) = φ x := by
          have h_iso : ∀ x : Polynomial ℤ, x ≠ 0 → φ x ≠ 0 := by
            simp_all [ Polynomial.ext_iff ];
          exact ⟨ IsFractionRing.lift ( show Function.Injective φ from fun x y hxy => Classical.not_not.1 fun h => h_iso ( x - y ) ( sub_ne_zero_of_ne h ) <| by simpa [ sub_eq_zero ] using hxy ), fun x => by simp ⟩;
        aesop;
      obtain ⟨φ, hφ⟩ := h_iso
      have h_iso_bijective : Function.Bijective φ := by
        have h_iso_bijective : Function.Surjective φ := by
          intro x;
          obtain ⟨ p, q, hq, rfl ⟩ := IsLocalization.mk'_surjective ( nonZeroDivisors ( Polynomial ℚ ) ) x;
          -- Let $d$ be the least common multiple of the denominators of the coefficients of $p$ and $q$.
          obtain ⟨d, hd⟩ : ∃ d : ℕ, d > 0 ∧ ∀ i ∈ p.1.support ∪ p.2.val.support, (d * p.1.coeff i : ℚ) ∈ Set.range (Int.cast : ℤ → ℚ) ∧ (d * p.2.val.coeff i : ℚ) ∈ Set.range (Int.cast : ℤ → ℚ) := by
            -- Let $d$ be the least common multiple of the denominators of the coefficients of $p$ and $q$. Since $p$ and $q$ are polynomials with rational coefficients, such a $d$ exists.
            have hd_exists : ∀ i ∈ p.1.support ∪ p.2.val.support, ∃ d : ℕ, d > 0 ∧ (d * p.1.coeff i : ℚ) ∈ Set.range (Int.cast : ℤ → ℚ) ∧ (d * p.2.val.coeff i : ℚ) ∈ Set.range (Int.cast : ℤ → ℚ) := by
              intro i hi
              obtain ⟨d1, hd1⟩ : ∃ d1 : ℕ, d1 > 0 ∧ (d1 * p.1.coeff i : ℚ) ∈ Set.range (Int.cast : ℤ → ℚ) := by
                exact ⟨ p.1.coeff i |> Rat.den, Nat.cast_pos.mpr ( Rat.pos _ ), ⟨ p.1.coeff i |> Rat.num, by simp [ Rat.cast_def, mul_comm, mul_left_comm, mul_assoc ] ⟩ ⟩
              obtain ⟨d2, hd2⟩ : ∃ d2 : ℕ, d2 > 0 ∧ (d2 * p.2.val.coeff i : ℚ) ∈ Set.range (Int.cast : ℤ → ℚ) := by
                exact ⟨ p.2.val.coeff i |> Rat.den, Nat.cast_pos.mpr ( Rat.pos _ ), ⟨ p.2.val.coeff i |> Rat.num, by simp [ Rat.cast_def, mul_comm, mul_left_comm, mul_assoc ] ⟩ ⟩
              use d1 * d2
              simp [hd1, hd2];
              exact ⟨ by obtain ⟨ y, hy ⟩ := hd1.2; exact ⟨ y * d2, by push_cast; linear_combination' hy * d2 ⟩, by obtain ⟨ y, hy ⟩ := hd2.2; exact ⟨ y * d1, by push_cast; linear_combination' hy * d1 ⟩ ⟩;
            choose! d hd using hd_exists;
            use ∏ i ∈ p.1.support ∪ p.2.val.support, d i;
            simp_all [ Finset.prod_eq_zero_iff, ne_of_gt ];
            intro i hi; specialize hd i hi; simp_all [ Finset.prod_eq_prod_diff_singleton_mul ( show i ∈ p.1.support ∪ ( p.2 : Polynomial ℚ ).support from by aesop ) ] ;
            exact ⟨ by obtain ⟨ y, hy ⟩ := hd.2.1; exact ⟨ y * ∏ i ∈ ( p.1.support ∪ ( p.2 : Polynomial ℚ ).support ) \ { i }, d i, by push_cast; rw [ hy ] ; ring ⟩, by obtain ⟨ y, hy ⟩ := hd.2.2; exact ⟨ y * ∏ i ∈ ( p.1.support ∪ ( p.2 : Polynomial ℚ ).support ) \ { i }, d i, by push_cast; rw [ hy ] ; ring ⟩ ⟩;
          -- Let $p'$ and $q'$ be the polynomials with integer coefficients obtained by multiplying $p$ and $q$ by $d$.
          obtain ⟨p', hp'⟩ : ∃ p' : Polynomial ℤ, Polynomial.map (Int.castRingHom ℚ) p' = Polynomial.C (d : ℚ) * p.1 := by
            choose! f hf using fun i hi => hd.2 i hi |>.1;
            use ∑ i ∈ p.1.support, f i • Polynomial.X ^ i; ext i; by_cases hi : i ∈ p.1.support <;> simp_all [ Polynomial.coeff_sum, Polynomial.coeff_C_mul ] ;
          obtain ⟨q', hq'⟩ : ∃ q' : Polynomial ℤ, Polynomial.map (Int.castRingHom ℚ) q' = Polynomial.C (d : ℚ) * p.2.val := by
            choose! f hf using fun i hi => hd.2 i hi |>.2;
            use ∑ i ∈ p.2.val.support, f i • Polynomial.X ^ i; ext i; simp [ Polynomial.coeff_sum, Polynomial.coeff_C_mul ] ; aesop;
          use algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)) p' * (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)) q')⁻¹;
          simp_all [ mul_assoc, mul_comm, mul_left_comm ];
          rw [ ← mul_assoc, mul_inv_cancel₀ ( by norm_cast; linarith ), one_mul, div_eq_mul_inv ];
        exact ⟨ RingHom.injective φ, h_iso_bijective ⟩
      exact ⟨RingEquiv.ofBijective φ h_iso_bijective, hφ⟩;
    obtain ⟨φ, hφ⟩ := h_iso
    have h_iso_map : Irreducible (F.map (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)))) ↔ Irreducible (F.map (mapRingHom (Int.castRingHom ℚ)) |> Polynomial.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))) := by
      have h_iso_map : ∀ p : Polynomial (FractionRing (Polynomial ℤ)), Irreducible p ↔ Irreducible (p.map (φ : FractionRing (Polynomial ℤ) →+* FractionRing (Polynomial ℚ))) := by
        intro p; exact ⟨fun hp => by
          constructor;
          · intro h; have := hp.1; simp_all [ Polynomial.isUnit_iff_degree_eq_zero ] ;
          · intro a b hab
            have h_iso : p = (a.map (φ.symm : FractionRing (Polynomial ℚ) →+* FractionRing (Polynomial ℤ))) * (b.map (φ.symm : FractionRing (Polynomial ℚ) →+* FractionRing (Polynomial ℤ))) := by
              convert congr_arg ( Polynomial.map ( φ.symm : FractionRing ( Polynomial ℚ ) →+* FractionRing ( Polynomial ℤ ) ) ) hab using 1 ; simp [ Polynomial.map_map ];
              rw [ Polynomial.map_mul ];
            have := hp.2 h_iso; simp_all [ Polynomial.isUnit_iff_degree_eq_zero ] ;, fun hp => by
          rw [ irreducible_iff ] at *;
          simp_all [ Polynomial.isUnit_iff_degree_eq_zero ];
          intro a b hab; specialize hp; have := hp.2 ( show map ( φ : FractionRing ℤ[X] →+* FractionRing ℚ[X] ) p = map ( φ : FractionRing ℤ[X] →+* FractionRing ℚ[X] ) a * map ( φ : FractionRing ℤ[X] →+* FractionRing ℚ[X] ) b from by rw [ ← Polynomial.map_mul, ← hab ] ) ; aesop;⟩;
      convert h_iso_map _ using 2;
      ext; simp [ hφ ] ;
    have h_iso_map : Irreducible (F.map (mapRingHom (Int.castRingHom ℚ)) |> Polynomial.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))) → Irreducible (F.map (mapRingHom (Int.castRingHom ℚ))) := by
      convert Polynomial.Monic.irreducible_of_irreducible_map ( algebraMap ( Polynomial ℚ ) ( FractionRing ( Polynomial ℚ ) ) ) _ _ using 1;
      exact hF_monic.map _;
    grind;
  -- By `irreducible_over_ratFunc`, $fQ.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))$ is irreducible.
  have hfQ_map_irr : Irreducible (fQ.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))) := by
    apply irreducible_over_ratFunc;
    · exact hF_monic.map _;
    · exact hfQ_irr;
  convert hfQ_map_irr using 1;
  rw [ Polynomial.map_map ] ; aesop;

lemma resolvent_exists
    (F : Polynomial (Polynomial ℤ))
    (hF_monic : F.Monic) (hF_irr : Irreducible F)
    (hF_abs_irr :
      Irreducible (F.map (mapRingHom (algebraMap ℤ (AlgebraicClosure ℚ)))))
    (k : ℕ) (hk : 1 ≤ k) (hk' : k < F.natDegree) :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ 2 ≤ P.natDegree ∧
      (∀ a : FractionRing (Polynomial ℚ), ¬ (P.map toRatFunc).IsRoot a) ∧
      (∀ t : ℤ, (∃ g : Polynomial ℤ, g.natDegree = k ∧ g.Monic ∧
        g ∣ (F.map (Polynomial.evalRingHom t))) →
        ∃ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y) := by
  classical
  -- Base field `K = ℚ(T)` and the polynomial `f = F` viewed over `K`.
  set K := FractionRing (Polynomial ℚ) with hK
  set f : Polynomial K := F.map toRatFunc with hf
  have hf_monic : f.Monic := hF_monic.map _
  have hFK_irr : Irreducible f := FmapToRatFunc_irreducible F hF_monic hF_irr
  -- `toRatFunc` is injective, so degrees are preserved.
  have htr_inj : Function.Injective (toRatFunc) := by
    unfold toRatFunc
    exact (FaithfulSMul.algebraMap_injective (Polynomial ℚ) K).comp
      (Polynomial.map_injective _ (Int.cast_injective))
  have hf_deg : f.natDegree = F.natDegree := by
    rw [hf]; exact natDegree_map_eq_of_injective htr_inj F
  -- Splitting field `L` of `f` over `K`.
  set L := f.SplittingField with hL
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have hsplitsL : (f.map (algebraMap K L)).Splits := SplittingField.splits f
  have hcardL : (f.map (algebraMap K L)).roots.card = f.natDegree := by
    have hspl : (f.map (algebraMap K L)).Splits := SplittingField.splits f
    exact (hspl.natDegree_eq_card_roots).symm.trans
      (natDegree_map_eq_of_injective (algebraMap K L).injective f)
  -- Genericity: choose the integer linear form `lam`.
  obtain ⟨lam, hlam⟩ :=
    exists_generic_lam f hFK_irr hf_monic hcardL k hk (hf_deg ▸ hk')
  -- The resolvent polynomial `P`.
  obtain ⟨P, hP_monic, hP_deg, hP_id⟩ := exists_resolvent_poly F hF_monic k lam
  refine ⟨P, hP_monic, ?_, ?_, ?_⟩
  · -- `2 ≤ P.natDegree`
    rw [hP_deg]; exact two_le_natDegree_choose hk hk'
  · -- No root in `ℚ(T)`.
    intro a haroot
    set evL : Polynomial ℤ →+* L := (algebraMap K L).comp toRatFunc with hevL
    have hmapL : F.map evL = f.map (algebraMap K L) := by
      rw [hevL, ← map_map, ← hf]
    have hdegL : (F.map evL).natDegree = F.natDegree := by
      rw [hmapL, natDegree_map_eq_of_injective (algebraMap K L).injective, hf_deg]
    have hcardL' : (F.map evL).roots.card = F.natDegree := by
      rw [hmapL, hcardL, hf_deg]
    have hPevL := hP_id evL hdegL hcardL'
    -- Push the root `a ∈ K` into `L`.
    have hroot_L : (P.map evL).IsRoot (algebraMap K L a) := by
      have hmapP : P.map evL = (P.map toRatFunc).map (algebraMap K L) := by
        rw [hevL, ← map_map]
      unfold Polynomial.IsRoot
      rw [hmapP, eval_map, eval₂_at_apply]
      simp only [← hf] at *
      rw [show (P.map toRatFunc).eval a = 0 from haroot, map_zero]
    rw [hPevL] at hroot_L
    obtain ⟨s, hs_mem, hs_eq⟩ := exists_mem_of_isRoot_resolventProduct k lam _ hroot_L
    rw [hmapL] at hs_mem
    exact hlam s hs_mem ⟨a, hs_eq.symm⟩
  · -- Specialization property: integer factor ⇒ integer root of the resolvent.
    rintro t ⟨g, hg_deg, hg_monic, hg_dvd⟩
    set evC : Polynomial ℤ →+* ℂ := (Int.castRingHom ℂ).comp (Polynomial.evalRingHom t) with hevC
    have hmapC : F.map evC = (F.map (Polynomial.evalRingHom t)).map (Int.castRingHom ℂ) := by
      rw [hevC, ← map_map]
    have hFt_monic : (F.map (Polynomial.evalRingHom t)).Monic := hF_monic.map _
    have hdegC : (F.map evC).natDegree = F.natDegree := by
      rw [hmapC, hFt_monic.natDegree_map, hF_monic.natDegree_map]
    have hsplitC : (F.map evC).Splits := by
      rw [← splits_id_iff_splits]
      exact IsAlgClosed.splits_codomain _
    have hcardC : (F.map evC).roots.card = F.natDegree := by
      exact (hsplitC.natDegree_eq_card_roots).symm.trans hdegC
    have hPevC := hP_id evC hdegC hcardC
    -- The image of `g` over `ℂ`.
    set gC : Polynomial ℂ := g.map (Int.castRingHom ℂ) with hgC
    have hgC_monic : gC.Monic := hg_monic.map _
    have hgC_dvd : gC ∣ F.map evC := by
      rw [hmapC]; exact Polynomial.map_dvd _ hg_dvd
    have hFmapC_ne : F.map evC ≠ 0 := by
      rw [hmapC]; exact (hFt_monic.map (Int.castRingHom ℂ)).ne_zero
    have hgC_card : gC.roots.card = k := by
      have hspl : gC.Splits := by
        have := hgC_dvd
        exact hsplitC.of_dvd hFmapC_ne this
      rw [(hspl.natDegree_eq_card_roots).symm, hgC, hg_monic.natDegree_map, hg_deg]
    have hgC_le : gC.roots ≤ (F.map evC).roots := Polynomial.roots.le_of_dvd hFmapC_ne hgC_dvd
    have hgC_mem : gC.roots ∈ (F.map evC).roots.powersetCard k :=
      Multiset.mem_powersetCard.mpr ⟨hgC_le, hgC_card⟩
    have hroot := isRoot_resolventProduct_of_mem k lam (F.map evC).roots hgC_mem
    rw [← hPevC] at hroot
    -- The resolvent value is an integer.
    have hg_card' : (g.map (Int.castRingHom ℂ)).roots.card = g.natDegree := by
      rw [← hgC, hgC_card, hg_deg]
    obtain ⟨y, hy⟩ :=
      wval_roots_map_mem_range (Int.castRingHom ℂ) g hg_monic hg_card' k lam
    refine ⟨y, ?_⟩
    -- Transfer the root back to `ℤ`.
    have hmapPC : P.map evC = (P.map (Polynomial.evalRingHom t)).map (Int.castRingHom ℂ) := by
      rw [hevC, ← map_map]
    have : ((P.map (Polynomial.evalRingHom t)).map (Int.castRingHom ℂ)).IsRoot (wval k lam gC.roots) := by
      rw [← hmapPC]; exact hroot
    unfold Polynomial.IsRoot at this ⊢
    rw [hgC, ← hy, eval_map, eval₂_at_apply] at this
    have h2 : ((eval y (map (evalRingHom t) P) : ℤ) : ℂ) = 0 := this
    exact_mod_cast h2

/--

For a monic polynomial `F ∈ ℤ[T][X]` that is irreducible (hence, by Gauss, irreducible
over `ℚ(T)`) of degree `d ≥ 2`, and `1 ≤ k < d`, the set of integers `t` for which the
specialization `F(t, X)` has a monic factor of degree `k` in `ℤ[X]` grows *sublinearly*
in `[-N, N]`: there are constants `C > 0` and `0 ≤ α < 1` with
`#{t ∈ [-N, N] : F(t, X) has a monic degree-k factor} ≤ C · N^α`.

This is the quantitative heart of Hilbert's Irreducibility Theorem. It is proved by the
classical **elementary** argument of Dörge (1927); see also Serre, *Topics in Galois
Theory*, Ch. 3. The argument uses only tools available around 1900 — root and
coefficient bounds together with the sparsity of integer points on an algebraic curve —
and in particular uses **no** reduction modulo `p` and no deep analytic number theory. -/
lemma int_factor_locus_sublinear
    (F : Polynomial (Polynomial ℤ))
    (hF_monic : F.Monic) (hF_irr : Irreducible F)
    (hF_abs_irr :
      Irreducible (F.map (mapRingHom (algebraMap ℤ (AlgebraicClosure ℚ)))))
    (k : ℕ) (hk : 1 ≤ k) (hk' : k < F.natDegree) :
    ∃ (C : ℝ) (α : ℝ), 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard ({t : ℤ | ∃ g : Polynomial ℤ, g.natDegree = k ∧ g.Monic ∧
        g ∣ (F.map (Polynomial.evalRingHom t))} ∩
        Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) ≤ C * (N : ℝ) ^ α := by
  -- Build the `k`-subset-sum resolvent `P` capturing the traces of degree-`k` factors.
  obtain ⟨P, hP_monic, hP_deg, hP_no_root, hP_trace⟩ :=
    resolvent_exists F hF_monic hF_irr hF_abs_irr k hk hk'
  -- Its integer-root locus is sublinear by the elementary analytic core.
  obtain ⟨C, α, hC, hα, hα', hbound⟩ :=
    int_root_locus_sublinear P hP_monic hP_deg hP_no_root
  refine ⟨C, α, hC, hα, hα', fun N hN => ?_⟩
  -- The reducible locus of `F` embeds into the integer-root locus of `P`.
  have hsub :
      ({t : ℤ | ∃ g : Polynomial ℤ, g.natDegree = k ∧ g.Monic ∧
          g ∣ (F.map (Polynomial.evalRingHom t))} ∩ Set.Icc (-(N : ℤ)) (N : ℤ))
        ⊆ ({t : ℤ | ∃ y : ℤ, (P.map (Polynomial.evalRingHom t)).IsRoot y} ∩
          Set.Icc (-(N : ℤ)) (N : ℤ)) := by
    rintro t ⟨htmem, htIcc⟩
    exact ⟨hP_trace t htmem, htIcc⟩
  refine le_trans ?_ (hbound N hN)
  exact_mod_cast Set.ncard_le_ncard hsub ((Set.finite_Icc _ _).inter_of_right _)

/-- **Dörge's density estimate** (the quantitative core of HIT).

Given a monic irreducible `f ∈ ℚ[T][X]` of degree `d ≥ 2` in `X`, absolutely irreducible
over `ℚ̄(T)`, and `1 ≤ k < d`, the set of integers `t` for which `f(t, X)` has a monic
factor of degree `k` over `ℚ` grows sublinearly in `[-N, N]`. -/
lemma dorge_density_estimate
    (f : Polynomial (Polynomial ℚ))
    (hf_irr : Irreducible f) (hf_monic : f.Monic)
    (hf_abs_irr :
      Irreducible (f.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))))
    (k : ℕ) (hk : 1 ≤ k) (hk' : k < f.natDegree) :
    ∃ (C : ℝ) (α : ℝ), 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard ({t : ℤ | ∃ g : Polynomial ℚ, g.natDegree = k ∧ g.Monic ∧
        g ∣ (f.map (Polynomial.evalRingHom (↑t : ℚ)))} ∩
        Set.Icc (-(N : ℤ)) (N : ℤ)) : ℝ) ≤ C * (N : ℝ) ^ α := by
  -- Pass to an integral model `F ∈ ℤ[T][X]` (Tschirnhaus scaling preserving absolute irr.).
  obtain ⟨F, hF_monic, hF_deg, hF_irr, hF_abs_irr, hF_factor⟩ :=
    integral_model_exists f hf_irr hf_monic hf_abs_irr
  have hf_deg2 : 2 ≤ f.natDegree := lt_of_le_of_lt hk hk'
  -- Apply the counting core to `F`.
  obtain ⟨C, α, hC, hα, hα', hbound⟩ :=
    int_factor_locus_sublinear F hF_monic hF_irr hF_abs_irr k hk (hF_deg ▸ hk')
  refine ⟨C, α, hC, hα, hα', fun N hN => ?_⟩
  -- The `ℚ`-reducible locus of `f` is contained in the `ℤ`-reducible locus of `F`.
  have hsub :
      ({t : ℤ | ∃ g : Polynomial ℚ, g.natDegree = k ∧ g.Monic ∧
          g ∣ (f.map (Polynomial.evalRingHom (↑t : ℚ)))} ∩ Set.Icc (-(N : ℤ)) (N : ℤ))
        ⊆ ({t : ℤ | ∃ g : Polynomial ℤ, g.natDegree = k ∧ g.Monic ∧
          g ∣ (F.map (Polynomial.evalRingHom t))} ∩ Set.Icc (-(N : ℤ)) (N : ℤ)) := by
    rintro t ⟨htmem, htIcc⟩
    exact ⟨hF_factor t k hk htmem, htIcc⟩
  refine le_trans ?_ (hbound N hN)
  exact_mod_cast Set.ncard_le_ncard hsub ((Set.finite_Icc _ _).inter_of_right _)


end
