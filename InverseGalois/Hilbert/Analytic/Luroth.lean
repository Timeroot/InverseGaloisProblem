import Mathlib

/-!
# Lüroth's theorem (work in progress)

Any intermediate field `M` strictly larger than the base field `k` inside the rational
function field `k(X)` is itself a rational function field `k(w)`.

We build this from scratch (it is not in Mathlib).  The overall structure follows the
classical proof of van der Waerden.
-/

open Polynomial IntermediateField

namespace RatFunc

variable {k : Type*} [Field k]

/-- The "height" of a rational function: the maximum of the degrees of its (coprime)
numerator and denominator.  This equals `[k(X) : k(θ)]` when `θ` is nonconstant. -/
noncomputable def height (θ : RatFunc k) : ℕ := max θ.num.natDegree θ.denom.natDegree

/-
An element of `k(X)` lies in the base subfield `k` (i.e. `⊥`) iff it is constant, i.e.
iff it equals `RatFunc.C c` for some `c`.
-/
theorem mem_bot_iff (θ : RatFunc k) :
    θ ∈ (⊥ : IntermediateField k (RatFunc k)) ↔ ∃ c : k, RatFunc.C c = θ := by
  exact Eq.to_iff rfl

/-
A rational function not lying in the base field `k` is transcendental over `k`.
-/
theorem transcendental_of_not_mem_bot (θ : RatFunc k)
    (h : θ ∉ (⊥ : IntermediateField k (RatFunc k))) : Transcendental k θ := by
  intro h_alg
  convert h_alg.isIntegral
  constructor <;> intro h <;> contrapose! h
  · trivial
  · intro h_int
    -- Since `k[X]` is integrally closed, any element of `k(X)` integral over `k` must lie in `k[X]`.
    have h_int_closed : ∀ {x : RatFunc k}, IsIntegral k x → ∃ p : Polynomial k, x = RatFunc.mk p 1 := by
      intro x hx_int
      have hx_int' : IsIntegral (Polynomial k) x := hx_int.tower_top
      obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx_int'
      refine ⟨p, hp.symm.trans ?_⟩
      simp [RatFunc.mk_eq_div]
    obtain ⟨p, rfl⟩ := h_int_closed h_int
    -- Since `p` is a polynomial in `k[X]`, it is algebraic over `k`.
    have h_p_alg : IsAlgebraic k p := by
      obtain ⟨q, hq⟩ := h_alg
      refine ⟨q, hq.1, ?_⟩
      convert hq.2 using 1
      simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
      rw [← (IsFractionRing.injective (Polynomial k) (RatFunc k)) |>.eq_iff]
      simp
    have h_deg_le : p.degree ≤ 0 := by
      obtain ⟨q, hq⟩ := h_p_alg
      have h_comp : q.comp p = 0 := by
        simpa [Polynomial.aeval_def] using hq.2
      rw [Polynomial.comp_eq_zero_iff] at h_comp
      rw [(h_comp.resolve_left hq.1).2]
      exact Polynomial.degree_C_le
    rw [Polynomial.eq_C_of_degree_le_zero h_deg_le] at h
    apply h
    rw [RatFunc.mk_one]
    exact Subalgebra.algebraMap_mem _ _

/-
`RatFunc.X` generates the whole field `k(X)` over `k`.
-/
theorem adjoin_X_top :
    IntermediateField.adjoin k {(RatFunc.X : RatFunc k)} = ⊤ := by
  -- We must show `k⟮RatFunc.X⟯ = ⊤` in `IntermediateField k (RatFunc k)`; equivalently the smallest subfield containing `k` and `RatFunc.X` is everything.
  ext z
  simp [IntermediateField.mem_adjoin_simple_iff]
  refine ⟨z.num, z.denom, ?_⟩
  simp [RatFunc.num_div_denom]

/-- `RatFunc.X` generates the whole field `k(X)` over any intermediate field `K`. -/
theorem adjoin_X_top' (K : IntermediateField k (RatFunc k)) :
    IntermediateField.adjoin K {(RatFunc.X : RatFunc k)} = ⊤ := by
  have hk : IntermediateField.adjoin k {(RatFunc.X : RatFunc k)} = ⊤ := adjoin_X_top
  simp_all [IntermediateField.adjoin]
  simp_all [SetLike.ext_iff, Subfield.mem_closure]
  intro x S hS
  specialize hk x S
  simp_all [Set.insert_subset_iff, Set.range_subset_iff]
  apply hk
  intro y
  simpa using S.mul_mem (hS.2 _ <| IntermediateField.algebraMap_mem _ y) (S.one_mem)

/-
A degree-one polynomial `C a * X + C b` over a GCD domain with coprime coefficients
(and nonzero leading coefficient) is irreducible.
-/
theorem linear_irreducible {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
    (a b : R) (ha : a ≠ 0) (hcop : IsCoprime a b) :
    Irreducible (Polynomial.C a * Polynomial.X + Polynomial.C b) := by
  obtain ⟨u, v, h⟩ := hcop
  constructor
  · intro h_unit
    have := Polynomial.degree_eq_zero_of_isUnit h_unit
    rw [Polynomial.degree_add_C] at this <;> simp_all [Polynomial.degree_C, Polynomial.degree_X]
  · intro p q hpq
    have h_deg : p.degree + q.degree = 1 := by
      rw [← Polynomial.degree_mul, ← hpq, Polynomial.degree_add_C] <;> simp [ha]
    -- Since the degree of `p` and `q` is 1, one of them must be a constant polynomial.
    have h_const : p.degree = 0 ∨ q.degree = 0 := by
      have hp0 : p ≠ 0 := fun h ↦ by simp [h] at h_deg
      have hq0 : q ≠ 0 := fun h ↦ by simp [h] at h_deg
      rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0] at *
      norm_cast at *
      omega
    rcases h_const with (h | h) <;>
      rw [Polynomial.eq_C_of_degree_eq_zero h] at hpq ⊢ <;> simp_all [Polynomial.ext_iff]
    · have := hpq 0
      have := hpq 1
      simp_all [Polynomial.coeff_C, Polynomial.coeff_X]
      refine Or.inl (isUnit_of_dvd_one ⟨u * q.coeff 1 + v * q.coeff 0, ?_⟩)
      linear_combination' ‹u * (p.coeff 0 * q.coeff 1) + v * (p.coeff 0 * q.coeff 0) = 1›.symm
    · have := hpq 0
      have := hpq 1
      simp_all [Polynomial.coeff_C, Polynomial.coeff_X]
      refine Or.inr (isUnit_of_dvd_one ⟨u * p.coeff 1 + v * p.coeff 0, ?_⟩)
      linear_combination' ‹u * (p.coeff 1 * q.coeff 0) + v * (p.coeff 0 * q.coeff 0) = 1›.symm

/-
The primitive trinomial `g(Y) - X*h(Y)` over the ring `k[X]` is irreducible. Here the
coefficients of `g, h` are lifted from `k` into `k[X]` (via `algebraMap k (k[X]) = C`), and
`X` is the base variable of `k[X]`.  Proved via the bivariate variable swap
(`Polynomial.Bivariate.swap`), which turns it into the linear polynomial
`C g - C h * X` handled by `linear_irreducible`.
-/
theorem auxPoly_R_irreducible (g h : k[X]) (hcop : IsCoprime g h)
    (hpos : 0 < max g.natDegree h.natDegree) :
    Irreducible ((g.map (algebraMap k (k[X])))
      - Polynomial.C (Polynomial.X : k[X]) * (h.map (algebraMap k (k[X])))) := by
  -- Let `P := map g - X * map h`. Note `P ∈ (k[X])[Y]`.
  set P : Polynomial (Polynomial k) := (g.map (algebraMap k (Polynomial k)))
    - Polynomial.C (Polynomial.X) * (h.map (algebraMap k (Polynomial k))) with hP_def

  -- key identity: swap P = C g - C h * X
  have h_swap : Polynomial.Bivariate.swap P = Polynomial.C g - Polynomial.C h * Polynomial.X := by
    ext i j
    simp [Bivariate.swap, Polynomial.coeff_C, Polynomial.coeff_X]
    split_ifs <;> simp_all
    · simp [Polynomial.aeval_def]
      simp [Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range]
      simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, Polynomial.eval_C]
      intro hj
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj]
    · simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
      simp [Polynomial.eval_finset_sum, Polynomial.coeff_C, pow_succ, Finset.sum_range_succ', ‹1 = i›.symm]
      rcases j with (_ | j) <;> simp [Polynomial.coeff_eq_zero_of_natDegree_lt]
      simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, Polynomial.eval_C]
      intro hj
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by linarith)]
    · simp_all [Polynomial.aeval_def]
      simp_all [Polynomial.eval₂_eq_sum_range]
      simp_all [Polynomial.eval_finset_sum]
      rcases i with (_ | _ | i) <;> simp_all [Polynomial.coeff_eq_zero_of_natDegree_lt]
  -- By `linear_irreducible (-h) g (by ... -h ≠ 0) (hcop.symm.neg_left)` this is irreducible.
  have h_linear_irreducible : Irreducible (Polynomial.C (-h) * Polynomial.X + Polynomial.C g) := by
    convert linear_irreducible (-h) g _ _ using 1 <;> norm_num [Polynomial.X_ne_zero]
    · exact UniqueFactorizationMonoid.toGCDMonoid k[X]
    · rintro rfl
      simp_all [IsCoprime]
      obtain ⟨a, ha⟩ := hcop
      have := congr_arg Polynomial.natDegree ha
      rw [Polynomial.natDegree_mul'] at this
      · simp only [Polynomial.natDegree_one] at this
        omega
      · rw [← Polynomial.leadingCoeff_mul, ha, Polynomial.leadingCoeff_one]
        exact one_ne_zero
    · exact hcop.symm.neg_left
  -- Since swap is an AlgEquiv (a ring isomorphism), irreducibility transports: `(AlgEquiv.irreducible_iff _).mp` / `(MulEquiv.irreducible_iff swap.toMulEquiv)`.
  have h_swap_irreducible : Irreducible (Polynomial.Bivariate.swap P) ↔ Irreducible P := by
    exact MulEquiv.irreducible_iff Bivariate.swap
  convert h_swap_irreducible.mp _ using 1
  convert h_linear_irreducible using 1
  rw [h_swap]
  simp [sub_eq_neg_add]
  ring

/-
**Irreducibility of the generic trinomial `g(Y) - T*h(Y)`** over `k(T)`.
`T = RatFunc.X` is a transcendental parameter and `g, h` are coprime, not both constant.
Analogue of `genPolyC_irreducible`; proved via the primitive polynomial in `(k[X])[Y]`
and Gauss's lemma.
-/
theorem auxPoly_irreducible (g h : k[X]) (hcop : IsCoprime g h)
    (hpos : 0 < max g.natDegree h.natDegree) :
    Irreducible ((g.map (algebraMap k (RatFunc k)))
      - Polynomial.C (RatFunc.X : RatFunc k) * (h.map (algebraMap k (RatFunc k)))) := by
  -- Let `P = g.map (algebraMap k (k[X])) - Polynomial.C (Polynomial.X : k[X]) * h.map (algebraMap k (k[X]))`.
  set P : Polynomial (Polynomial k) := (g.map (algebraMap k (Polynomial k)))
    - Polynomial.C (Polynomial.X : Polynomial k) * (h.map (algebraMap k (Polynomial k)))
  -- By Gauss's lemma, since `P` is primitive and irreducible over `k[X]`, it is also irreducible over `k(T)`.
  have h_gauss : Irreducible (Polynomial.map (algebraMap (Polynomial k) (RatFunc k)) P) := by
    convert Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map _ |>.1
      (auxPoly_R_irreducible g h hcop hpos) using 1
    · infer_instance
    · have h_irred : Irreducible P := by
        apply auxPoly_R_irreducible g h hcop hpos
      intro r hr
      obtain ⟨q, hq⟩ := hr
      have := h_irred.2 hq
      simp_all [Polynomial.isUnit_iff]
      rcases this with (⟨r, hr, rfl⟩ | ⟨a, ha, rfl⟩) <;> simp_all [Polynomial.ext_iff]
      · exact ⟨r, hr, fun n ↦ rfl⟩
      · have := hq 0 0
        have := hq 0 1
        have := hq 1 0
        have := hq 1 1
        simp_all [Polynomial.coeff_C, Polynomial.coeff_X]
        have h_const : ∀ n ≥ 2, g.coeff n = 0 ∧ h.coeff n = 0 := by
          intro n hn
          have := hq n 0
          have := hq n 1
          simp_all
          split_ifs at * <;> simp_all [Polynomial.coeff_eq_zero_of_natDegree_lt]
        have h_gh_const : g = Polynomial.C (g.coeff 0) ∧ h = Polynomial.C (h.coeff 0) := by
          constructor
          · apply Polynomial.ext
            intro n
            rcases n with (_ | _ | n) <;> simp_all
          · apply Polynomial.ext
            intro n
            rcases n with (_ | _ | n) <;> simp_all
        rw [h_gh_const.1, h_gh_const.2] at hpos
        simp_all +singlePass
  convert h_gauss using 1
  simp +zetaDelta at *
  simp [Polynomial.map_map]

/-
For a nonconstant (hence transcendental) rational function `θ`, the subfield `k⟮θ⟯` is
`k`-isomorphic to the whole rational function field, via an isomorphism sending the
generator `RatFunc.X` to `θ`.
-/
theorem exists_algEquiv_ratFunc (θ : RatFunc k)
    (h : θ ∉ (⊥ : IntermediateField k (RatFunc k))) :
    ∃ e : RatFunc k ≃ₐ[k] k⟮θ⟯,
      e RatFunc.X = ⟨θ, IntermediateField.subset_adjoin k {θ} rfl⟩ := by
  obtain ⟨τ, hτ⟩ : ∃ τ : (IntermediateField.adjoin k {θ})ˣ, τ.val = ⟨θ, IntermediateField.subset_adjoin k {θ} rfl⟩ := by
    refine ⟨Units.mk0 _ ?_, rfl⟩
    contrapose! h
    rw [Subtype.ext_iff] at h
    simp_all
  obtain ⟨e₀, he₀⟩ :
      ∃ e₀ : Polynomial k →ₐ[k] IntermediateField.adjoin k {θ},
        e₀ Polynomial.X = τ.val ∧ Function.Injective e₀ := by
    refine ⟨Polynomial.aeval (τ : ↥ (IntermediateField.adjoin k { θ })), ?_, ?_⟩ <;>
      simp_all [Function.Injective]
    have h_transcendental : Transcendental k θ := by
      grind only [transcendental_of_not_mem_bot]
    intro p q hpq
    have h_eval : Polynomial.aeval (R := k) θ p = Polynomial.aeval (R := k) θ q := by
      convert congr_arg Subtype.val hpq using 1 <;> simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
    apply Classical.not_not.1
    intro h
    refine h_transcendental ⟨p - q, sub_ne_zero.2 h, ?_⟩
    simp [h_eval]
  -- By RatFunc.liftAlgHom, it extends to a k-algebra hom e₀ : RatFunc k →ₐ[k] k⟮θ⟯ with e₀ RatFunc.X = τ.
  obtain ⟨e₀', he₀'⟩ :
      ∃ e₀' : RatFunc k →ₐ[k] IntermediateField.adjoin k {θ},
        e₀' (RatFunc.X : RatFunc k) = τ.val ∧ Function.Injective e₀' := by
    have h_lift :
        ∃ e₀' : RatFunc k →ₐ[k] IntermediateField.adjoin k {θ},
          e₀' ∘ (algebraMap (Polynomial k) (RatFunc k)) = e₀ := by
      refine ⟨RatFunc.liftAlgHom e₀ ?_, ?_⟩
      · intro x hx
        simp at *
        intro h
        apply hx
        apply he₀.2
        simpa using h
      · funext x
        simp [liftAlgHom]
    obtain ⟨e₀', he₀'⟩ := h_lift
    refine ⟨e₀', ?_, ?_⟩
    · convert congr_fun he₀' Polynomial.X using 1
      exact he₀.1.symm
    · exact e₀'.injective
  -- Step 3: e₀' is surjective. Let y ∈ k⟮θ⟯. By IntermediateField.mem_adjoin_simple_iff, y = (aeval θ p)/(aeval θ q) for some p, q ∈ k[X] (as an element of k⟮θ⟯, i.e. y.val = that in RatFunc k). Then y = e₀' (RatFunc.mk p q) = e₀' ((algebraMap k[X] (RatFunc k) p)/(algebraMap k[X] (RatFunc k) q)), because e₀' ∘ algebraMap k[X] (RatFunc k) = aeval τ (both send X ↦ τ and agree on k), and e₀' preserves division. Conclude bijective.
  have h_surj : Function.Surjective e₀' := by
    intro y
    obtain ⟨p, q, hpq⟩ : ∃ p q : Polynomial k, y.val = (Polynomial.aeval θ p) / (Polynomial.aeval θ q) := by
      have := IntermediateField.mem_adjoin_simple_iff
      exact this k y.1 |>.1 y.2
    have h_eval : e₀' (RatFunc.mk p q) = (Polynomial.aeval τ.val p) / (Polynomial.aeval τ.val q) := by
      have h_eval : ∀ p : Polynomial k, e₀' (algebraMap (Polynomial k) (RatFunc k) p) = Polynomial.aeval τ.val p := by
        intro p
        induction' p using Polynomial.induction_on with p q hp hq
        · simp [Polynomial.aeval_def]
          exact e₀'.commutes p
        · simp [*, map_add]
        · simp_all [pow_succ, ← mul_assoc]
      by_cases hq : q = 0 <;> simp_all [RatFunc.mk_eq_div]
    simp_all [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
    use (algebraMap k[X] (RatFunc k)) p / (algebraMap k[X] (RatFunc k)) q
    convert h_eval using 1
    · exact map_div₀ _ _ _
    · ext
      simp [hpq]
      simp [div_eq_mul_inv]
      apply Or.inl
      erw [Subtype.coe_mk]
      simp
  refine ⟨AlgEquiv.ofBijective e₀' ⟨he₀'.2, h_surj⟩, ?_⟩
  simp_all

/-
The defining relation `num = θ * denom` in `RatFunc k`.
-/
theorem num_eq_mul_denom (θ : RatFunc k) :
    algebraMap (k[X]) (RatFunc k) θ.num
      = θ * algebraMap (k[X]) (RatFunc k) θ.denom := by
  grind only [num_div_denom, denom_ne_zero, algebraMap_apply, algebraMap_ne_zero]

/-
A nonconstant rational function has positive height.
-/
theorem height_pos_of_not_mem_bot (θ : RatFunc k)
    (h : θ ∉ (⊥ : IntermediateField k (RatFunc k))) : 0 < height θ := by
  contrapose! h
  have := RatFunc.num_div_denom θ
  simp_all [RatFunc.height]
  obtain ⟨a, b, ha, hb⟩ : ∃ a b : k, θ.num = Polynomial.C a ∧ θ.denom = Polynomial.C b := by
    exact ⟨_, _, Polynomial.eq_C_of_natDegree_eq_zero h.1, Polynomial.eq_C_of_natDegree_eq_zero h.2⟩
  rw [← RatFunc.num_div_denom θ, ha, hb]
  refine ⟨a / b, ?_⟩
  simp [div_eq_mul_inv]

/-
**Degree formula.** For a nonconstant rational function `θ`, the rational function
field `k(X)` is a finite extension of `k(θ)` of degree equal to the height of `θ`.
-/
theorem finrank_adjoin_eq_height (θ : RatFunc k)
    (h : θ ∉ (⊥ : IntermediateField k (RatFunc k))) :
    Module.finrank k⟮θ⟯ (RatFunc k) = height θ := by
  -- Here `height θ = max (deg num) (deg denom)`.
  set g := θ.num
  set h := θ.denom
  set K := k⟮θ⟯
  set τ : K := ⟨θ, IntermediateField.subset_adjoin k {θ} rfl⟩
  set G : Polynomial K := Polynomial.map (algebraMap k K) g - Polynomial.C τ * Polynomial.map (algebraMap k K) h
  -- Fact 1 (irreducible): G is irreducible over K.
  have hG_irreducible : Irreducible G := by
    obtain ⟨e, he⟩ := exists_algEquiv_ratFunc θ ‹_›
    convert (auxPoly_irreducible g h (RatFunc.isCoprime_num_denom θ) (height_pos_of_not_mem_bot θ ‹_›))
      |> Irreducible.map (Polynomial.mapEquiv e.toRingEquiv) using 1
    ext
    simp [he, Polynomial.map_map]
    simp +zetaDelta at *
    erw [e.commutes, e.commutes]
    trivial
  -- Fact 2 (root): G has X as a root.
  have hG_root : Polynomial.aeval (RatFunc.X : RatFunc k) G = 0 := by
    convert sub_eq_zero.mpr (num_eq_mul_denom θ) using 1
    simp +zetaDelta at *
  -- Fact 3 (degree): The degree of G is equal to the height of θ.
  have hG_degree : G.natDegree = θ.height := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · exact le_trans (Polynomial.natDegree_map_le ..) (le_max_left _ _)
      · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.natDegree_map]
        exact le_max_right _ _
    · -- The coefficient of `X ^ height θ` in `G` is `g.coeff (height θ) - τ * h.coeff (height θ)`.
      have h_coeff : G.coeff θ.height = algebraMap k K (g.coeff θ.height) - τ * algebraMap k K (h.coeff θ.height) := by
        simp_all only [aeval_sub, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, map_mul, aeval_C, IntermediateField.algebraMap_apply, coeff_sub, coeff_map, coeff_C_mul, K, G, g, τ, h]
      intro h_zero
      have h_const : θ = RatFunc.C (g.coeff θ.height / h.coeff θ.height) := by
        have h_ratio : algebraMap k K (g.coeff θ.height) = τ * algebraMap k K (h.coeff θ.height) :=
          eq_of_sub_eq_zero (h_coeff.symm.trans h_zero)
        have h_eq :
            algebraMap k (RatFunc k) (g.coeff θ.height) = θ * algebraMap k (RatFunc k) (h.coeff θ.height) := by
          convert congr_arg (algebraMap K (RatFunc k)) h_ratio using 1
        by_cases h : h.coeff θ.height = 0 <;> simp_all [div_eq_mul_inv, mul_comm]
        cases max_choice (Polynomial.natDegree θ.num) (Polynomial.natDegree θ.denom) <;>
          simp_all [RatFunc.height]
        · apply absurd h_ratio
          rw [Polynomial.coeff_natDegree]
          refine mt Polynomial.leadingCoeff_eq_zero.1 ?_
          rename_i h_2 h_3
          simp_all only [aeval_sub, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, map_mul, aeval_C, IntermediateField.algebraMap_apply, coeff_sub, coeff_map, coeff_natDegree, coeff_C_mul, leadingCoeff_eq_zero, num_eq_zero_iff, denom_zero, num_zero, natDegree_zero, coeff_one_zero, one_ne_zero, K, G, g, τ, h_2]
        · apply absurd h
          intro h
          apply absurd h
          intro h
          refine absurd (RatFunc.denom_ne_zero θ) ?_
          exact fun hne ↦ hne (Polynomial.leadingCoeff_eq_zero.mp h)
      apply ‹θ ∉ ⊥›
      rw [h_const]
      exact IntermediateField.mem_bot.mpr ⟨_, rfl⟩
  -- Therefore, the minimal polynomial of `X` over `K` is `G`.
  have h_minpoly : minpoly K (RatFunc.X : RatFunc k) = G * Polynomial.C (G.leadingCoeff)⁻¹ := by
    refine Eq.symm (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_)
    · rw [irreducible_mul_iff]
      simp_all only [aeval_sub, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, map_mul, aeval_C, IntermediateField.algebraMap_apply, isUnit_map_iff, isUnit_iff_ne_zero, ne_eq, inv_eq_zero, leadingCoeff_eq_zero, true_and, K, G, g, τ, h]
      obtain ⟨val, property⟩ := τ
      apply Or.inl
      apply Aesop.BuiltinRules.not_intro
      intro a
      simp_all only [not_irreducible_zero]
    · simp_all
    · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      exact mul_inv_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hG_irreducible.ne_zero)
  -- Therefore, the degree of the extension `K(X)` over `K` equals the degree of `G`, which is `θ.height`.
  have h_finrank : Module.finrank K (RatFunc k) = Polynomial.natDegree (minpoly K (RatFunc.X : RatFunc k)) := by
    have h_finrank : IsIntegral K (RatFunc.X : RatFunc k) := by
      refine ⟨G * Polynomial.C (G.leadingCoeff) ⁻¹, ?_, ?_⟩
      · exact Polynomial.monic_mul_leadingCoeff_inv hG_irreducible.ne_zero
      · simp_all [Polynomial.aeval_def]
    convert IntermediateField.adjoin.finrank h_finrank
    rw [adjoin_X_top' K]
    simp [Module.finrank]
  rw [h_finrank, h_minpoly, Polynomial.natDegree_mul']
  · simp_all only [aeval_sub, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, map_mul, aeval_C, IntermediateField.algebraMap_apply, natDegree_C, add_zero, K, G, g, τ, h]
  · simp_all only [aeval_sub, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, map_mul, aeval_C, IntermediateField.algebraMap_apply, leadingCoeff_C, ne_eq, mul_eq_zero, leadingCoeff_eq_zero, inv_eq_zero, or_self, K, G, g, τ, h]
    obtain ⟨val, property⟩ := τ
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [not_irreducible_zero]

/-
`RatFunc k` is finite over any intermediate field `M ≠ ⊥`.
-/
theorem finiteDimensional_of_ne_bot (M : IntermediateField k (RatFunc k)) (hM : M ≠ ⊥) :
    FiniteDimensional M (RatFunc k) := by
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : RatFunc k, θ₀ ∈ M ∧ θ₀ ∉ (⊥ : IntermediateField k (RatFunc k)) := by
    contrapose! hM
    exact le_bot_iff.mp hM
  have h_finrank : FiniteDimensional k⟮θ₀⟯ (RatFunc k) := by
    have h_eq := finrank_adjoin_eq_height θ₀ hθ₀.2
    apply FiniteDimensional.of_finrank_pos
    rw [h_eq]
    exact height_pos_of_not_mem_bot θ₀ hθ₀.2
  have h_subfield : k⟮θ₀⟯ ≤ M := by
    simp_all
  obtain ⟨s, hs⟩ := h_finrank
  refine ⟨s, ?_⟩
  rw [Submodule.eq_top_iff'] at hs ⊢
  intro x
  obtain ⟨y, hy⟩ := Submodule.mem_span_finset.mp (hs x)
  rw [← hy.2]
  apply Submodule.sum_mem
  intro a ha
  rw [Submodule.mem_span]
  intro p hp
  exact p.smul_mem (⟨y a, h_subfield (y a |>.2)⟩ : M) (hp ha)

/-
The minimal polynomial of `RatFunc.X` over `M` has a nonconstant coefficient (otherwise
`RatFunc.X` would be algebraic over `k`).
-/
theorem exists_coeff_not_mem_bot (M : IntermediateField k (RatFunc k))
    [FiniteDimensional M (RatFunc k)] (hM : M ≠ ⊥) :
    ∃ j, ((minpoly M (RatFunc.X : RatFunc k)).coeff j : RatFunc k)
      ∉ (⊥ : IntermediateField k (RatFunc k)) := by
  contrapose! hM
  -- If all coefficients of the minimal polynomial of `X` over `M` are in `k`, then `X` is algebraic over `k`.
  have h_alg : IsAlgebraic k (RatFunc.X : RatFunc k) := by
    -- By assumption, every coefficient of `F` lies in `k`.
    obtain ⟨g, hg⟩ : ∃ g : Polynomial k, (minpoly M (RatFunc.X : RatFunc k)) = Polynomial.map (algebraMap k M) g := by
      choose f hf using fun j ↦ mem_bot_iff _ |>.1 (hM j)
      use ∑ j ∈ (minpoly M (RatFunc.X : RatFunc k)).support, f j • Polynomial.X ^ j
      ext j
      simp_all only [coeff_map, finset_sum_coeff, coeff_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, mem_support_iff, ne_eq, SubalgebraClass.coe_algebraMap, algebraMap_eq_C]
      split
      next h => simp_all only [mem_support_iff, ne_eq]
      next h => simp_all only [mem_support_iff, ne_eq, not_not, ZeroMemClass.coe_zero, map_zero]
    refine ⟨g, ?_, ?_⟩
    · intro h
      simp_all
      exact minpoly.ne_zero (show IsIntegral M (RatFunc.X : RatFunc k) from (IsIntegral.of_finite M _)) hg
    · have := minpoly.aeval M (RatFunc.X : RatFunc k)
      simp_all [Polynomial.aeval_def, Polynomial.eval₂_map]
      exact this
  exact False.elim (RatFunc.transcendental_X h_alg)

/-- The antisymmetric bivariate polynomial `h(x)·g(Y) - g(x)·h(Y)` in `k[X][X]` (the outer
`X` is the polynomial variable `Y`, the inner `X` the base variable `x`).  It is the key
auxiliary object of the van der Waerden content argument. -/
noncomputable def bivarR (g h : k[X]) : k[X][X] :=
  Polynomial.C h * g.map (algebraMap k (k[X]))
    - Polynomial.C g * h.map (algebraMap k (k[X]))

/-
`bivarR g h` is antisymmetric under the bivariate variable swap.
-/
theorem bivarR_swap (g h : k[X]) :
    Polynomial.Bivariate.swap (bivarR g h) = - bivarR g h := by
  unfold bivarR Bivariate.swap
  rw [map_sub, map_mul, map_mul]
  norm_num
  simp_all [Polynomial.aeval_def]
  simp [Polynomial.eval₂_eq_sum_range]
  simp [Polynomial.eval_finset_sum]
  conv_rhs =>
    rw [Polynomial.as_sum_range_C_mul_X_pow g, Polynomial.as_sum_range_C_mul_X_pow h]
    ring_nf
  simp [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, add_comm]
  ring

/-
The `Y`-degree of `bivarR g h` is `max (deg g) (deg h)`.
-/
theorem bivarR_natDegree (g h : k[X]) (hcop : IsCoprime g h)
    (hpos : 0 < max g.natDegree h.natDegree) :
    (bivarR g h).natDegree = max g.natDegree h.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    refine max_le ?_ ?_ <;> refine le_trans (Polynomial.natDegree_mul_le ..) ?_ <;> simp [*]
  · by_cases h_deg : g.natDegree = max g.natDegree h.natDegree
    · unfold bivarR
      simp [← h_deg, Polynomial.coeff_C_mul]
      intro H
      -- Since `g` and `h` are coprime and `g ∣ h * leadingCoeff g`, it follows that `g ∣ leadingCoeff g`.
      have h_div : g ∣ Polynomial.C (g.leadingCoeff) := by
        apply hcop.dvd_of_dvd_mul_left
        refine ⟨Polynomial.C (h.coeff g.natDegree), ?_⟩
        linear_combination' H
      have := Polynomial.natDegree_le_of_dvd h_div
      by_cases hg : g = 0 <;> simp_all +singlePass
    · unfold bivarR
      cases max_cases g.natDegree h.natDegree <;> simp_all [Polynomial.coeff_eq_zero_of_natDegree_lt]
      constructor <;> rintro rfl <;> simp_all
      simp_all [isCoprime_zero_left]
      exact hpos.ne' (Polynomial.natDegree_eq_zero_of_isUnit hcop)

/-
`bivarR g h` is primitive (its content over `k[X]` is a unit) when `g, h` are coprime and
not both constant.  Indeed the `Y^i`-coefficient of `bivarR g h` is `g_i·h - h_i·g`, a
`k`-linear combination of `g` and `h`; since the coefficient vectors of `g` and `h` are
linearly independent (they are coprime and not both constant, hence not proportional), the
gcd of these combinations divides both `g` and `h`, hence is a unit.
-/
theorem bivarR_isPrimitive (g h : k[X]) (hcop : IsCoprime g h)
    (hpos : 0 < max g.natDegree h.natDegree) :
    (bivarR g h).IsPrimitive := by
  intro d hd
  -- The coefficients of `bivarR` are linear combinations of the coefficients of `g` and `h`.
  have h_coeff : ∀ i, d ∣ (g.coeff i) • h - (h.coeff i) • g := by
    intro i
    have h_coeff_i : Polynomial.coeff (bivarR g h) i = (g.coeff i) • h - (h.coeff i) • g := by
      simp [bivarR, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      simp [mul_comm, Polynomial.smul_eq_C_mul]
    rw [← h_coeff_i]
    rcases hd with ⟨q, hq⟩
    refine ⟨Polynomial.coeff q i, ?_⟩
    simpa [Polynomial.coeff_C_mul] using
      congr_arg (fun p : Polynomial (Polynomial k) ↦ Polynomial.coeff p i) hq
  -- Since `g` and `h` are coprime and not both constant, their coefficient vectors are linearly independent over `k`.
  have h_lin_indep : ∃ i j : ℕ, g.coeff i * h.coeff j ≠ g.coeff j * h.coeff i := by
    by_contra! h
    rename_i h'
    -- If the coefficients of `g` and `h'` are proportional, then `g` and `h'` are linearly dependent.
    have h_lin_dep : ∃ c : k, g = Polynomial.C c * h' := by
      by_cases h' : h' = 0 <;> simp_all [Polynomial.ext_iff]
      · simp_all [isCoprime_zero_right]
        rw [Polynomial.isUnit_iff] at hcop
        intro n
        simp_all only [isUnit_iff_ne_zero, ne_eq]
        obtain ⟨w, h⟩ := hcop
        obtain ⟨left, right⟩ := h
        subst right
        simp_all only [natDegree_C, lt_self_iff_false]
      · obtain ⟨i, hi⟩ := h'
        refine ⟨g.coeff i / h'.coeff i, ?_⟩
        intro n
        rw [div_mul_eq_mul_div, eq_div_iff hi]
        linear_combination' h n i
    rcases h_lin_dep with ⟨c, rfl⟩
    simp_all [IsCoprime]
    -- Since `h'` is a unit, its degree must be zero.
    have h_deg_zero : h'.natDegree = 0 := by
      apply Polynomial.natDegree_eq_zero_of_isUnit
      apply isUnit_of_dvd_one
      rw [← hcop.choose_spec.choose_spec]
      exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) (dvd_mul_left _ _)
    rw [Polynomial.natDegree_mul'] at hpos
    · simp [Polynomial.natDegree_C, h_deg_zero] at hpos
    · have hc : c ≠ 0 := by
        rintro rfl
        simp [h_deg_zero] at hpos
      have hh' : h' ≠ 0 := by
        rintro rfl
        simp at hpos
      simp [Polynomial.leadingCoeff_C, hc, hh']
  obtain ⟨i, j, hij⟩ := h_lin_indep
  have h_div_g : d ∣ g := by
    have h_div_g :
        d ∣ (g.coeff i • h - h.coeff i • g) * Polynomial.C (g.coeff j)
          - (g.coeff j • h - h.coeff j • g) * Polynomial.C (g.coeff i) := by
      exact dvd_sub (dvd_mul_of_dvd_left (h_coeff i) _) (dvd_mul_of_dvd_left (h_coeff j) _)
    convert h_div_g.mul_left (Polynomial.C ((g.coeff i * h.coeff j - g.coeff j * h.coeff i) ⁻¹)) using 1
    ring_nf
    ext
    simp [Polynomial.smul_eq_C_mul]
    ring_nf
    grind
  have h_div_h : d ∣ h := by
    have h_dvd_smul : ∀ i, d ∣ (g.coeff i) • h := by
      intro i
      specialize h_coeff i
      have h_div_g_i : d ∣ (h.coeff i) • g := dvd_smul_of_dvd _ h_div_g
      convert dvd_add h_coeff h_div_g_i using 1
      simp [sub_add_cancel]
    obtain ⟨i, hi⟩ : ∃ i, g.coeff i ≠ 0 := by
      refine ⟨Polynomial.natDegree g, ?_⟩
      simp_all only [lt_sup_iff, ne_eq, coeff_natDegree, leadingCoeff_eq_zero]
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [natDegree_zero, lt_self_iff_false, false_or, coeff_zero, zero_smul, smul_zero, sub_self, implies_true, zero_mul, not_true_eq_false]
    specialize h_dvd_smul i
    simp_all [Polynomial.smul_eq_C_mul]
  exact hcop.isUnit_of_dvd' h_div_g h_div_h

/-
The `Y`-degree of the bivariate swap of `P` dominates the `x`-degree of every
`Y`-coefficient of `P`.  (Swapping the two variables turns the `x`-degree of a coefficient
into a `Y`-degree.)
-/
theorem natDegree_le_natDegree_swap (P : k[X][X]) (i : ℕ) :
    (P.coeff i).natDegree ≤ (Polynomial.Bivariate.swap P).natDegree := by
  -- Let's denote the swap of `P` by `Q`.
  set Q : Polynomial (Polynomial k) := P.aevalAeval Polynomial.X (Polynomial.C Polynomial.X)
  -- The coefficients of `Q` are those of `P` with the roles of `X` and `Y` swapped.
  have h_coeff : ∀ i j : ℕ, Polynomial.coeff (Polynomial.coeff Q i) j = Polynomial.coeff (Polynomial.coeff P j) i := by
    intro i j
    induction' P using Polynomial.induction_on' with p q hp hq
    · simp_all [Polynomial.aeval_def]
      simp +zetaDelta at *
      exact congr_arg₂ (· + ·) hp hq
    · simp +zetaDelta at *
      rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      rw [Finset.sum_eq_single i] <;> simp
      · simp [Polynomial.coeff_monomial, aeval_def]
        simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval₂_eq_sum_range]
        split_ifs <;> simp_all [Polynomial.coeff_X_pow]
        · grind
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ‹_›]
      · intro b hb hbi
        right
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
        simp [Polynomial.natDegree_pow, Polynomial.natDegree_C]
        exact lt_of_le_of_ne hb hbi
  by_cases hi : Polynomial.coeff P i = 0
  · simp [hi]
  · apply Polynomial.le_natDegree_of_ne_zero
    intro h
    specialize h_coeff (Polynomial.natDegree (P.coeff i)) i
    simp_all
    simp +zetaDelta at *
    simp_all
    exact hi (Polynomial.leadingCoeff_eq_zero.mp h_coeff.symm)

/-
**The content-and-swap finish** of the van der Waerden argument.  If `P` is primitive and
antisymmetric (`swap P = -P`), and `P = φ * S` with the `Y`-degree of `swap φ` at least the
`Y`-degree of `P`, then in fact `P.natDegree ≤ φ.natDegree` (equivalently `S` is constant in
`Y`).  The proof: from `swap P = -P` we get `-P = swap φ * swap S`, so
`swap S` has `Y`-degree `≤ P.natDegree - (swap φ).natDegree ≤ 0`; hence `swap S = C s` for some
`s ∈ k[X]`, and `C s ∣ P`; primitivity of `P` forces `s` to be a unit, so `S` is constant in
`Y`.
-/
theorem primitive_swap_degree_finish (P φ S : k[X][X]) (hP : P.IsPrimitive)
    (hPswap : Polynomial.Bivariate.swap P = -P) (hmul : P = φ * S)
    (hφ0 : φ ≠ 0) (hS0 : S ≠ 0)
    (hdx : P.natDegree ≤ (Polynomial.Bivariate.swap φ).natDegree) :
    P.natDegree ≤ φ.natDegree := by
  -- From `swap P = -P`, we see `-P = swap φ * swap S`, so `swap S` has `Y`-degree `≤ P.natDegree - (swap φ).natDegree ≤ 0`; hence `swap S = C s` for some `s ∈ k[X]`, and `C s ∣ P`; primitivity of `P` forces `s` to be a unit, so `S` is constant in `Y`.
  have h_swap_S : ∃ s : k[X], Polynomial.Bivariate.swap S = Polynomial.C s := by
    refine ⟨_, Polynomial.eq_C_of_natDegree_eq_zero ?_⟩
    have h_deg_swap_S : (Bivariate.swap P).natDegree = (Bivariate.swap φ).natDegree + (Bivariate.swap S).natDegree := by
      rw [hmul, map_mul, Polynomial.natDegree_mul']
      subst hmul
      simp_all
      apply And.intro
      · apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all only [zero_mul, zero_eq_neg, mul_eq_zero, or_self]
      · apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all only [mul_zero, zero_eq_neg, mul_eq_zero, or_self]
    rw [hPswap, Polynomial.natDegree_neg] at h_deg_swap_S
    linarith
  -- Since `swap S = C s` for some `s ∈ k[X]`, we have `C s ∣ P`. By `hP : P.IsPrimitive`, `IsUnit s`.
  obtain ⟨s, hs⟩ := h_swap_S
  have h_unit : IsUnit s := by
    have h_dvd : Polynomial.C s ∣ P := by
      have h_div : Polynomial.Bivariate.swap P = Polynomial.Bivariate.swap φ * Polynomial.C s := by
        rw [← hs, hmul, map_mul]
      rw [hPswap] at h_div
      refine ⟨-Bivariate.swap φ, ?_⟩
      linear_combination' -h_div
    refine hP _ ?_
    simpa using h_dvd
  have h_S_const : S.natDegree = 0 := by
    have h_S_eq : S = Polynomial.Bivariate.swap.symm (Polynomial.C s) := by
      rw [← hs, AlgEquiv.symm_apply_apply]
    simp [h_S_eq, Polynomial.Bivariate.swap]
    rw [Polynomial.isUnit_iff] at h_unit
    subst hmul h_S_eq
    simp_all
    obtain ⟨w, h⟩ := h_unit
    obtain ⟨left, right⟩ := h
    subst right
    simp_all only [map_eq_zero, not_false_eq_true, aeval_C, Polynomial.algebraMap_apply, algebraMap_eq, natDegree_C]
  rw [hmul, Polynomial.natDegree_mul'] <;> simp_all

/-- Every nonzero polynomial over `k(X) = Frac(k[X])` has a *primitive integer* representative:
a primitive `φ ∈ k[X][X]` of the same degree whose image over `k(X)` is a unit multiple of it.
Obtained from `IsLocalization.integerNormalization` and `Polynomial.primPart`. -/
theorem exists_primitive_repr (F' : (RatFunc k)[X]) (hF' : F' ≠ 0) :
    ∃ φ : k[X][X], φ.IsPrimitive ∧ φ.natDegree = F'.natDegree ∧
      ∃ w : RatFunc k, IsUnit w ∧
        φ.map (algebraMap (k[X]) (RatFunc k)) = Polynomial.C w * F' := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors (k[X])) F'
  set N := IsLocalization.integerNormalization (nonZeroDivisors (k[X])) F' with hN
  have hinj : Function.Injective (algebraMap (k[X]) (RatFunc k)) :=
    IsFractionRing.injective (k[X]) (RatFunc k)
  have hbne : ((b : k[X])) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hβb : algebraMap (k[X]) (RatFunc k) (b : k[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hbne
  have hbF : N.map (algebraMap (k[X]) (RatFunc k))
      = Polynomial.C (algebraMap (k[X]) (RatFunc k) (b : k[X])) * F' := by
    rw [hb, ← IsScalarTower.algebraMap_smul (RatFunc k) (b : k[X]) F', Polynomial.smul_eq_C_mul]
  have hNmap_ne : N.map (algebraMap (k[X]) (RatFunc k)) ≠ 0 := by
    rw [hbF]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hβb) hF'
  have hNne : N ≠ 0 := fun h ↦ hNmap_ne (by
    rw [h]
    simp)
  have hNdeg : N.natDegree = F'.natDegree := by
    have h := Polynomial.natDegree_map_eq_of_injective hinj N
    rw [hbF, Polynomial.natDegree_C_mul hβb] at h
    exact h.symm
  have hcont : N = Polynomial.C N.content * N.primPart := Polynomial.eq_C_content_mul_primPart N
  have hcontne : N.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
  have hβc : algebraMap (k[X]) (RatFunc k) N.content ≠ 0 := (map_ne_zero_iff _ hinj).mpr hcontne
  have hmap2 : N.map (algebraMap (k[X]) (RatFunc k))
      = Polynomial.C (algebraMap (k[X]) (RatFunc k) N.content)
          * N.primPart.map (algebraMap (k[X]) (RatFunc k)) := by
    conv_lhs => rw [hcont]
    rw [Polynomial.map_mul, Polynomial.map_C]
  refine ⟨N.primPart, Polynomial.isPrimitive_primPart N, ?_,
    algebraMap (k[X]) (RatFunc k) (b : k[X]) * (algebraMap (k[X]) (RatFunc k) N.content)⁻¹,
    (Ne.isUnit hβb).mul (Ne.isUnit hβc).inv, ?_⟩
  · rw [Polynomial.natDegree_primPart, hNdeg]
  have h1 : Polynomial.C (algebraMap (k[X]) (RatFunc k) N.content)
        * N.primPart.map (algebraMap (k[X]) (RatFunc k))
      = Polynomial.C (algebraMap (k[X]) (RatFunc k) (b : k[X])) * F' := by
    rw [← hmap2, hbF]
  have h2 := congrArg
    (fun p ↦ Polynomial.C (algebraMap (k[X]) (RatFunc k) N.content)⁻¹ * p) h1
  simp only [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hβc, Polynomial.C_1, one_mul] at h2
  rw [h2, mul_comm (algebraMap (k[X]) (RatFunc k) (b:k[X]))]

/-
**The van der Waerden content bound** (the crux of Lüroth's theorem): the height of any
nonconstant coefficient of the minimal polynomial of `RatFunc.X` over `M` is at most the
degree of that minimal polynomial.
-/
theorem height_coeff_le (M : IntermediateField k (RatFunc k))
    [FiniteDimensional M (RatFunc k)] (j : ℕ)
    (hj : ((minpoly M (RatFunc.X : RatFunc k)).coeff j : RatFunc k)
      ∉ (⊥ : IntermediateField k (RatFunc k))) :
    height ((minpoly M (RatFunc.X : RatFunc k)).coeff j : RatFunc k)
      ≤ (minpoly M (RatFunc.X : RatFunc k)).natDegree := by
  set t := (RatFunc.X : RatFunc k)
  set F := minpoly M t
  set n := F.natDegree
  set θ := ((F.coeff j) : RatFunc k)
  set g := θ.num
  set h := θ.denom
  obtain ⟨φ, hφprim, hφdeg, w, hwu, hφmap⟩ := exists_primitive_repr (F.map (algebraMap M (RatFunc k)))
    (Polynomial.map_ne_zero (minpoly.ne_zero (IsIntegral.of_finite M t)))
  -- By the properties of the primitive polynomial and the swap, we have that `φ ∣ bivarR g h`.
  have h_div : φ ∣ bivarR g h := by
    have h_divF :
        F.map (algebraMap M (RatFunc k)) ∣
          (g.map (algebraMap k (RatFunc k)) - Polynomial.C θ * h.map (algebraMap k (RatFunc k))) := by
      have h_aeval0 :
          Polynomial.aeval t (g.map (algebraMap k M) - Polynomial.C (F.coeff j) * h.map (algebraMap k M)) = 0 := by
        have h_num : algebraMap (k[X]) (RatFunc k) g = θ * algebraMap (k[X]) (RatFunc k) h :=
          num_eq_mul_denom θ
        simp +zetaDelta at *
        rw [h_num, sub_self]
      have h_Fdvd : F ∣ (g.map (algebraMap k M) - Polynomial.C (F.coeff j) * h.map (algebraMap k M)) :=
        minpoly.dvd M t h_aeval0
      convert Polynomial.map_dvd (algebraMap M (RatFunc k)) h_Fdvd using 1
      simp [Polynomial.map_map]
      rfl
    have h_divφ :
        φ.map (algebraMap k[X] (RatFunc k)) ∣
          (Polynomial.C (algebraMap (Polynomial k) (RatFunc k) h) * g.map (algebraMap k (RatFunc k))
            - Polynomial.C (algebraMap (Polynomial k) (RatFunc k) g) * h.map (algebraMap k (RatFunc k))) := by
      have h_divφ_aux :
          Polynomial.map (algebraMap k[X] (RatFunc k)) φ ∣
            Polynomial.C (algebraMap (Polynomial k) (RatFunc k) h) *
              (Polynomial.map (algebraMap k (RatFunc k)) g
                - Polynomial.C θ * Polynomial.map (algebraMap k (RatFunc k)) h) := by
        rw [hφmap]
        refine mul_dvd_mul ?_ h_divF
        refine ⟨Polynomial.C ((algebraMap k[X] (RatFunc k)) h * w⁻¹), ?_⟩
        rw [← Polynomial.C_mul, mul_comm]
        simp [hwu.ne_zero]
      rw [num_eq_mul_denom]
      ring_nf
      grind +splitIndPred
    convert Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map (RatFunc k) hφprim
        (show Polynomial.IsPrimitive (bivarR g h) from ?_) |>.2 ?_ using 1
    · apply bivarR_isPrimitive
      · exact RatFunc.isCoprime_num_denom _
      · exact height_pos_of_not_mem_bot θ hj
    · convert h_divφ using 1
      simp [bivarR]
      simp [Polynomial.map_map]
  obtain ⟨S, hS⟩ : ∃ S : k[X][X], bivarR g h = φ * S := h_div
  have hS0 : S ≠ 0 := by
    intro hS0
    have hR0 : bivarR g h = 0 := by
      rw [hS, hS0]
      simp
    have := bivarR_natDegree g h (RatFunc.isCoprime_num_denom θ) (height_pos_of_not_mem_bot θ hj)
    simp_all
    exact absurd this (ne_of_lt (height_pos_of_not_mem_bot θ hj))
  have hdx : (bivarR g h).natDegree ≤ (Polynomial.Bivariate.swap φ).natDegree := by
    have h_dvd_coeff : h ∣ φ.coeff n ∧ g ∣ φ.coeff j := by
      have h_eq1 : algebraMap (k[X]) (RatFunc k) (φ.coeff j) = θ * algebraMap (k[X]) (RatFunc k) (φ.coeff n) := by
        have h_eq2 :
            algebraMap (k[X]) (RatFunc k) (φ.coeff j) = w * θ ∧
              algebraMap (k[X]) (RatFunc k) (φ.coeff n) = w := by
          have h_eq3 :
              Polynomial.coeff (Polynomial.map (algebraMap (k[X]) (RatFunc k)) φ) j = w * θ ∧
                Polynomial.coeff (Polynomial.map (algebraMap (k[X]) (RatFunc k)) φ) n = w := by
            simp_all [Polynomial.coeff_C_mul]
            exact ⟨rfl, minpoly.monic (IsIntegral.of_finite M t)⟩
          simpa [Polynomial.coeff_map] using h_eq3
        rw [h_eq2.1, h_eq2.2, mul_comm]
      have h_eq4 : algebraMap (k[X]) (RatFunc k) (φ.coeff j * h) = algebraMap (k[X]) (RatFunc k) (φ.coeff n * g) := by
        simp [h_eq1, mul_comm, mul_left_comm]
        rw [mul_left_comm, ← num_eq_mul_denom]
      have h_prod : φ.coeff j * h = φ.coeff n * g :=
        IsFractionRing.injective (Polynomial k) (RatFunc k) h_eq4
      have h_dvd_n : h ∣ φ.coeff n := by
        have h_coprime : IsCoprime g h := RatFunc.isCoprime_num_denom _
        apply h_coprime.symm.dvd_of_dvd_mul_right
        rw [← h_prod]
        exact dvd_mul_left _ _
      have h_dvd_j : g ∣ φ.coeff j := by
        have h_dvd_jh : g ∣ φ.coeff j * h := by
          simp_all
        exact IsCoprime.dvd_of_dvd_mul_right (RatFunc.isCoprime_num_denom θ) h_dvd_jh
      exact ⟨h_dvd_n, h_dvd_j⟩
    have hdx :
        h.natDegree ≤ (Polynomial.Bivariate.swap φ).natDegree ∧
          g.natDegree ≤ (Polynomial.Bivariate.swap φ).natDegree := by
      apply And.intro
      · have hcoeff_n : φ.coeff n ≠ 0 := by
          intro h_coeff_zero
          replace hφmap := congr_arg (fun p ↦ Polynomial.coeff p n) hφmap
          simp_all [Polynomial.coeff_map]
          have hmonic := minpoly.monic (IsIntegral.of_finite M t)
          apply absurd hφmap
          rw [hmonic.coeff_natDegree]
          simp
        exact le_trans (Polynomial.natDegree_le_of_dvd h_dvd_coeff.left hcoeff_n)
          (natDegree_le_natDegree_swap φ n)
      · have hcoeff_j : φ.coeff j ≠ 0 := by
          replace hφmap := congr_arg (fun p ↦ p.coeff j) hφmap
          simp_all only [natDegree_map, isUnit_iff_ne_zero, ne_eq, coeff_map, coeff_C_mul, IntermediateField.algebraMap_apply,
            θ, F, t, g, h, n]
          obtain ⟨left, right⟩ := h_dvd_coeff
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [map_zero, zero_eq_mul, ZeroMemClass.coe_eq_zero, false_or, ZeroMemClass.coe_zero, denom_zero,
            isUnit_one, IsUnit.dvd, num_zero, dvd_refl, zero_mem, not_true_eq_false]
        exact le_trans (Polynomial.natDegree_le_of_dvd h_dvd_coeff.right hcoeff_j)
          (natDegree_le_natDegree_swap φ j)
    rw [bivarR_natDegree g h (RatFunc.isCoprime_num_denom θ) (height_pos_of_not_mem_bot θ hj)]
    omega
  convert primitive_swap_degree_finish (bivarR g h) φ S _ _ hS _ hS0 hdx using 1
  · rw [bivarR_natDegree g h (RatFunc.isCoprime_num_denom θ) (height_pos_of_not_mem_bot θ hj)]
    rfl
  · rw [hφdeg, Polynomial.natDegree_map_of_leadingCoeff_ne_zero]
    simp_all only [natDegree_map, isUnit_iff_ne_zero, ne_eq, Bivariate.swap_apply, AlgHom.coe_comp,
      AlgHom.coe_restrictScalars', coe_aeval_eq_eval, Function.comp_apply, IntermediateField.algebraMap_apply,
      ZeroMemClass.coe_eq_zero, leadingCoeff_eq_zero, θ, F, t, g, h]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [coeff_zero, ZeroMemClass.coe_zero, zero_mem, not_true_eq_false]
  · apply bivarR_isPrimitive g h (RatFunc.isCoprime_num_denom θ) (height_pos_of_not_mem_bot θ hj)
  · exact bivarR_swap g h
  · exact hφprim.ne_zero

/-- Over any intermediate field `M`, the degree of `RatFunc k` equals the degree of the
minimal polynomial of the generator `RatFunc.X`. -/
theorem finrank_eq_minpoly_natDegree (M : IntermediateField k (RatFunc k))
    [FiniteDimensional M (RatFunc k)] :
    Module.finrank M (RatFunc k) = (minpoly M (RatFunc.X : RatFunc k)).natDegree := by
  have hX : IsIntegral M (RatFunc.X : RatFunc k) := IsIntegral.of_finite M _
  convert IntermediateField.adjoin.finrank hX
  rw [show (M⟮(RatFunc.X : RatFunc k)⟯ : IntermediateField M (RatFunc k)) = ⊤ from ?_]
  · simp [Module.finrank]
  · have hk : IntermediateField.adjoin k {(RatFunc.X : RatFunc k)} = ⊤ := adjoin_X_top
    simp_all [IntermediateField.adjoin]
    simp_all [SetLike.ext_iff, Subfield.mem_closure]
    intro x S hS
    specialize hk x S
    simp_all [Set.insert_subset_iff, Set.range_subset_iff]
    apply hk
    intro y
    simpa using S.mul_mem (hS.2 _ <| IntermediateField.algebraMap_mem _ y) (S.one_mem)

/-
**Lüroth's theorem.** Every intermediate field of `k(X) / k` other than `k` itself is
generated by a single element.
-/
theorem luroth (M : IntermediateField k (RatFunc k)) (hM : M ≠ ⊥) :
    ∃ w : RatFunc k, M = IntermediateField.adjoin k {w} := by
  revert hM M
  intro M hM_ne_bot
  obtain ⟨w, hw⟩ :
      ∃ w : RatFunc k, w ∈ M ∧ w ∉ (⊥ : IntermediateField k (RatFunc k)) ∧
        Module.finrank (↥k⟮w⟯) (RatFunc k) = Module.finrank (↥M) (RatFunc k) := by
    obtain ⟨j, hj⟩ :
        ∃ j, ((minpoly M (RatFunc.X : RatFunc k)).coeff j : RatFunc k) ∈ M ∧
          ((minpoly M (RatFunc.X : RatFunc k)).coeff j : RatFunc k) ∉ (⊥ : IntermediateField k (RatFunc k)) := by
      convert exists_coeff_not_mem_bot M hM_ne_bot using 1
      · ext
        simp
      · convert RatFunc.finiteDimensional_of_ne_bot M hM_ne_bot
    refine ⟨_, hj.1, hj.2, le_antisymm ?_ ?_⟩
    · convert height_coeff_le M j hj.2 using 1
      · convert finrank_adjoin_eq_height _ hj.2 using 1
      · convert finrank_eq_minpoly_natDegree M
        convert finiteDimensional_of_ne_bot M hM_ne_bot
      · convert RatFunc.finiteDimensional_of_ne_bot M hM_ne_bot
    · have h_sub_le : k⟮((minpoly M (RatFunc.X : RatFunc k)).coeff j : RatFunc k)⟯ ≤ M := by
        simp
      have h_fd : FiniteDimensional (↥k⟮((minpoly M (RatFunc.X : RatFunc k)).coeff j : RatFunc k)⟯) (RatFunc k) := by
        apply finiteDimensional_of_ne_bot
        simp_all
      exact finrank_le_of_le_left h_sub_le
  have h_le : k⟮w⟯ ≤ M := by
    simp_all
  have h_eq : k⟮w⟯ = M := by
    convert IntermediateField.eq_of_le_of_finrank_eq' h_le hw.2.2
    convert finiteDimensional_of_ne_bot _ _
    simp_all
  exact ⟨w, h_eq.symm⟩

end RatFunc
