import Mathlib

/-!
# Sublinear count of integer points on a smooth non-polynomial arc (with decay rate)

This file proves the honest, provable form of the one-variable Bombieri–Pila / Jarník
sparsity estimate that is needed as the analytic input `graph_integer_points_sublinear`
in `InverseGalois/Hilbert/Analytic/DorgeBauer.lean`.

## The statement and why a decay rate is needed

For `f : ℝ → ℝ` that is `Cᵏ` on `[1, ∞)` (`k ≥ 2`) with `iteratedDerivWithin k f`
**strictly** monotone, the set of integers `1 ≤ t ≤ N` at which `f` takes an integer value
grows sublinearly.

Fortunately this is exactly what the real Puiseux branches of an algebraic function at
infinity satisfy: their `k`-th derivative behaves like `c · x^{r-k}`, a genuine power law.
So we add the hypothesis `|f⁽ᵏ⁾(x)| ≤ C₀ · x^(-β)` (`β > 0`); the branches feeding
`int_root_locus_large_cover` all satisfy it.

* **Divided differences.**  For `k+1` integer nodes `t₀ < … < t_k` at which `f` is
  integer-valued, the leading coefficient `d` of the degree-`≤k` Lagrange interpolant is
  the `k`-th divided difference.  Times the product of all pairwise differences it is an
  integer (`ddiff_mul_prod_isInt`), and by the mean value theorem for divided differences
  (iterated Rolle) it equals `f⁽ᵏ⁾(ξ)/k!` for some `ξ` in the hull (`exists_ddiff_eq`).
* **Per block.**  On a sub-block `[a, a+H]` on which `H^{k(k+1)} · sup|f⁽ᵏ⁾| < k!`, every
  such `d` is an integer of absolute value `< 1`, hence `0`; so all integer points of the
  block lie on one polynomial of degree `< k`.  Since `f⁽ᵏ⁾` has at most one zero (strict
  monotonicity), iterated Rolle bounds the number of such points by `k + 1`
  (`block_card_le`).
* **Counting.**  Choosing `H(a) = c · a^{β/(k(k+1))}` and summing over dyadic sub-blocks
  gives `O(N^{1-β/(k(k+1))})` (`count_of_block_bound`), which is `O(Nᵅ)` for
  `α = max (1 - β/(k(k+1))) (1/2) < 1`. -/

open Set Filter Polynomial
open scoped BigOperators

namespace IntegerPointsSublinear

/-- The set of integers `1 ≤ t ≤ N` at which `f` takes an integer value. -/
def goodSet (f : ℝ → ℝ) (N : ℕ) : Set ℤ :=
  {t : ℤ | (1 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (N : ℝ) ∧ ∃ m : ℤ, f (t : ℝ) = (m : ℝ)}

/-! ### Iterated derivative of a polynomial -/

/-
The `n`-th derivative of the evaluation of a polynomial is the evaluation of the
`n`-fold formal derivative.
-/
lemma iteratedDeriv_polynomial_eval (p : ℝ[X]) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun x => p.eval x) x = (((⇑derivative)^[n]) p).eval x := by
  induction' n with n ih generalizing x
  · rfl
  · rw [iteratedDeriv_succ]
    rw [show iteratedDeriv n _ = _ from funext ih]
    norm_num [Function.iterate_succ_apply']

/-
For a polynomial `p` of degree `≤ k`, the `k`-th derivative of its evaluation is the
constant `k! · p.coeff k`.
-/
lemma iteratedDeriv_eval_top (p : ℝ[X]) (k : ℕ) (hp : p.natDegree ≤ k) (x : ℝ) :
    iteratedDeriv k (fun x => p.eval x) x = (k.factorial : ℝ) * p.coeff k := by
  rw [iteratedDeriv_polynomial_eval]
  rw [Polynomial.eval]
  rw [Polynomial.eval₂_eq_sum_range']
  case n => exact 1
  · simp [Polynomial.coeff_iterate_derivative, Nat.descFactorial_self]
  · exact lt_of_le_of_lt (Polynomial.natDegree_le_of_degree_le <|
      Polynomial.degree_le_of_natDegree_le <| Polynomial.natDegree_iterate_derivative p k) (by omega)

/-! ### Iterated Rolle -/

/-
**Iterated Rolle.**  A function that is `Cⁿ` on `[a,b]` and vanishes at `n+1` strictly
increasing points of `[a,b]` has a point in `(a,b)` at which its `n`-th derivative
vanishes.
-/
lemma exists_iteratedDeriv_eq_zero (n : ℕ) (hn : 1 ≤ n) (g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hg : ContDiffOn ℝ n g (Set.Icc a b))
    (z : Fin (n + 1) → ℝ) (hz_mono : StrictMono z) (hz_mem : ∀ i, z i ∈ Set.Icc a b)
    (hz_zero : ∀ i, g (z i) = 0) :
    ∃ ξ ∈ Set.Ioo a b, iteratedDeriv n g ξ = 0 := by
  induction' n with n ih generalizing g a b
  · grind
  · by_cases hn : 1 ≤ n
    · obtain ⟨w, hw_mono, hw_mem, hw_zero⟩ : ∃ w : Fin (n + 1) → ℝ, StrictMono w ∧ (∀ i : Fin (n + 1),
        w i ∈ Ioo a b) ∧ (∀ i : Fin (n + 1), deriv g (w i) = 0) := by
        have h_rolle : ∀ i : Fin (n + 1), ∃ w ∈ Set.Ioo (z i.castSucc) (z i.succ), deriv g w = 0 := by
          intro i
          apply_mod_cast exists_deriv_eq_zero <;> try linarith [hz_mono i.castSucc_lt_succ]
          · exact hg.continuousOn.mono (Set.Icc_subset_Icc (hz_mem _ |>.1) (hz_mem _ |>.2))
          · rw [hz_zero, hz_zero]
        choose w hw₁ hw₂ using h_rolle
        refine ⟨w, ?_, ?_, hw₂⟩
        · intro i j hij
          exact lt_of_lt_of_le (hw₁ i |>.2) (le_of_lt (hw₁ j |>.1) |>
            le_trans (hz_mono.monotone (Nat.succ_le_of_lt hij)))
        · exact fun i ↦ ⟨by linarith [Set.mem_Ioo.mp (hw₁ i), Set.mem_Icc.mp (hz_mem (Fin.castSucc i))],
            by linarith [Set.mem_Ioo.mp (hw₁ i), Set.mem_Icc.mp (hz_mem (Fin.succ i))]⟩
      specialize ih hn (deriv g) (w 0) (w (Fin.last n)) ?_ ?_ w hw_mono ?_ hw_zero
      · exact hw_mono (Nat.zero_lt_of_lt hn)
      · have h_cont_diff : ContDiffOn ℝ (n + 1) g (Set.Ioo a b) :=
          hg.mono Set.Ioo_subset_Icc_self
        have h_cont_diff' : ContDiffOn ℝ n (deriv g) (Set.Ioo a b) :=
          h_cont_diff.deriv_of_isOpen isOpen_Ioo (by norm_num)
        exact h_cont_diff'.mono (Set.Icc_subset_Ioo (hw_mem 0 |>.1) (hw_mem (Fin.last n) |>.2))
      · exact fun i ↦ ⟨hw_mono.monotone (Nat.zero_le _), hw_mono.monotone (Fin.le_last _)⟩
      · obtain ⟨ξ, hξ₁, hξ₂⟩ := ih
        use ξ
        simp_all [iteratedDeriv_succ']
        constructor <;> linarith [hw_mem 0, hw_mem (Fin.last n)]
    · interval_cases n
      simp_all [iteratedDeriv_succ']
      obtain ⟨c, hc_mem, hc⟩ := exists_deriv_eq_zero (show z 0 < z 1 from hz_mono (by decide))
        (hg.continuousOn.mono (Set.Icc_subset_Icc (by linarith) (by linarith))) (by aesop)
      refine ⟨c, ⟨?_, ?_⟩, hc⟩
      · linarith [hc_mem.1]
      · linarith [hc_mem.2]

/-! ### The `k`-th divided difference via Lagrange interpolation -/

/-- The `k`-th divided difference of `f` at the nodes `s` (`s.card = k+1`): the leading
coefficient of the degree-`≤k` interpolating polynomial. -/
noncomputable def ddiff (s : Finset ℝ) (f : ℝ → ℝ) : ℝ :=
  (Lagrange.interpolate s id f).coeff (s.card - 1)

/-
**Integrality of the (scaled) divided difference.**  If the nodes are integers and the
values `f (tᵢ)` are integers, then the divided difference times the product of all ordered
pairwise differences of the nodes is an integer.
-/
lemma ddiff_mul_prod_isInt (t : Fin (k + 1) → ℤ) (ht : Function.Injective t)
    (f : ℝ → ℝ) (hf : ∀ i, ∃ m : ℤ, f ((t i : ℝ)) = (m : ℝ)) :
    ∃ z : ℤ, ddiff (Finset.image (fun i => ((t i : ℤ) : ℝ)) Finset.univ) f *
        (∏ p ∈ (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))).filter (fun p => p.1 ≠ p.2),
          ((t p.1 : ℝ) - (t p.2 : ℝ))) = (z : ℝ) := by
  -- Expand `ddiff` as an explicit sum:
  have h_ddiff : ddiff (Finset.image (fun i : Fin (k + 1) ↦ (t i : ℝ)) Finset.univ) f =
      ∑ i : Fin (k + 1), (f (t i : ℝ)) * (1 / (∏ j ∈ Finset.univ.erase i,
      ((t i : ℝ) - (t j : ℝ)))) := by
    unfold ddiff Lagrange.interpolate
    simp [Finset.card_image_of_injective _ (show Function.Injective (fun i : Fin (k + 1) ↦ (t i : ℝ)) from
      fun i j hij ↦ ht <| by simpa using hij)]
    rw [Finset.sum_image <| fun i hi j hj hij ↦ ht <| by simpa using hij]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    apply congr_arg
    have hinj : Function.Injective (fun i : Fin (k + 1) ↦ (t i : ℝ)) :=
      fun i j hij ↦ ht <| by simpa using hij
    have hvs : Set.InjOn id (↑(Finset.image (fun i : Fin (k + 1) ↦ (t i : ℝ)) Finset.univ) : Set ℝ) :=
      fun x _ y _ h ↦ h
    have hi' : (↑(t i) : ℝ) ∈ Finset.image (fun i : Fin (k + 1) ↦ (t i : ℝ)) Finset.univ :=
      Finset.mem_image_of_mem _ hi
    convert Lagrange.leadingCoeff_basis hvs hi' using 1
    · convert Polynomial.coeff_natDegree using 1
      convert rfl
      rw [Lagrange.natDegree_basis hvs hi']
      norm_num [Finset.card_image_of_injective _ hinj]
    · refine congr_arg _ (Finset.prod_bij (fun j hj ↦ (t j : ℝ)) ?_ ?_ ?_ ?_) <;> simp [ht.eq_iff]
      refine fun b hb x hx ↦ ⟨x, ?_, hx⟩
      rintro rfl
      exact hb hx.symm
  choose m hm using hf
  -- Rewrite the product over off-diagonal pairs as a double product over `i` and `j ≠ i`.
  have h_prod : ∏ p ∈ Finset.univ.filter (fun p : Fin (k + 1) × Fin (k + 1) ↦ p.1 ≠ p.2), ((t p.1 : ℝ) - (t p.2 : ℝ)) =
      ∏ i : Fin (k + 1), ∏ j ∈ Finset.univ.erase i, ((t i : ℝ) - (t j : ℝ)) := by
    rw [Finset.prod_sigma']
    refine Finset.prod_bij (fun p hp ↦ ⟨p.1, p.2⟩) ?_ ?_ ?_ ?_ <;> aesop
  use ∑ i : Fin (k + 1), m i * ∏ j ∈ Finset.univ.erase i, ∏ k ∈ Finset.univ.erase j, (t j - t k)
  simp_all [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [mul_assoc, inv_mul_eq_div, div_eq_mul_inv]
  rw [← Finset.prod_erase_mul _ _ hi, mul_assoc,
    mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun j hj ↦ sub_ne_zero_of_ne <| mod_cast ht.ne <| by aesop), mul_one]

/-
**Mean value theorem for divided differences.**  For `f` that is `Cᵏ` on `[a,b]` and
`k+1` strictly increasing nodes in `[a,b]`, the `k`-th divided difference equals
`f⁽ᵏ⁾(ξ) / k!` for some `ξ ∈ (a,b)`.
-/
lemma exists_ddiff_eq (k : ℕ) (hk : 1 ≤ k) (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContDiffOn ℝ k f (Set.Icc a b))
    (t : Fin (k + 1) → ℝ) (ht_mono : StrictMono t) (ht_mem : ∀ i, t i ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo a b,
      ddiff (Finset.image t Finset.univ) f * (k.factorial : ℝ) = iteratedDeriv k f ξ := by
  -- The `k`-th derivative of `L` is `k! * L.coeff k`.
  set L : Polynomial ℝ := Lagrange.interpolate (Finset.image t Finset.univ) id f
  have hL_deriv : ∀ x ∈ Set.Ioo a b, iteratedDeriv k (fun x ↦ L.eval x) x = k.factorial * L.coeff k := by
    intro x hx
    rw [iteratedDeriv_eval_top]
    have hL_deg : L.natDegree ≤ k := by
      have hL_card : (Finset.image t Finset.univ).card = k + 1 := by
        rw [Finset.card_image_of_injective _ ht_mono.injective, Finset.card_fin]
      convert Polynomial.natDegree_le_of_degree_le (Lagrange.degree_interpolate_le _ _) using 1
      · aesop
      · exact fun x hx y hy hxy ↦ hxy
    exact hL_deg
  -- By iterated Rolle, there is a point `ξ ∈ (a, b)` with `g⁽ᵏ⁾(ξ) = 0`.
  obtain ⟨ξ, hξ⟩ : ∃ ξ ∈ Set.Ioo a b, iteratedDeriv k (fun x ↦ f x - L.eval x) ξ = 0 := by
    have hcd : ContDiffOn ℝ k (fun x ↦ f x - L.eval x) (Set.Icc a b) := by
      apply hf.sub
      refine ContDiff.contDiffOn ?_
      simpa only [Polynomial.eval_eq_sum_range] using
        ContDiff.sum fun i hi ↦ ContDiff.mul contDiff_const (contDiff_id.pow i)
    apply exists_iteratedDeriv_eq_zero k hk (fun x ↦ f x - L.eval x) a b hab hcd t ht_mono ht_mem
    simp +zetaDelta at *
    intro i
    rw [Polynomial.eval_finset_sum, Finset.sum_eq_single (t i)] <;> simp [Lagrange.basis]
    · simp [Polynomial.eval_prod, Lagrange.basisDivisor]
      rw [Finset.prod_eq_one fun x hx ↦ by
        rw [inv_mul_cancel₀]
        refine sub_ne_zero_of_ne ?_
        intro h
        have := Finset.mem_erase.mp hx
        aesop]
      ring
    · intro j hj
      rw [Polynomial.eval_prod]
      refine Or.inr <| Finset.prod_eq_zero
        (Finset.mem_erase_of_ne_of_mem (Ne.symm hj) <| Finset.mem_image_of_mem _ <|
          Finset.mem_univ _) ?_
      simp [Lagrange.basisDivisor]
  -- The `k`-th derivative of `g` is `f⁽ᵏ⁾(ξ) - L⁽ᵏ⁾(ξ)`.
  have hg_deriv : iteratedDeriv k (fun x ↦ f x - L.eval x) ξ =
      iteratedDeriv k f ξ - iteratedDeriv k (fun x ↦ L.eval x) ξ := by
    apply iteratedDeriv_sub
    · exact hf.contDiffAt (Icc_mem_nhds hξ.1.1 hξ.1.2)
    · simp +zetaDelta at *
      simp [Polynomial.eval_finset_sum]
      refine ContDiffAt.sum fun i hi ↦ ?_
      apply ContDiffAt.mul <;> norm_num [Polynomial.eval_eq_sum_range]
      · exact contDiffAt_const
      · exact ContDiffAt.sum fun _ _ ↦ ContDiffAt.mul (contDiffAt_const) (contDiffAt_id.pow _)
  simp_all [ddiff]
  simp +zetaDelta at *
  refine ⟨ξ, hξ.1, ?_⟩
  rw [Finset.card_image_of_injective _ ht_mono.injective]
  norm_num [Finset.card_univ]
  linarith [hL_deriv ξ hξ.1.1 hξ.1.2]

/-
**Two distinct zeros of the `n`-th derivative from `n+2` zeros.**  A counting form of
iterated Rolle: a function that is `Cⁿ` on `[a,b]` and vanishes at `n+2` strictly
increasing points of `[a,b]` has (at least) two *distinct* points in `(a,b)` at which its
`n`-th derivative vanishes.
-/
lemma exists_two_iteratedDeriv_eq_zero (n : ℕ) (hn : 1 ≤ n) (g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hg : ContDiffOn ℝ n g (Set.Icc a b))
    (z : Fin (n + 2) → ℝ) (hz_mono : StrictMono z) (hz_mem : ∀ i, z i ∈ Set.Icc a b)
    (hz_zero : ∀ i, g (z i) = 0) :
    ∃ ξ₁ ξ₂, ξ₁ ∈ Set.Ioo a b ∧ ξ₂ ∈ Set.Ioo a b ∧ ξ₁ ≠ ξ₂ ∧
      iteratedDeriv n g ξ₁ = 0 ∧ iteratedDeriv n g ξ₂ = 0 := by
  induction' n, hn using Nat.le_induction with n hn ih generalizing g a b
  · simp_all [iteratedDeriv_eq_iterate]
    -- Between any two zeros of `g` there is a zero of `g'`.
    have h_rolle : ∀ i j : Fin 3, i < j → ∃ ξ ∈ Set.Ioo (z i) (z j), deriv g ξ = 0 := by
      intros i j hij
      apply_mod_cast exists_deriv_eq_zero <;> try linarith [hz_mono hij]
      · exact hg.continuousOn.mono (Set.Icc_subset_Icc (hz_mem i |>.1) (hz_mem j |>.2))
      · rw [hz_zero i, hz_zero j]
    obtain ⟨ξ₁, hξ₁₁, hξ₁₂⟩ := h_rolle 0 1 (by decide)
    obtain ⟨ξ₂, hξ₂₁, hξ₂₂⟩ := h_rolle 1 2 (by decide)
    refine ⟨ξ₁, ⟨?_, ?_⟩, ξ₂, ⟨?_, ?_⟩, ?_, hξ₁₂, hξ₂₂⟩
    · linarith [hz_mem 0, hz_mem 1, hξ₁₁.1]
    · linarith [hz_mem 0, hz_mem 1, hξ₁₁.2]
    · linarith [hz_mem 1, hz_mem 2, hξ₂₁.1]
    · linarith [hz_mem 1, hz_mem 2, hξ₂₁.2]
    · linarith [hξ₁₁.1, hξ₁₁.2, hξ₂₁.1, hξ₂₁.2]
  · obtain ⟨w, hw⟩ : ∃ w : Fin (n + 2) → ℝ, StrictMono w ∧ (∀ i, w i ∈ Set.Ioo a b) ∧ (∀ i, deriv g (w i) = 0) := by
      have h_rolle : ∀ i : Fin (n + 2), ∃ w_i ∈ Set.Ioo (z i.castSucc) (z i.succ), deriv g w_i = 0 := by
        intro i
        apply_mod_cast exists_deriv_eq_zero <;> try linarith [hz_mono i.castSucc_lt_succ]
        · exact hg.continuousOn.mono (Set.Icc_subset_Icc (hz_mem _ |>.1) (hz_mem _ |>.2))
        · rw [hz_zero, hz_zero]
      choose w hw using h_rolle
      refine ⟨w, ?_, ?_, ?_⟩
      · intro i j hij
        exact lt_of_lt_of_le (hw i |>.1.2) (le_of_lt (hw j |>.1.1) |>
          le_trans (hz_mono.monotone (Nat.succ_le_of_lt hij)))
      · grind +qlia
      · exact fun i ↦ hw i |>.2
    specialize ih (deriv g) (w 0) (w (Fin.last _)) ?_ ?_ w hw.1 ?_ hw.2.2
    · exact hw.1 (Nat.zero_lt_succ _)
    · have h_cont_diff : ContDiffOn ℝ (n + 1) g (Set.Ioo a b) :=
        hg.mono Set.Ioo_subset_Icc_self
      exact (h_cont_diff.deriv_of_isOpen isOpen_Ioo (by norm_num)).mono
        (Set.Icc_subset_Ioo (hw.2.1 0 |>.1) (hw.2.1 (Fin.last _) |>.2))
    · exact fun i ↦ ⟨hw.1.monotone (Nat.zero_le _), hw.1.monotone (Fin.le_last _)⟩
    · obtain ⟨ξ₁, ξ₂, hξ₁, hξ₂, hne, h₁, h₂⟩ := ih
      use ξ₁, ξ₂
      simp_all [iteratedDeriv_succ']
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · linarith [hw.2.1 0]
      · linarith [hw.2.1 (Fin.last _)]
      · linarith [hw.2.1 0]
      · linarith [hw.2.1 (Fin.last _)]

/-
**The `k`-th divided difference vanishes on a small block.**  For `k+1` strictly
increasing integer nodes lying in `[a, a+H]` at which `f` is integer-valued, the smallness
of `f⁽ᵏ⁾` forces the `k`-th divided difference to be `0`: it is an integer (after scaling by
the product of pairwise differences, `ddiff_mul_prod_isInt`) of absolute value `< 1` (by
`exists_ddiff_eq` and `hsmall`).
-/
lemma block_ddiff_zero (f : ℝ → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hf : ContDiffOn ℝ k f (Set.Ici (1 : ℝ)))
    (a H : ℝ) (ha : 1 ≤ a)
    (hsmall : ∀ x ∈ Set.Icc a (a + H),
      |iteratedDerivWithin k f (Set.Ici 1) x| * H ^ (k * (k + 1)) < (k.factorial : ℝ))
    (p : Fin (k + 1) → ℤ) (hp_mono : StrictMono p)
    (hp_mem : ∀ i, a ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ a + H)
    (hp_int : ∀ i, ∃ m : ℤ, f ((p i : ℤ) : ℝ) = (m : ℝ)) :
    ddiff (Finset.image (fun i => ((p i : ℤ) : ℝ)) Finset.univ) f = 0 := by
  obtain ⟨z, hz⟩ : ∃ z : ℤ, ddiff (Finset.image (fun i ↦ ((p i : ℤ) : ℝ)) Finset.univ) f *
      (∏ p' ∈ (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))).filter (fun p' ↦ p'.1 ≠ p'.2),
        ((p p'.1 : ℝ) - (p p'.2 : ℝ))) = (z : ℝ) := by
          exact ddiff_mul_prod_isInt p hp_mono.injective f hp_int
  -- `|d| = |iteratedDeriv k f ξ| / k!`.
  obtain ⟨ξ, hξ⟩ : ∃ ξ ∈ Set.Ioo ((p 0 : ℝ)) ((p (Fin.last k) : ℝ)),
      ddiff (Finset.image (fun i ↦ ((p i : ℤ) : ℝ)) Finset.univ) f * (k.factorial : ℝ) = iteratedDeriv k f ξ := by
    convert exists_ddiff_eq k (by linarith) f (p 0 : ℝ) (p (Fin.last k) : ℝ) _ _ _ _ _ using 1
    · exact_mod_cast hp_mono (Nat.zero_lt_of_lt hk)
    · exact hf.mono (Set.Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.2 <| by linarith [hp_mem 0]))
    · exact fun i j hij ↦ Int.cast_lt.mpr (hp_mono hij)
    · exact fun i ↦ ⟨mod_cast hp_mono.monotone (Nat.zero_le _), mod_cast hp_mono.monotone (Fin.le_last _)⟩
  -- `|P| ≤ H ^ (k * (k + 1))`.
  have hP_bound : |∏ p' ∈ (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))).filter (fun p' ↦ p'.1 ≠ p'.2),
      ((p p'.1 : ℝ) - (p p'.2 : ℝ))| ≤ H ^ (k * (k + 1)) := by
    rw [Finset.abs_prod]
    have hbd : ∀ p' ∈ (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))).filter (fun p' ↦ p'.1 ≠ p'.2),
        |(p p'.1 : ℝ) - p p'.2| ≤ H := by
      intro p' _
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith [hp_mem p'.1, hp_mem p'.2]
    refine le_trans (Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) hbd) ?_
    norm_num [Finset.filter_not, Finset.card_sdiff]
    have hfilter : (Finset.univ.filter fun a : Fin (k + 1) × Fin (k + 1) ↦ a.1 = a.2) =
        Finset.image (fun i : Fin (k + 1) ↦ (i, i)) Finset.univ := by
      ext ⟨i, j⟩
      aesop
    rw [hfilter]
    rw [Finset.card_image_of_injective _ fun i j hij ↦ by simpa using hij]
    norm_num [Nat.succ_mul]
  -- `|z| < 1`.
  have hz_lt_one : |(z : ℝ)| < 1 := by
    have hderiv_lt : |iteratedDeriv k f ξ| * H ^ (k * (k + 1)) < k.factorial := by
      convert hsmall ξ ⟨by linarith [hξ.1.1, hp_mem 0], by linarith [hξ.1.2, hp_mem (Fin.last k)]⟩ using 1
      rw [iteratedDerivWithin_eq_iteratedDeriv]
      · exact uniqueDiffOn_Ici _
      · exact hf.contDiffAt (Ici_mem_nhds <| by linarith [hξ.1.1, hp_mem 0])
      · exact Set.mem_Ici.mpr (by linarith [hξ.1.1, hp_mem 0])
    rw [← hz, abs_mul]
    rw [← hξ.2, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k.factorial)] at *
    nlinarith [show (k.factorial : ℝ) > 0 by positivity,
      mul_le_mul_of_nonneg_left hP_bound <|
        show (0 : ℝ) ≤ |ddiff (Finset.image (fun i : Fin (k + 1) ↦ (p i : ℝ)) Finset.univ) f| by positivity]
  norm_cast at hz_lt_one
  simp_all [Finset.prod_eq_zero_iff, sub_eq_zero, hp_mono.injective.eq_iff]

/-
**`k+2` block points lie on a common polynomial of degree `< k`.**  Every `k+1`-subset
has vanishing `k`-th divided difference (`block_ddiff_zero`), so the Lagrange interpolant
`Q` of the first `k+1` points has degree `< k`, and each remaining point lies on `Q` by
uniqueness of low-degree interpolation.
-/
set_option maxHeartbeats 1000000 in
lemma block_common_poly (f : ℝ → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hf : ContDiffOn ℝ k f (Set.Ici (1 : ℝ)))
    (a H : ℝ) (ha : 1 ≤ a)
    (hsmall : ∀ x ∈ Set.Icc a (a + H),
      |iteratedDerivWithin k f (Set.Ici 1) x| * H ^ (k * (k + 1)) < (k.factorial : ℝ))
    (p : Fin (k + 2) → ℤ) (hp_mono : StrictMono p)
    (hp_mem : ∀ i, a ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ a + H)
    (hp_int : ∀ i, ∃ m : ℤ, f ((p i : ℤ) : ℝ) = (m : ℝ)) :
    ∃ Q : Polynomial ℝ, Q.natDegree < k ∧ ∀ i, f ((p i : ℤ) : ℝ) = Q.eval ((p i : ℤ) : ℝ) := by
  have hQ : ∀ (q : Fin (k + 1) → ℤ), StrictMono q → (∀ i, a ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ a + H) →
      (∀ i, ∃ m : ℤ, f ((q i : ℤ) : ℝ) = (m : ℝ)) →
      ∃ Q : Polynomial ℝ, Q.natDegree < k ∧ ∀ i : Fin (k + 1), f ((q i : ℤ) : ℝ) = Q.eval ((q i : ℤ) : ℝ) := by
    intros q hq_mono hq_mem hq_int
    set Q := Lagrange.interpolate (Finset.image (fun i ↦ ((q i : ℤ) : ℝ)) Finset.univ) id f with hQ_def
    have hQ_deg : Q.natDegree < k := by
      have hQ_coeff : Q.coeff k = 0 := by
        convert block_ddiff_zero f k hk hf a H ha hsmall q hq_mono hq_mem hq_int using 1
        rw [show ddiff (Finset.image (fun i : Fin (k + 1) ↦ (q i : ℝ)) Finset.univ) f =
          Q.coeff (Finset.card (Finset.image (fun i : Fin (k + 1) ↦ (q i : ℝ)) Finset.univ) - 1) from rfl]
        rw [Finset.card_image_of_injective _ fun i j hij ↦ by simpa [hq_mono.injective.eq_iff] using hij]
        simp [Finset.card_univ]
      have hQ_degle : Q.degree ≤ k := by
        convert Lagrange.degree_interpolate_le _ _
        · rw [Finset.card_image_of_injective _ fun i j hij ↦ by simpa [hq_mono.injective.eq_iff] using hij]
          simp
        · exact fun x hx y hy hxy ↦ hxy
      refine lt_of_le_of_ne (Polynomial.natDegree_le_of_degree_le hQ_degle) fun h ↦ ?_
      rw [← h, Polynomial.coeff_natDegree] at hQ_coeff
      aesop
    use Q
    simp_all
    intro i
    rw [Polynomial.eval_finset_sum, Finset.sum_eq_single (q i : ℝ)] <;> simp [Lagrange.basis]
    · simp [Polynomial.eval_prod, Lagrange.basisDivisor]
      rw [Finset.prod_eq_one fun x hx ↦ by
        rw [inv_mul_cancel₀]
        exact sub_ne_zero_of_ne (by aesop)]
      ring
    · intro j hj
      right
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase_of_ne_of_mem (by aesop)
        (Finset.mem_image_of_mem _ (Finset.mem_univ i))) (by aesop)
  obtain ⟨Q1, hQ1⟩ := hQ (fun i ↦ p (Fin.castSucc i)) (hp_mono.comp Fin.strictMono_castSucc)
    (fun i ↦ hp_mem _) (fun i ↦ hp_int _)
  obtain ⟨Q2, hQ2⟩ := hQ (fun i ↦ p (Fin.succ i)) (fun i j hij ↦ hp_mono (Nat.succ_lt_succ hij))
    (fun i ↦ hp_mem _) (fun i ↦ hp_int _)
  have hQ_eq : Q1 = Q2 := by
    refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq
      (Finset.image (fun i : Fin k ↦ (p (Fin.succ (Fin.castSucc i)) : ℝ)) Finset.univ) ?_ ?_
    · rw [Finset.card_image_of_injective _ fun i j hij ↦ _] <;> norm_num [Fin.ext_iff, hp_mono.injective.eq_iff] at *
      exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt
        (lt_of_le_of_lt (Polynomial.degree_le_natDegree) (WithBot.coe_lt_coe.mpr hQ1.1))
        (lt_of_le_of_lt (Polynomial.degree_le_natDegree) (WithBot.coe_lt_coe.mpr hQ2.1)))
    · grind +extAll
  use Q1
  simp_all [Fin.forall_fin_succ]

/-! ### Per-block bound -/

/-
**At most `k+1` integer points per small block.**

If `f` is `Cᵏ` on `[1,∞)`, its `k`-th derivative has at most one zero (a consequence of
strict monotonicity), and on the block `[a, a+H]` (with `1 ≤ a`) the size of `f⁽ᵏ⁾` is so
small that `H^{k(k+1)} · sup ≤ ...` forces every `k`-th divided difference to vanish, then
`[a,a+H]` contains at most `k+1` integers at which `f` is integer-valued.
-/
lemma block_card_le (f : ℝ → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hf : ContDiffOn ℝ k f (Set.Ici (1 : ℝ)))
    (hone : ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → x ≠ y →
      iteratedDerivWithin k f (Set.Ici 1) x = 0 → iteratedDerivWithin k f (Set.Ici 1) y = 0 →
      False)
    (a H : ℝ) (ha : 1 ≤ a)
    (hsmall : ∀ x ∈ Set.Icc a (a + H),
      |iteratedDerivWithin k f (Set.Ici 1) x| * H ^ (k * (k + 1)) < (k.factorial : ℝ)) :
    {t : ℤ | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ a + H ∧ ∃ m : ℤ, f (t : ℝ) = (m : ℝ)}.ncard ≤ k + 1 := by
  contrapose! hone with h
  have h_finite : Set.Finite {t : ℤ | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ a + H ∧ ∃ m : ℤ, f (t : ℝ) = (m : ℝ)} := by
    exact Set.finite_of_ncard_pos (pos_of_gt h)
  obtain ⟨s,
    hs⟩ : ∃ s : Finset ℤ, s.card = k + 2 ∧ ∀ t ∈ s, a ≤ (t : ℝ) ∧ (t : ℝ) ≤ a + H ∧ ∃ m : ℤ, f (t : ℝ) = (m : ℝ) := by
    have := Set.Finite.exists_finset_coe h_finite
    obtain ⟨s', hs'⟩ := this
    refine Exists.elim (Finset.exists_subset_card_eq
      (by linarith [Set.ncard_coe_finset s' ▸ hs'.symm ▸ h] : k + 2 ≤ s'.card)) fun t ht ↦ ?_
    exact ⟨t, ht.2, fun x hx ↦ hs'.subset <| Finset.mem_coe.1 <| ht.1 hx⟩
  obtain ⟨p, hp_mono, hp_mem⟩ : ∃ p : Fin (k + 2) → ℤ, StrictMono p ∧ ∀ i, p i ∈ s := by
    refine ⟨fun i ↦ s.orderEmbOfFin hs.1 i, ?_, fun i ↦ ?_⟩
    · aesop_cat
    · aesop
  obtain ⟨Q, hQdeg, hQ⟩ : ∃ Q : Polynomial ℝ, Q.natDegree < k ∧ ∀ i, f ((p i : ℤ) : ℝ) = Q.eval ((p i : ℤ) : ℝ) := by
    apply block_common_poly f k hk hf a H ha hsmall p hp_mono (fun i ↦ ⟨hs.right (p i) (hp_mem i) |>.1,
      hs.right (p i) (hp_mem i) |>.2.1⟩) (fun i ↦ hs.right (p i) (hp_mem i) |>.2.2)
  obtain ⟨ξ₁, ξ₂, hξ₁, hξ₂, hξ₁ξ₂, hξ₁_zero, hξ₂_zero⟩ :
      ∃ ξ₁ ξ₂ : ℝ, ξ₁ ∈ Set.Ioo (p 0 : ℝ) (p (Fin.last (k + 1)) : ℝ) ∧
        ξ₂ ∈ Set.Ioo (p 0 : ℝ) (p (Fin.last (k + 1)) : ℝ) ∧ ξ₁ ≠ ξ₂ ∧
        iteratedDeriv k (fun x ↦ f x - Q.eval x) ξ₁ = 0 ∧ iteratedDeriv k (fun x ↦ f x - Q.eval x) ξ₂ = 0 := by
    apply exists_two_iteratedDeriv_eq_zero (n := k) (z := fun i ↦ (p i : ℝ))
    · omega
    · exact_mod_cast hp_mono (Fin.last_pos)
    · apply ContDiffOn.sub
      · exact hf.mono (Set.Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.2 <|
          mod_cast hs.2 _ (hp_mem _) |>.1.trans' ha))
      · refine ContDiff.contDiffOn ?_
        simpa only [Polynomial.eval_eq_sum_range] using
          ContDiff.sum fun i hi ↦ ContDiff.mul contDiff_const (contDiff_id.pow i)
    · exact fun i j hij ↦ Int.cast_lt.mpr (hp_mono hij)
    · exact fun i ↦ ⟨mod_cast hp_mono.monotone (Nat.zero_le _), mod_cast hp_mono.monotone (Fin.le_last _)⟩
    · aesop
  have hξ₁_sub : iteratedDeriv k (fun x ↦ f x - Q.eval x) ξ₁ =
      iteratedDeriv k f ξ₁ - iteratedDeriv k (fun x ↦ Q.eval x) ξ₁ := by
    apply iteratedDeriv_sub
    · exact hf.contDiffAt (Ici_mem_nhds <|
        by linarith [hξ₁.1, show (p 0 : ℝ) ≥ 1 by exact_mod_cast ha.trans (hs.2 _ (hp_mem 0) |>.1)])
    · simp [Polynomial.eval_eq_sum_range]
      fun_prop
  have hξ₂_sub : iteratedDeriv k (fun x ↦ f x - Q.eval x) ξ₂ =
      iteratedDeriv k f ξ₂ - iteratedDeriv k (fun x ↦ Q.eval x) ξ₂ := by
    apply iteratedDeriv_sub
    · refine hf.contDiffAt (Ici_mem_nhds ?_)
      grind +splitIndPred
    · simp [Polynomial.eval_eq_sum_range]
      exact ContDiffAt.sum fun _ _ ↦ ContDiffAt.mul (contDiffAt_const) (contDiffAt_id.pow _)
  have hξ₁_zero : iteratedDeriv k (fun x ↦ Q.eval x) ξ₁ = 0 := by
    convert iteratedDeriv_eval_top Q k (by linarith) ξ₁ using 1
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hQdeg, MulZeroClass.mul_zero]
  have hξ₂_zero : iteratedDeriv k (fun x ↦ Q.eval x) ξ₂ = 0 := by
    rw [iteratedDeriv_eval_top] <;> norm_num [hQdeg]
    · exact Or.inr <| Polynomial.coeff_eq_zero_of_natDegree_lt hQdeg
    · linarith
  use ξ₁, ξ₂
  simp_all
  refine ⟨by linarith [hs.2 (p 0) (hp_mem 0)], by linarith [hs.2 (p 0) (hp_mem 0)], ?_, ?_⟩ <;>
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici _)
        (hf.contDiffAt (Ici_mem_nhds (by linarith [hs.2 (p 0) (hp_mem 0)])))
        (by
          norm_num
          linarith [hs.2 (p 0) (hp_mem 0)])] <;>
      linarith

/-! ### Counting -/

/-
**From a per-block bound to a power-saving count.**

If `S ⊆ ℤ` has at most `B` elements in every block `[a, a + c · a^e]` (`a ≥ 1`, with
`0 < e ≤ 1`, `0 < c`), then `S ∩ [1,N]` has `O(N^{max (1-e) (1/2)})` elements.
-/
set_option maxHeartbeats 1600000 in
lemma count_of_block_bound (S : Set ℤ) (B : ℕ) (c e : ℝ) (hc : 0 < c) (he0 : 0 < e)
    (he1 : e ≤ 1)
    (hblock : ∀ a : ℝ, 1 ≤ a →
      (S ∩ {t : ℤ | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ a + c * a ^ e}).ncard ≤ B) :
    ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard (S ∩ {t : ℤ | (1 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (N : ℝ)}) : ℝ) ≤
        C * (N : ℝ) ^ α := by
  -- Set `g : ℕ → ℕ := fun m ↦ (S ∩ {t : ℤ | 1 ≤ (t:ℝ) ∧ (t:ℝ) ≤ (2^m:ℝ)}).ncard`.
  set g : ℕ → ℕ := fun m ↦ (S ∩ {t : ℤ | 1 ≤ (t : ℝ) ∧ (t : ℝ) ≤ (2 ^ m : ℝ)}).ncard
  -- Step 1: Prove the recurrence relation for `g`.
  have h_recurrence : ∀ m : ℕ, g (m + 1) ≤ g m + B * (Nat.ceil ((2 ^ m : ℝ) / (c * (2 ^ m) ^ e)) + 1) := by
    intro m
    have h_cover : (S ∩ {t : ℤ | (2 ^ m : ℝ) < (t : ℝ) ∧ (t : ℝ) ≤ (2 ^ (m + 1) : ℝ)}).ncard ≤
        B * (Nat.ceil ((2 ^ m : ℝ) / (c * (2 ^ m) ^ e)) + 1) := by
      -- Cover the interval `(2^m, 2^(m+1)]` with blocks of length `c · (2^m)^e`.
      have h_cover_sub : {t : ℤ | (2 ^ m : ℝ) < (t : ℝ) ∧ (t : ℝ) ≤ (2 ^ (m + 1) : ℝ)} ⊆
          ⋃ i ∈ Finset.range (Nat.ceil ((2 ^ m : ℝ) / (c * (2 ^ m) ^ e)) + 1),
            {t : ℤ | (2 ^ m + i * c * (2 ^ m) ^ e : ℝ) ≤ (t : ℝ) ∧
              (t : ℝ) ≤ (2 ^ m + (i + 1) * c * (2 ^ m) ^ e : ℝ)} := by
        intro t ht
        obtain ⟨ht1, ht2⟩ := ht
        have h_block : ∃ i ∈ Finset.range (Nat.ceil ((2 ^ m : ℝ) / (c * (2 ^ m) ^ e)) + 1),
            (2 ^ m + i * c * (2 ^ m) ^ e : ℝ) ≤ (t : ℝ) ∧
              (t : ℝ) ≤ (2 ^ m + (i + 1) * c * (2 ^ m) ^ e : ℝ) := by
          refine ⟨⌊(t - 2 ^ m) / (c * (2 ^ m) ^ e)⌋₊, ?_, ?_, ?_⟩ <;> norm_num
          · apply Nat.le_of_lt_succ
            rw [Nat.floor_lt', div_lt_iff₀] <;> norm_num [pow_succ'] at *
            · nlinarith [Nat.le_ceil ((2 ^ m : ℝ) / (c * (2 ^ m) ^ e)), show (0 : ℝ) < c * (2 ^ m) ^ e by positivity,
                div_mul_cancel₀ (2 ^ m : ℝ) (show (c * (2 ^ m) ^ e) ≠ 0 by positivity)]
            · positivity
          · have hnn : 0 ≤ (t - 2 ^ m : ℝ) / (c * (2 ^ m) ^ e) :=
              div_nonneg (sub_nonneg.mpr ht1.le) (by positivity)
            nlinarith [Nat.floor_le hnn, show 0 < c * (2 ^ m) ^ e by positivity,
              mul_div_cancel₀ (t - 2 ^ m : ℝ) (by positivity : (c * (2 ^ m) ^ e) ≠ 0)]
          · nlinarith [Nat.lt_floor_add_one ((t - 2 ^ m : ℝ) / (c * (2 ^ m) ^ e)),
              show 0 < c * (2 ^ m : ℝ) ^ e by positivity,
              mul_div_cancel₀ (t - 2 ^ m : ℝ) (show (c * (2 ^ m : ℝ) ^ e) ≠ 0 by positivity)]
        aesop
      -- Apply the block bound to each block in the cover.
      have h_block_bound : ∀ i ∈ Finset.range (Nat.ceil ((2 ^ m : ℝ) / (c * (2 ^ m) ^ e)) + 1),
          (S ∩ {t : ℤ | (2 ^ m + i * c * (2 ^ m) ^ e : ℝ) ≤ (t : ℝ) ∧
            (t : ℝ) ≤ (2 ^ m + (i + 1) * c * (2 ^ m) ^ e : ℝ)}).ncard ≤ B := by
        intro i hi
        refine le_trans ?_ (hblock (2 ^ m + i * c * (2 ^ m) ^ e) ?_)
        · fapply Set.ncard_le_ncard
          · intro t ht
            simp_all [add_mul, add_assoc]
            apply le_trans ht.2.2
            gcongr
            exact le_add_of_nonneg_right (by positivity)
          · refine Set.Finite.subset (Set.finite_Icc (⌈2 ^ m + i * c * (2 ^ m) ^ e⌉)
              (⌊2 ^ m + i * c * (2 ^ m) ^ e + c * (2 ^ m + i * c * (2 ^ m) ^ e) ^ e⌋)) ?_
            exact fun x hx ↦ ⟨Int.ceil_le.mpr hx.2.1, Int.le_floor.mpr hx.2.2⟩
        · exact le_add_of_le_of_nonneg (one_le_pow₀ (by norm_num)) (by positivity)
      have h_union_bound : (S ∩ ⋃ i ∈ Finset.range (Nat.ceil ((2 ^ m : ℝ) / (c * (2 ^ m) ^ e)) + 1),
          {t : ℤ | (2 ^ m + i * c * (2 ^ m) ^ e : ℝ) ≤ (t : ℝ) ∧
            (t : ℝ) ≤ (2 ^ m + (i + 1) * c * (2 ^ m) ^ e : ℝ)}).ncard ≤
          ∑ i ∈ Finset.range (Nat.ceil ((2 ^ m : ℝ) / (c * (2 ^ m) ^ e)) + 1),
            (S ∩ {t : ℤ | (2 ^ m + i * c * (2 ^ m) ^ e : ℝ) ≤ (t : ℝ) ∧
              (t : ℝ) ≤ (2 ^ m + (i + 1) * c * (2 ^ m) ^ e : ℝ)}).ncard := by
        convert Finset.set_ncard_biUnion_le _ _ using 2
        aesop
      refine le_trans ?_ (h_union_bound.trans ?_)
      · apply Set.ncard_le_ncard
        · exact fun x hx ↦ ⟨hx.1, h_cover_sub hx.2⟩
        · refine Set.Finite.subset (Set.finite_Icc
            (-⌈2 ^ m + (⌈2 ^ m / (c * (2 ^ m) ^ e)⌉₊ + 1) * c * (2 ^ m) ^ e⌉₊ : ℤ)
            ⌈2 ^ m + (⌈2 ^ m / (c * (2 ^ m) ^ e)⌉₊ + 1) * c * (2 ^ m) ^ e⌉₊) ?_
          simp [Set.subset_def]
          intro x hx i hi₁ hi₂ hi₃
          constructor <;> norm_num at *
          · refine Int.le_of_lt_add_one ?_
            rw [← @Int.cast_lt ℝ]
            push_cast
            nlinarith [Nat.le_ceil (2 ^ m + (⌈2 ^ m / (c * (2 ^ m) ^ e)⌉₊ + 1) * c * (2 ^ m) ^ e),
              show (0 : ℝ) ≤ c * (2 ^ m) ^ e by positivity, show (0 : ℝ) ≤ 2 ^ m by positivity]
          · refine Int.le_of_lt_add_one ?_
            rw [← @Int.cast_lt ℝ]
            push_cast
            nlinarith [Nat.le_ceil (2 ^ m + (⌈2 ^ m / (c * (2 ^ m) ^ e)⌉₊ + 1) * c * (2 ^ m) ^ e),
              show (i : ℝ) ≤ ⌈2 ^ m / (c * (2 ^ m) ^ e)⌉₊ by exact_mod_cast hi₂,
              show (0 : ℝ) < c * (2 ^ m) ^ e by positivity]
      · simpa [mul_comm] using Finset.sum_le_sum h_block_bound
    convert Set.ncard_union_le _ _ |> le_trans <| add_le_add_left h_cover _ using 1
    any_goals exact S ∩ {t : ℤ | 1 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 2 ^ m}
    · simp +zetaDelta at *
      congr with x
      norm_cast
      simp [pow_succ']
      grind +splitImp
    · ring!
  -- Step 2: Solve the recurrence relation for `g`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ m : ℕ, g m ≤ C * (2 ^ m : ℝ) ^ (max (1 - e) (1 / 2)) := by
    -- `⌈2^m / (c * (2^m)^e)⌉₊ + 1 ≤ C' * ((2^m)^(1-e) + 1)` for some constant `C'`.
    obtain ⟨C',
      hC'⟩ : ∃ C' : ℝ, ∀ m : ℕ, (Nat.ceil ((2 ^ m : ℝ) / (c * (2 ^ m : ℝ) ^ e)) + 1) ≤
          C' * ((2 ^ m : ℝ) ^ (1 - e) + 1) := by
      -- Bound the ceiling by `x + 1` and factor out the power.
      have h_ceil_bound : ∀ m : ℕ, (Nat.ceil ((2 ^ m : ℝ) / (c * (2 ^ m : ℝ) ^ e)) : ℝ) ≤
          (2 ^ m : ℝ) / (c * (2 ^ m : ℝ) ^ e) + 1 := by
        exact fun m ↦ le_of_lt <| Nat.ceil_lt_add_one <| by positivity
      -- `2^m / (c * (2^m)^e) = (2^m)^(1-e) / c`.
      have h_exp : ∀ m : ℕ, (2 ^ m : ℝ) / (c * (2 ^ m : ℝ) ^ e) = (2 ^ m : ℝ) ^ (1 - e) / c := by
        intro m
        rw [Real.rpow_sub (by positivity), Real.rpow_one]
        ring
      use 2 / c + 1
      intro m
      specialize h_ceil_bound m
      specialize h_exp m
      ring_nf at *
      nlinarith [inv_pos.mpr hc, mul_inv_cancel₀ hc.ne', show (1 : ℝ) ≤ 2 ^ m from one_le_pow₀ (by norm_num),
        show (2 ^ m : ℝ) ^ (1 - e) ≥ 1 from Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by linarith)]
    -- `g m ≤ C'' * (∑ i < m, (2^i)^(1-e) + m + 1)` for some constant `C''`.
    obtain ⟨C'', hC''⟩ : ∃ C'' : ℝ, ∀ m : ℕ, (g m : ℝ) ≤ C'' * (∑ i ∈ Finset.range m,
      (2 ^ i : ℝ) ^ (1 - e) + m + 1) := by
      use (g 0 + B * C') + 1
      intro m
      induction' m with m ih <;> norm_num [Finset.sum_range_succ] at *
      · refine le_add_of_le_of_nonneg (le_add_of_nonneg_right <| mul_nonneg (Nat.cast_nonneg _) ?_) zero_le_one
        have := hC' 0
        norm_num at this
        linarith
      · refine le_trans (Nat.cast_le.mpr (h_recurrence m)) ?_
        norm_num at *
        refine le_trans (add_le_add ih (mul_le_mul_of_nonneg_left (hC' m) (Nat.cast_nonneg _))) ?_
        have hC'0 : 0 ≤ C' := by
          have := hC' 0
          norm_num at this
          linarith
        nlinarith [show 0 ≤ (B : ℝ) * C' from mul_nonneg (Nat.cast_nonneg _) hC'0,
          show (2 ^ m : ℝ) ^ (1 - e) ≥ 0 by positivity]
    -- `∑ i < m, (2^i)^(1-e) ≤ C''' * (2^m)^(max (1-e) (1/2))` for some constant `C'''`.
    obtain ⟨C''', hC'''⟩ : ∃ C''' : ℝ, ∀ m : ℕ, (∑ i ∈ Finset.range m,
      (2 ^ i : ℝ) ^ (1 - e)) ≤ C''' * (2 ^ m : ℝ) ^ (max (1 - e) (1 / 2)) := by
      by_cases h_case : 1 - e ≤ 1 / 2
      · -- When `1 - e ≤ 1/2`, `∑ i < m, (2^i)^(1-e) ≤ ∑ i < m, (2^i)^(1/2)`.
        have h_sum_bound_case1 : ∀ m : ℕ, (∑ i ∈ Finset.range m, (2 ^ i : ℝ) ^ (1 - e)) ≤ (∑ i ∈ Finset.range m,
          (2 ^ i : ℝ) ^ (1 / 2 : ℝ)) := by
          exact fun m ↦ Finset.sum_le_sum fun i _ ↦
            Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) h_case
        -- `∑ i < m, (2^i)^(1/2)` is geometric with ratio `2^(1/2)`, so it is `O((2^m)^(1/2))`.
        have h_geo_series : ∃ C''' : ℝ, ∀ m : ℕ, (∑ i ∈ Finset.range m,
          (2 ^ i : ℝ) ^ (1 / 2 : ℝ)) ≤ C''' * (2 ^ m : ℝ) ^ (1 / 2 : ℝ) := by
          use 2 / (Real.sqrt 2 - 1)
          intro m
          rw [div_mul_eq_mul_div, le_div_iff₀] <;> norm_num [← Real.sqrt_eq_rpow]
          · induction m <;> norm_num [Finset.sum_range_succ, pow_succ'] at *
            nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, Real.sqrt_nonneg (2 ^ ‹_› : ℝ),
              Real.sq_sqrt (show 0 ≤ 2 ^ ‹_› by positivity)]
          · norm_num [Real.lt_sqrt]
        exact ⟨h_geo_series.choose,
          fun m ↦ le_trans (h_sum_bound_case1 m) (le_trans (h_geo_series.choose_spec m) (by rw [max_eq_right h_case]))⟩
      · -- When `1 - e > 1/2`, `∑ i < m, (2^i)^(1-e) ≤ (2^m)^(1-e) / (2^(1-e) - 1)`.
        have h_sum_bound_case2 : ∀ m : ℕ, (∑ i ∈ Finset.range m,
          (2 ^ i : ℝ) ^ (1 - e)) ≤ (2 ^ m : ℝ) ^ (1 - e) / (2 ^ (1 - e) - 1) := by
          intro m
          rw [le_div_iff₀ (sub_pos.mpr <| Real.one_lt_rpow one_lt_two <| by linarith)]
          induction' m with m ih <;> norm_num [Finset.sum_range_succ, pow_succ'] at *
          rw [Real.mul_rpow (by positivity) (by positivity)]
          linarith
        use 1 / (2 ^ (1 - e) - 1)
        intro m
        convert h_sum_bound_case2 m using 1
        rw [max_eq_left (by linarith)]
        ring
    -- `m ≤ C'''' * (2^m)^(max (1-e) (1/2))` for some constant `C''''`.
    obtain ⟨C'''', hC''''⟩ : ∃ C'''' : ℝ, ∀ m : ℕ, (m : ℝ) ≤ C'''' * (2 ^ m : ℝ) ^ (max (1 - e) (1 / 2)) := by
      use 2 / Real.log 2
      intro m
      rw [div_mul_eq_mul_div, le_div_iff₀ (Real.log_pos one_lt_two)]
      norm_num [Real.rpow_def_of_pos]
      ring_nf
      (
      have hmnn : (0 : ℝ) ≤ m * Real.log 2 * max (1 - e) (1 / 2) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)) (by positivity)
      nlinarith [Real.add_one_le_exp (m * Real.log 2 * max (1 - e) (1 / 2)), Real.log_pos one_lt_two,
        show (0 : ℝ) ≤ m * Real.log 2 by positivity, hmnn,
        show (max (1 - e) (1 / 2) : ℝ) ≥ 1 / 2 from le_max_right _ _])
    use C'' * (C''' + C'''' + 1)
    intro m
    specialize hC'' m
    specialize hC''' m
    specialize hC'''' m
    rcases lt_trichotomy C'' 0 with hC'' | rfl | hC'' <;> norm_num at *
    · nlinarith [show 0 ≤ ∑ i ∈ Finset.range m,
        (2 ^ i : ℝ) ^ (1 - e) from Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (by positivity) _,
        show 0 ≤ (m : ℝ) by positivity]
    · exact hC''
    · have h1 : (1 : ℝ) ≤ (2 ^ m) ^ max (1 - e) (1 / 2) :=
        Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)
      nlinarith [h1]
  refine ⟨Max.max C 1 * 2 ^ (Max.max (1 - e) (1 / 2)), Max.max (1 - e) (1 / 2), ?_, ?_, ?_, ?_⟩ <;> norm_num
  · positivity
  · linarith
  · intro N hN
    have h_card : (S ∩ {t : ℤ | 1 ≤ (t : ℝ) ∧ (t : ℝ) ≤ N}).ncard ≤ g (Nat.log 2 N + 1) := by
      fapply Set.ncard_le_ncard
      · exact fun x hx ↦ ⟨hx.1, hx.2.1,
          hx.2.2.trans <| mod_cast Nat.le_of_lt <| Nat.lt_pow_succ_log_self (by decide) _⟩
      · exact Set.Finite.subset (Set.finite_Icc (1 : ℤ) (2 ^ (Nat.log 2 N + 1))) fun x hx ↦ ⟨mod_cast hx.2.1,
          mod_cast hx.2.2⟩
    refine le_trans (Nat.cast_le.mpr h_card) (le_trans (hC _) ?_)
    rw [mul_assoc, ← Real.mul_rpow (by positivity) (by positivity)]
    gcongr
    · norm_num
    · exact_mod_cast by
        rw [pow_succ']
        exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hN.ne')

/-! ### Main theorem -/

/-- **Sublinear count of integer points on a smooth non-polynomial arc (with a polynomial
decay rate on `f⁽ᵏ⁾`).**

This is the honest, provable form of `graph_integer_points_sublinear`.  The hypotheses are:
`f` is `Cᵏ` on `[1,∞)`; its `k`-th derivative is strictly monotone (so it has at most one
zero and no tail of `f` is a polynomial); and `|f⁽ᵏ⁾(x)| ≤ C₀ · x^(-β)` for some `β > 0`
(a polynomial decay rate — satisfied by every real algebraic Puiseux branch at infinity).

Conclusion: the number of integers `1 ≤ t ≤ N` at which `f` is integer-valued is `O(Nᵅ)`
for some `α < 1`. -/
theorem integerValue_count_sublinear
    (f : ℝ → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hf : ContDiffOn ℝ k f (Set.Ici (1 : ℝ)))
    (hmono : StrictMonoOn (iteratedDerivWithin k f (Set.Ici 1)) (Set.Ici 1) ∨
        StrictAntiOn (iteratedDerivWithin k f (Set.Ici 1)) (Set.Ici 1))
    (C₀ β : ℝ) (hβ : 0 < β)
    (hrate : ∀ x : ℝ, 1 ≤ x → |iteratedDerivWithin k f (Set.Ici 1) x| ≤ C₀ * x ^ (-β)) :
    ∃ C α : ℝ, 0 < C ∧ 0 ≤ α ∧ α < 1 ∧ ∀ N : ℕ, 0 < N →
      (Set.ncard {t : ℤ | (1 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (N : ℝ) ∧
          ∃ m : ℤ, f (t : ℝ) = (m : ℝ)} : ℝ) ≤ C * (N : ℝ) ^ α := by
  -- `f⁽ᵏ⁾` has at most one zero, from strict monotonicity.
  have hone : ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → x ≠ y →
      iteratedDerivWithin k f (Set.Ici 1) x = 0 →
      iteratedDerivWithin k f (Set.Ici 1) y = 0 → False := by
    intro x y hx hy hxy hx0 hy0
    apply hxy
    rcases hmono with hm | hm <;>
      exact hm.injOn (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) (by rw [hx0, hy0])
  -- Positivity facts.
  set n : ℕ := k * (k + 1) with hn_def
  have hnpos : 0 < n := by
    rw [hn_def]
    positivity
  have hkk : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  set C₀' : ℝ := max C₀ 1 with hC₀'
  have hC₀'pos : 0 < C₀' := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- Exponent and width constant.
  set e : ℝ := min (β / (n : ℝ)) 1 with he_def
  have he0 : 0 < e := lt_min (by positivity) one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have hek : e * (n : ℝ) ≤ β := by
    calc e * (n : ℝ) ≤ (β / (n : ℝ)) * (n : ℝ) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (le_of_lt hkk)
      _ = β := by field_simp
  set c : ℝ := (k.factorial / (C₀' + 1)) ^ (1 / (n : ℝ)) with hc_def
  have hcpos : 0 < c := by
    apply Real.rpow_pos_of_pos
    positivity
  have hcpow : c ^ n = k.factorial / (C₀' + 1) := by
    rw [hc_def, ← Real.rpow_natCast _ n, ← Real.rpow_mul (by positivity)]
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hkk), Real.rpow_one]
  have hbound_c : C₀' * c ^ n < (k.factorial : ℝ) := by
    rw [hcpow]
    have hkfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have h1 : C₀' / (C₀' + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    calc C₀' * ((k.factorial : ℝ) / (C₀' + 1))
        = (k.factorial : ℝ) * (C₀' / (C₀' + 1)) := by ring
      _ < (k.factorial : ℝ) * 1 := mul_lt_mul_of_pos_left h1 hkfac
      _ = (k.factorial : ℝ) := by ring
  -- The (unbounded) set of integer-value points.
  set S : Set ℤ := {t : ℤ | ∃ m : ℤ, f (t : ℝ) = (m : ℝ)} with hS
  -- Per-block bound.
  have hblock : ∀ a : ℝ, 1 ≤ a →
      (S ∩ {t : ℤ | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ a + c * a ^ e}).ncard ≤ k + 1 := by
    intro a ha
    have hapos : (0 : ℝ) < a := by linarith
    have hHpos : 0 < c * a ^ e := by positivity
    have hsmall : ∀ x ∈ Set.Icc a (a + c * a ^ e),
        |iteratedDerivWithin k f (Set.Ici 1) x| * (c * a ^ e) ^ n <
          (k.factorial : ℝ) := by
      intro x hx
      have hx1 : 1 ≤ x := le_trans ha hx.1
      have hxa : a ≤ x := hx.1
      have hxpos : (0 : ℝ) < x := by linarith
      -- bound the derivative
      have hd : |iteratedDerivWithin k f (Set.Ici 1) x| ≤ C₀' * a ^ (-β) := by
        calc |iteratedDerivWithin k f (Set.Ici 1) x| ≤ C₀ * x ^ (-β) := hrate x hx1
          _ ≤ C₀' * x ^ (-β) := by
              apply mul_le_mul_of_nonneg_right (le_max_left _ _)
              positivity
          _ ≤ C₀' * a ^ (-β) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hC₀'pos)
              rw [Real.rpow_neg (le_of_lt hapos), Real.rpow_neg (le_of_lt hxpos)]
              apply inv_anti₀ (by positivity)
              exact Real.rpow_le_rpow (le_of_lt hapos) hxa (le_of_lt hβ)
      -- rewrite the width power
      have hae : (a ^ e) ^ n = a ^ (e * (n : ℝ)) := by
        rw [← Real.rpow_natCast (a ^ e) n, ← Real.rpow_mul (le_of_lt hapos)]
      have hpow : (c * a ^ e) ^ n = c ^ n * a ^ (e * (n : ℝ)) := by
        rw [mul_pow, hae]
      have haβ : a ^ (e * (n : ℝ)) ≤ a ^ β :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hek
      -- combine
      calc |iteratedDerivWithin k f (Set.Ici 1) x| * (c * a ^ e) ^ n
          = |iteratedDerivWithin k f (Set.Ici 1) x| *
              (c ^ n * a ^ (e * (n : ℝ))) := by rw [hpow]
        _ ≤ (C₀' * a ^ (-β)) * (c ^ n * a ^ β) := by
            apply mul_le_mul hd _ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left haβ (by positivity)
        _ = C₀' * c ^ n * (a ^ (-β) * a ^ β) := by ring
        _ = C₀' * c ^ n := by
            rw [← Real.rpow_add hapos]
            norm_num
        _ < (k.factorial : ℝ) := hbound_c
    have hcard := block_card_le f k hk hf hone a (c * a ^ e) ha hsmall
    calc (S ∩ {t : ℤ | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ a + c * a ^ e}).ncard
        = {t : ℤ | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ a + c * a ^ e ∧
            ∃ m : ℤ, f (t : ℝ) = (m : ℝ)}.ncard := by
          congr 1
          ext t
          simp only [hS, Set.mem_inter_iff, Set.mem_setOf_eq]
          tauto
      _ ≤ k + 1 := hcard
  obtain ⟨C, α, hC, hα0, hα1, hbound⟩ :=
    count_of_block_bound S (k + 1) c e hcpos he0 he1 hblock
  refine ⟨C, α, hC, hα0, hα1, fun N hN ↦ ?_⟩
  have hset : {t : ℤ | (1 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (N : ℝ) ∧
      ∃ m : ℤ, f (t : ℝ) = (m : ℝ)} =
      S ∩ {t : ℤ | (1 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (N : ℝ)} := by
    ext t
    simp only [hS, Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  rw [hset]
  exact hbound N hN

end IntegerPointsSublinear