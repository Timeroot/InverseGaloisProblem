import Mathlib
import InverseGalois.CFT.Global.QuaternaryForms
import InverseGalois.CFT.Global.ThreeSquaresOdd
import InverseGalois.CFT.Global.IntApprox
import InverseGalois.CFT.Global.OddUnitIsotropy
import InverseGalois.CFT.Global.OddGenerators

/-!
# The Hasse principle for diagonal forms in five variables

A diagonal form in five variables splits as a binary form against a ternary one, and is isotropic
exactly when the two halves share a nonzero value.  Whether a nonzero element is a value of a
diagonal form depends only on its square class, so at each place the shared value is a square
class, and the point of the argument is to produce a single rational number lying in the right
square class at every place of a suitable finite set while being a value of the binary half
*over the rational field itself*.

## Main results

* `InverseGalois.CFT.Local.IsQuinaryIsotropic`: a diagonal form in five variables represents zero
  nontrivially.
* `InverseGalois.CFT.Local.isQuinaryIsotropic_iff_exists_common`: such a form is isotropic exactly
  when its binary and ternary halves share a nonzero value.
* `InverseGalois.CFT.Local.exists_repr_binary_of_isSquare_div`,
  `InverseGalois.CFT.Local.exists_repr_ternary_of_isSquare_div`: the values of a diagonal form are
  a union of square classes.
* `InverseGalois.CFT.exists_rat_value_of_local`: a rational value of a diagonal binary form lying
  in a prescribed square class at each place of a finite set, and with a prescribed sign.
* `InverseGalois.CFT.isQuinaryIsotropic_rat_of_forall_local`,
  `InverseGalois.CFT.isQuinaryIsotropic_rat_iff_forall_local`: **the Hasse principle for diagonal
  forms in five variables** over the rational field.
-/

namespace InverseGalois.CFT.Local

section Values

variable {K : Type*} [Field K]

/-- The diagonal quinary form `⟨a, b, c, d, e⟩` over `K` is **isotropic** when it represents zero
at a point other than the origin. -/
def IsQuinaryIsotropic (a b c d e : K) : Prop :=
  ∃ x y z w u : K, ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 ∧ u = 0) ∧
    a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + d * w ^ 2 + e * u ^ 2 = 0

/-- **The values of a diagonal binary form are a union of square classes.** -/
theorem exists_repr_binary_of_isSquare_div {a b t s : K} (ht : t ≠ 0)
    (h : ∃ x y : K, t = a * x ^ 2 + b * y ^ 2) (hs : IsSquare (s / t)) :
    ∃ x y : K, s = a * x ^ 2 + b * y ^ 2 := by
  obtain ⟨x, y, hxy⟩ := h
  obtain ⟨c, hc⟩ := hs
  rw [div_eq_iff ht] at hc
  exact ⟨x * c, y * c, by rw [hc, hxy]; ring⟩

/-- **The values of a diagonal ternary form are a union of square classes.** -/
theorem exists_repr_ternary_of_isSquare_div {a b c t s : K} (ht : t ≠ 0)
    (h : ∃ x y z : K, t = a * x ^ 2 + b * y ^ 2 + c * z ^ 2) (hs : IsSquare (s / t)) :
    ∃ x y z : K, s = a * x ^ 2 + b * y ^ 2 + c * z ^ 2 := by
  obtain ⟨x, y, z, hxyz⟩ := h
  obtain ⟨d, hd⟩ := hs
  rw [div_eq_iff ht] at hd
  exact ⟨x * d, y * d, z * d, by rw [hd, hxyz]; ring⟩

/-- **A diagonal quinary form is isotropic exactly when its binary and ternary halves share a
nonzero value.** -/
theorem isQuinaryIsotropic_iff_exists_common (h2 : (2 : K) ≠ 0) {a b c d e : K} (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    IsQuinaryIsotropic a b c d e ↔ ∃ t : K, t ≠ 0 ∧ (∃ x y : K, t = a * x ^ 2 + b * y ^ 2) ∧
      ∃ z w u : K, t = -c * z ^ 2 + -d * w ^ 2 + -e * u ^ 2 := by
  constructor
  · rintro ⟨x, y, z, w, u, hne, hzero⟩
    rcases eq_or_ne (a * x ^ 2 + b * y ^ 2) 0 with hbin | hbin
    · by_cases hxy : x = 0 ∧ y = 0
      · obtain ⟨rfl, rfl⟩ := hxy
        have hzwu : ¬(z = 0 ∧ w = 0 ∧ u = 0) := fun hzwu =>
          hne ⟨rfl, rfl, hzwu.1, hzwu.2.1, hzwu.2.2⟩
        have hiso : -c * z ^ 2 + -d * w ^ 2 + -e * u ^ 2 = 0 := by linear_combination -hzero
        refine ⟨a, ha, ⟨1, 0, by ring⟩, ?_⟩
        exact exists_repr_of_isTernaryIsotropic h2 (neg_ne_zero.2 hc) (neg_ne_zero.2 hd)
          (neg_ne_zero.2 he) ⟨z, w, u, hzwu, hiso⟩ a
      · exact ⟨-c, neg_ne_zero.2 hc,
          exists_repr_of_binary_isotropic h2 ha hb hxy hbin (-c), ⟨1, 0, 0, by ring⟩⟩
    · exact ⟨a * x ^ 2 + b * y ^ 2, hbin, ⟨x, y, rfl⟩, ⟨z, w, u, by linear_combination hzero⟩⟩
  · rintro ⟨t, ht, ⟨x, y, hxy⟩, ⟨z, w, u, hzwu⟩⟩
    refine ⟨x, y, z, w, u, ?_, by linear_combination hzwu - hxy⟩
    rintro ⟨rfl, rfl, -, -, -⟩
    exact ht (by rw [hxy]; ring)

end Values

end InverseGalois.CFT.Local

namespace InverseGalois.CFT

open Local

/-- A power of `p` with nonpositive exponent may be increased without leaving the unit ball. -/
private theorem norm_pow_mul_le_one_of_le {p : ℕ} [Fact p.Prime] {u : ℚ_[p]} {m n : ℕ}
    (hmn : m ≤ n) (h : ‖((p : ℚ_[p])) ^ m * u‖ ≤ 1) : ‖((p : ℚ_[p])) ^ n * u‖ ≤ 1 := by
  have hp1 : ‖((p : ℚ_[p]))‖ ≤ 1 := by
    have := Padic.norm_int_le_one (p := p) ((p : ℤ))
    simpa using this
  have hfac : ((p : ℚ_[p])) ^ n * u = ((p : ℚ_[p])) ^ (n - m) * (((p : ℚ_[p])) ^ m * u) := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  calc ‖((p : ℚ_[p])) ^ n * u‖ = ‖((p : ℚ_[p])) ^ (n - m)‖ * ‖((p : ℚ_[p])) ^ m * u‖ := by
        rw [hfac, norm_mul]
    _ ≤ 1 * 1 := by
        refine mul_le_mul ?_ h (norm_nonneg _) zero_le_one
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) hp1
    _ = 1 := one_mul 1

/-- **A local value of a diagonal binary form may be taken at integral coordinates**, at the cost
of replacing the value by another one in the same square class. -/
private theorem exists_integral_repr {p : ℕ} [Fact p.Prime] {a₁ a₂ : ℚ} {t : ℚ_[p]} (ht : t ≠ 0)
    (h : ∃ x y : ℚ_[p], t = ((a₁ : ℚ_[p])) * x ^ 2 + ((a₂ : ℚ_[p])) * y ^ 2) :
    ∃ U V T : ℚ_[p], ‖U‖ ≤ 1 ∧ ‖V‖ ≤ 1 ∧ T ≠ 0 ∧ IsSquare (T / t) ∧
      T = ((a₁ : ℚ_[p])) * U ^ 2 + ((a₂ : ℚ_[p])) * V ^ 2 := by
  obtain ⟨x, y, hxy⟩ := h
  obtain ⟨n₁, hn₁⟩ := exists_pow_mul_norm_le_one x
  obtain ⟨n₂, hn₂⟩ := exists_pow_mul_norm_le_one y
  set n : ℕ := max n₁ n₂ with hn
  have hp0 : ((p : ℚ_[p])) ≠ 0 := by
    have := (Fact.out : p.Prime).pos
    exact_mod_cast Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  refine ⟨((p : ℚ_[p])) ^ n * x, ((p : ℚ_[p])) ^ n * y, ((p : ℚ_[p])) ^ (2 * n) * t,
    norm_pow_mul_le_one_of_le (le_max_left _ _) hn₁,
    norm_pow_mul_le_one_of_le (le_max_right _ _) hn₂, ?_, ?_, ?_⟩
  · exact mul_ne_zero (pow_ne_zero _ hp0) ht
  · refine ⟨((p : ℚ_[p])) ^ n, ?_⟩
    rw [two_mul, pow_add]
    field_simp
  · rw [hxy, two_mul, pow_add]
    ring

/-- **An integral approximation of the coordinates keeps the value inside its square class.** -/
private theorem isSquare_div_of_approx {p : ℕ} [Fact p.Prime] {a₁ a₂ : ℚ} {U V T : ℚ_[p]}
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (hT : T ≠ 0)
    (hTdef : T = ((a₁ : ℚ_[p])) * U ^ 2 + ((a₂ : ℚ_[p])) * V ^ 2) {X Y : ℤ}
    (hX : ‖((X : ℚ_[p])) - U‖ < ‖T‖ / (8 * p * (‖((a₁ : ℚ_[p]))‖ + ‖((a₂ : ℚ_[p]))‖ + 1)))
    (hY : ‖((Y : ℚ_[p])) - V‖ < ‖T‖ / (8 * p * (‖((a₁ : ℚ_[p]))‖ + ‖((a₂ : ℚ_[p]))‖ + 1))) :
    IsSquare ((((a₁ * (X : ℚ) ^ 2 + a₂ * (Y : ℚ) ^ 2 : ℚ)) : ℚ_[p]) / T) := by
  have hn1 : (0 : ℝ) ≤ ‖((a₁ : ℚ_[p]))‖ := norm_nonneg _
  have hn2 : (0 : ℝ) ≤ ‖((a₂ : ℚ_[p]))‖ := norm_nonneg _
  set M : ℝ := ‖((a₁ : ℚ_[p]))‖ + ‖((a₂ : ℚ_[p]))‖ + 1 with hM
  have hM0 : (0 : ℝ) < M := by rw [hM]; linarith
  have hM0' : M ≠ 0 := ne_of_gt hM0
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
  have h8p : (0 : ℝ) < 8 * p := by linarith
  have h8p' : (8 : ℝ) * p ≠ 0 := ne_of_gt h8p
  have hXn : ‖((X : ℚ_[p]))‖ ≤ 1 := Padic.norm_int_le_one _
  have hYn : ‖((Y : ℚ_[p]))‖ ≤ 1 := Padic.norm_int_le_one _
  have hbound : ∀ (a : ℚ) (W Z : ℚ_[p]), ‖((a : ℚ_[p]))‖ ≤ M → ‖W‖ ≤ 1 → ‖Z‖ ≤ 1 →
      ‖((a : ℚ_[p])) * (W ^ 2 - Z ^ 2)‖ ≤ M * ‖W - Z‖ := by
    intro a W Z haM hW hZ
    have hsum : ‖W + Z‖ ≤ 1 := le_trans (Padic.nonarchimedean W Z) (max_le hW hZ)
    have hfac : ((a : ℚ_[p])) * (W ^ 2 - Z ^ 2) = ((a : ℚ_[p])) * ((W - Z) * (W + Z)) := by ring
    rw [hfac, norm_mul, norm_mul]
    have hone : ‖((a : ℚ_[p]))‖ * (‖W - Z‖ * ‖W + Z‖) ≤ ‖((a : ℚ_[p]))‖ * (‖W - Z‖ * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (norm_nonneg _)) (norm_nonneg _)
    have htwo : ‖((a : ℚ_[p]))‖ * (‖W - Z‖ * 1) ≤ M * ‖W - Z‖ := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right haM (norm_nonneg _)
    linarith
  have hscale : ∀ W Z : ℚ_[p], ‖W - Z‖ < ‖T‖ / (8 * p * M) → M * ‖W - Z‖ < ‖T‖ / (8 * p) := by
    intro W Z h
    calc M * ‖W - Z‖ < M * (‖T‖ / (8 * p * M)) := mul_lt_mul_of_pos_left h hM0
      _ = ‖T‖ / (8 * p) := by field_simp
  have hcast : (((a₁ * (X : ℚ) ^ 2 + a₂ * (Y : ℚ) ^ 2 : ℚ)) : ℚ_[p]) - T
      = ((a₁ : ℚ_[p])) * (((X : ℚ_[p])) ^ 2 - U ^ 2)
        + ((a₂ : ℚ_[p])) * (((Y : ℚ_[p])) ^ 2 - V ^ 2) := by
    rw [hTdef]
    push_cast
    ring
  refine isSquare_div_of_dist_lt hT ?_
  rw [hcast]
  refine lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt (hbound a₁ _ _ (by rw [hM]; linarith) hXn hU) (hscale _ _ hX)
  · exact lt_of_le_of_lt (hbound a₂ _ _ (by rw [hM]; linarith) hYn hV) (hscale _ _ hY)

/-- **A rational value of a diagonal binary form in prescribed local square classes.**  Given a
nonzero local value of `⟨a₁, a₂⟩` at each place of a finite set, there is a rational value of the
form lying in the same square class at every one of those places, and with the sign of `a₁`. -/
theorem exists_rat_value_of_local (S : Finset Nat.Primes) {a₁ a₂ : ℚ} (h1 : a₁ ≠ 0) (h2 : a₂ ≠ 0)
    (t : ∀ p : Nat.Primes, ℚ_[(p : ℕ)]) (ht : ∀ p ∈ S, t p ≠ 0)
    (hval : ∀ p ∈ S, ∃ x y : ℚ_[(p : ℕ)],
      t p = ((a₁ : ℚ_[(p : ℕ)])) * x ^ 2 + ((a₂ : ℚ_[(p : ℕ)])) * y ^ 2) :
    ∃ q : ℚ, 0 < a₁ * q ∧ (∃ x y : ℚ, q = a₁ * x ^ 2 + a₂ * y ^ 2) ∧
      ∀ p ∈ S, IsSquare (((q : ℚ_[(p : ℕ)])) / t p) := by
  classical
  have hint : ∀ p : Nat.Primes, ∃ U V T : ℚ_[(p : ℕ)], ‖U‖ ≤ 1 ∧ ‖V‖ ≤ 1 ∧
      (p ∈ S → T ≠ 0 ∧ IsSquare (T / t p) ∧
        T = ((a₁ : ℚ_[(p : ℕ)])) * U ^ 2 + ((a₂ : ℚ_[(p : ℕ)])) * V ^ 2) := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨U, V, T, hU, hV, hT0, hTs, hTd⟩ := exists_integral_repr (ht p hp) (hval p hp)
      exact ⟨U, V, T, hU, hV, fun _ => ⟨hT0, hTs, hTd⟩⟩
    · exact ⟨0, 0, 0, by simp, by simp, fun h => absurd h hp⟩
  choose U V T hU hV hkey using hint
  have hεpos : ∀ p ∈ S, 0 < ‖T p‖ / (8 * ((p : ℕ) : ℝ) *
      (‖((a₁ : ℚ_[(p : ℕ)]))‖ + ‖((a₂ : ℚ_[(p : ℕ)]))‖ + 1)) := by
    intro p hp
    have hT0 : T p ≠ 0 := (hkey p hp).1
    have hn1 : (0 : ℝ) ≤ ‖((a₁ : ℚ_[(p : ℕ)]))‖ := norm_nonneg _
    have hn2 : (0 : ℝ) ≤ ‖((a₂ : ℚ_[(p : ℕ)]))‖ := norm_nonneg _
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have h8 : (0 : ℝ) < 8 * ((p : ℕ) : ℝ) := by linarith
    exact div_pos (norm_pos_iff.2 hT0) (mul_pos h8 (by linarith))
  obtain ⟨Y, hYapp⟩ := exists_int_norm_sub_lt S V (fun p _ => hV p)
    (fun p => ‖T p‖ / (8 * ((p : ℕ) : ℝ) *
      (‖((a₁ : ℚ_[(p : ℕ)]))‖ + ‖((a₂ : ℚ_[(p : ℕ)]))‖ + 1))) hεpos
  obtain ⟨X, hXgt, hXapp⟩ := exists_int_gt_and_norm_sub_lt S U (fun p _ => hU p)
    (fun p => ‖T p‖ / (8 * ((p : ℕ) : ℝ) *
      (‖((a₁ : ℚ_[(p : ℕ)]))‖ + ‖((a₂ : ℚ_[(p : ℕ)]))‖ + 1))) hεpos
    (⌈|a₂| * (Y : ℚ) ^ 2 / |a₁|⌉ + 1)
  refine ⟨a₁ * (X : ℚ) ^ 2 + a₂ * (Y : ℚ) ^ 2, ?_, ⟨(X : ℚ), (Y : ℚ), rfl⟩, ?_⟩
  · have ha1 : (0 : ℚ) < |a₁| := abs_pos.2 h1
    have hc0 : (0 : ℤ) ≤ ⌈|a₂| * (Y : ℚ) ^ 2 / |a₁|⌉ := Int.ceil_nonneg (by positivity)
    have hce : |a₂| * (Y : ℚ) ^ 2 / |a₁| ≤ ((⌈|a₂| * (Y : ℚ) ^ 2 / |a₁|⌉ : ℤ) : ℚ) := Int.le_ceil _
    have hXQ : (((⌈|a₂| * (Y : ℚ) ^ 2 / |a₁|⌉ + 1 : ℤ)) : ℚ) < (X : ℚ) := by exact_mod_cast hXgt
    have hX1 : (1 : ℚ) ≤ (X : ℚ) := by
      have hXZ : (1 : ℤ) ≤ X := by omega
      exact_mod_cast hXZ
    have hXsq : (X : ℚ) ≤ (X : ℚ) ^ 2 := by nlinarith
    have hlt : |a₂| * (Y : ℚ) ^ 2 / |a₁| < (X : ℚ) ^ 2 := by
      push_cast at hXQ
      linarith
    rw [div_lt_iff₀ ha1] at hlt
    have hmul : |a₁| * (|a₂| * (Y : ℚ) ^ 2) < |a₁| * ((X : ℚ) ^ 2 * |a₁|) :=
      mul_lt_mul_of_pos_left hlt ha1
    have hb : -(|a₁| * |a₂| * (Y : ℚ) ^ 2) ≤ a₁ * a₂ * (Y : ℚ) ^ 2 := by
      have h0 : -(|a₁| * |a₂|) ≤ a₁ * a₂ := by
        rw [← abs_mul]
        exact neg_abs_le _
      nlinarith [sq_nonneg ((Y : ℚ))]
    have expand : a₁ * (a₁ * (X : ℚ) ^ 2 + a₂ * (Y : ℚ) ^ 2)
        = |a₁| * |a₁| * (X : ℚ) ^ 2 + a₁ * a₂ * (Y : ℚ) ^ 2 := by
      rw [abs_mul_abs_self]
      ring
    rw [expand]
    nlinarith [hmul, hb]
  · intro p hp
    have happrox := isSquare_div_of_approx (a₁ := a₁) (a₂ := a₂) (hU p) (hV p) (hkey p hp).1
      (hkey p hp).2.2 (hXapp p hp) (hYapp p hp)
    exact isSquare_div_trans (hkey p hp).1 happrox (hkey p hp).2.1

/-- Interchanging the first two coefficients of a diagonal form in five variables. -/
theorem isQuinaryIsotropic_swap {K : Type*} [Field K] {a b c d e : K}
    (h : IsQuinaryIsotropic a b c d e) : IsQuinaryIsotropic b a c d e := by
  obtain ⟨x, y, z, w, u, hne, h0⟩ := h
  exact ⟨y, x, z, w, u, fun hz => hne ⟨hz.2.1, hz.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2⟩,
    by linear_combination h0⟩

set_option maxHeartbeats 1000000 in
/-- The Hasse principle in five variables, in the case where the real value shared by the two
halves of the form has the sign of the first coefficient. -/
private theorem isQuinaryIsotropic_rat_aux {a₁ a₂ a₃ a₄ a₅ : ℚ} (h1 : a₁ ≠ 0) (h2 : a₂ ≠ 0)
    (h3 : a₃ ≠ 0) (h4 : a₄ ≠ 0) (h5 : a₅ ≠ 0)
    (hloc : ∀ p : Nat.Primes, IsQuinaryIsotropic ((a₁ : ℚ_[(p : ℕ)])) ((a₂ : ℚ_[(p : ℕ)]))
      ((a₃ : ℚ_[(p : ℕ)])) ((a₄ : ℚ_[(p : ℕ)])) ((a₅ : ℚ_[(p : ℕ)])))
    {tr : ℝ} (htr : tr ≠ 0) (hsign : 0 < ((a₁ : ℝ)) * tr)
    (htrb : ∃ z w u : ℝ, tr = -((a₃ : ℝ)) * z ^ 2 + -((a₄ : ℝ)) * w ^ 2 + -((a₅ : ℝ)) * u ^ 2) :
    IsQuinaryIsotropic a₁ a₂ a₃ a₄ a₅ := by
  classical
  have hlocal : ∀ p : Nat.Primes, ∃ tp : ℚ_[(p : ℕ)], tp ≠ 0 ∧
      (∃ x y : ℚ_[(p : ℕ)], tp = ((a₁ : ℚ_[(p : ℕ)])) * x ^ 2 + ((a₂ : ℚ_[(p : ℕ)])) * y ^ 2) ∧
      (∃ z w u : ℚ_[(p : ℕ)], tp = -((a₃ : ℚ_[(p : ℕ)])) * z ^ 2 + -((a₄ : ℚ_[(p : ℕ)])) * w ^ 2
        + -((a₅ : ℚ_[(p : ℕ)])) * u ^ 2) := by
    intro p
    exact (isQuinaryIsotropic_iff_exists_common (by norm_num) (Rat.cast_ne_zero.2 h1)
      (Rat.cast_ne_zero.2 h2) (Rat.cast_ne_zero.2 h3) (Rat.cast_ne_zero.2 h4)
      (Rat.cast_ne_zero.2 h5)).1 (hloc p)
  choose t ht htbin htter using hlocal
  obtain ⟨q, hqsign, hqbin, hqsq⟩ :=
    exists_rat_value_of_local (insert primeTwo ((finite_setOf_norm_ne_one h3).toFinset ∪
      (finite_setOf_norm_ne_one h4).toFinset ∪ (finite_setOf_norm_ne_one h5).toFinset))
      h1 h2 t (fun p _ => ht p) (fun p _ => htbin p)
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hqsign
    exact lt_irrefl 0 hqsign
  have hquat : ∀ p : Nat.Primes, IsQuaternaryIsotropic (((-q : ℚ)) : ℚ_[(p : ℕ)])
      (((-a₃ : ℚ)) : ℚ_[(p : ℕ)]) (((-a₄ : ℚ)) : ℚ_[(p : ℕ)]) (((-a₅ : ℚ)) : ℚ_[(p : ℕ)]) := by
    intro p
    by_cases hp : p ∈ insert primeTwo ((finite_setOf_norm_ne_one h3).toFinset ∪
      (finite_setOf_norm_ne_one h4).toFinset ∪ (finite_setOf_norm_ne_one h5).toFinset)
    · obtain ⟨z, w, u, hzwu⟩ :=
        exists_repr_ternary_of_isSquare_div (ht p) (htter p) (hqsq p hp)
      refine ⟨1, z, w, u, by simp, ?_⟩
      push_cast
      linear_combination -hzwu
    · have hp2 : ((p : ℕ)) ≠ 2 := by
        intro hc
        refine hp ?_
        rw [show p = primeTwo from Subtype.ext hc]
        exact Finset.mem_insert_self _ _
      have h3' : ‖((a₃ : ℚ_[(p : ℕ)]))‖ = 1 := by
        by_contra hc
        exact hp (Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_union_left _ (((finite_setOf_norm_ne_one h3).mem_toFinset).2 hc))))
      have h4' : ‖((a₄ : ℚ_[(p : ℕ)]))‖ = 1 := by
        by_contra hc
        exact hp (Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_union_right _ (((finite_setOf_norm_ne_one h4).mem_toFinset).2 hc))))
      have h5' : ‖((a₅ : ℚ_[(p : ℕ)]))‖ = 1 := by
        by_contra hc
        exact hp (Finset.mem_insert_of_mem (Finset.mem_union_right _
          (((finite_setOf_norm_ne_one h5).mem_toFinset).2 hc)))
      obtain ⟨x, y, z, hne, h0⟩ := isotropic_ternary_of_norm_one (p := (p : ℕ)) hp2
        (u₁ := (((-a₃ : ℚ)) : ℚ_[(p : ℕ)])) (u₂ := (((-a₄ : ℚ)) : ℚ_[(p : ℕ)]))
        (u₃ := (((-a₅ : ℚ)) : ℚ_[(p : ℕ)])) (by rw [Rat.cast_neg, norm_neg]; exact h3')
        (by rw [Rat.cast_neg, norm_neg]; exact h4') (by rw [Rat.cast_neg, norm_neg]; exact h5')
      exact ⟨0, x, y, z, fun hc => hne ⟨hc.2.1, hc.2.2.1, hc.2.2.2⟩, by linear_combination h0⟩
  have hqr : IsQuaternaryIsotropic (((-q : ℚ)) : ℝ) (((-a₃ : ℚ)) : ℝ) (((-a₄ : ℚ)) : ℝ)
      (((-a₅ : ℚ)) : ℝ) := by
    have hprod : 0 < ((a₁ : ℝ)) * ((q : ℝ)) := by exact_mod_cast hqsign
    have hqtr : 0 < ((q : ℝ)) * tr := by nlinarith [mul_pos hprod hsign, sq_nonneg ((a₁ : ℝ))]
    have htr2 : 0 < tr ^ 2 := lt_of_le_of_ne (sq_nonneg tr) (Ne.symm (pow_ne_zero 2 htr))
    have hsq : IsSquare (((q : ℝ)) / tr) := by
      refine (isSquare_real_iff _).2 ?_
      have hrw : ((q : ℝ)) / tr = ((q : ℝ)) * tr / tr ^ 2 := by
        field_simp
      rw [hrw]
      exact le_of_lt (div_pos hqtr htr2)
    obtain ⟨z, w, u, hzwu⟩ := exists_repr_ternary_of_isSquare_div htr htrb hsq
    refine ⟨1, z, w, u, by simp, ?_⟩
    push_cast
    linear_combination -hzwu
  have hquatrat : IsQuaternaryIsotropic (-q) (-a₃) (-a₄) (-a₅) :=
    isQuaternaryIsotropic_rat_of_forall_local (neg_ne_zero.2 hq0) (neg_ne_zero.2 h3)
      (neg_ne_zero.2 h4) (neg_ne_zero.2 h5) hquat hqr
  obtain ⟨x, z, w, u, hne, h0⟩ := hquatrat
  refine (isQuinaryIsotropic_iff_exists_common (by norm_num) h1 h2 h3 h4 h5).2 ⟨q, hq0, hqbin, ?_⟩
  by_cases hx : x = 0
  · subst hx
    have hiso : ∃ z w u : ℚ, ¬(z = 0 ∧ w = 0 ∧ u = 0) ∧
        -a₃ * z ^ 2 + -a₄ * w ^ 2 + -a₅ * u ^ 2 = 0 :=
      ⟨z, w, u, fun hh => hne ⟨rfl, hh.1, hh.2.1, hh.2.2⟩, by linear_combination h0⟩
    exact exists_repr_of_isTernaryIsotropic (by norm_num) (neg_ne_zero.2 h3) (neg_ne_zero.2 h4)
      (neg_ne_zero.2 h5) hiso q
  · refine ⟨z / x, w / x, u / x, ?_⟩
    field_simp
    linear_combination -h0

/-- **The Hasse principle for diagonal forms in five variables**: such a form over the rational
field represents zero nontrivially as soon as it does so over every completion. -/
theorem isQuinaryIsotropic_rat_of_forall_local {a₁ a₂ a₃ a₄ a₅ : ℚ} (h1 : a₁ ≠ 0) (h2 : a₂ ≠ 0)
    (h3 : a₃ ≠ 0) (h4 : a₄ ≠ 0) (h5 : a₅ ≠ 0)
    (hloc : ∀ p : Nat.Primes, IsQuinaryIsotropic ((a₁ : ℚ_[(p : ℕ)])) ((a₂ : ℚ_[(p : ℕ)]))
      ((a₃ : ℚ_[(p : ℕ)])) ((a₄ : ℚ_[(p : ℕ)])) ((a₅ : ℚ_[(p : ℕ)])))
    (hreal : IsQuinaryIsotropic ((a₁ : ℝ)) ((a₂ : ℝ)) ((a₃ : ℝ)) ((a₄ : ℝ)) ((a₅ : ℝ))) :
    IsQuinaryIsotropic a₁ a₂ a₃ a₄ a₅ := by
  obtain ⟨tr, htr, htra, htrb⟩ :=
    (isQuinaryIsotropic_iff_exists_common (by norm_num) (Rat.cast_ne_zero.2 h1)
      (Rat.cast_ne_zero.2 h2) (Rat.cast_ne_zero.2 h3) (Rat.cast_ne_zero.2 h4)
      (Rat.cast_ne_zero.2 h5)).1 hreal
  have hsign : 0 < ((a₁ : ℝ)) * tr ∨ 0 < ((a₂ : ℝ)) * tr := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    obtain ⟨x, y, hxy⟩ := htra
    have hsq : tr ^ 2 = ((a₁ : ℝ)) * tr * x ^ 2 + ((a₂ : ℝ)) * tr * y ^ 2 := by
      linear_combination tr * hxy
    have htr2 : 0 < tr ^ 2 := lt_of_le_of_ne (sq_nonneg tr) (Ne.symm (pow_ne_zero 2 htr))
    have hA : ((a₁ : ℝ)) * tr * x ^ 2 ≤ 0 := mul_nonpos_iff.2 (Or.inr ⟨hc1, sq_nonneg x⟩)
    have hB : ((a₂ : ℝ)) * tr * y ^ 2 ≤ 0 := mul_nonpos_iff.2 (Or.inr ⟨hc2, sq_nonneg y⟩)
    linarith
  rcases hsign with hs | hs
  · exact isQuinaryIsotropic_rat_aux h1 h2 h3 h4 h5 hloc htr hs htrb
  · exact isQuinaryIsotropic_swap
      (isQuinaryIsotropic_rat_aux h2 h1 h3 h4 h5 (fun p => isQuinaryIsotropic_swap (hloc p)) htr hs
        htrb)

/-- **The Hasse principle for diagonal forms in five variables**, as an equivalence. -/
theorem isQuinaryIsotropic_rat_iff_forall_local {a₁ a₂ a₃ a₄ a₅ : ℚ} (h1 : a₁ ≠ 0) (h2 : a₂ ≠ 0)
    (h3 : a₃ ≠ 0) (h4 : a₄ ≠ 0) (h5 : a₅ ≠ 0) :
    IsQuinaryIsotropic a₁ a₂ a₃ a₄ a₅ ↔
      (∀ p : Nat.Primes, IsQuinaryIsotropic ((a₁ : ℚ_[(p : ℕ)])) ((a₂ : ℚ_[(p : ℕ)]))
        ((a₃ : ℚ_[(p : ℕ)])) ((a₄ : ℚ_[(p : ℕ)])) ((a₅ : ℚ_[(p : ℕ)]))) ∧
      IsQuinaryIsotropic ((a₁ : ℝ)) ((a₂ : ℝ)) ((a₃ : ℝ)) ((a₄ : ℝ)) ((a₅ : ℝ)) := by
  refine ⟨fun h => ⟨fun p => ?_, ?_⟩, fun h => isQuinaryIsotropic_rat_of_forall_local h1 h2 h3 h4 h5
    h.1 h.2⟩
  · obtain ⟨x, y, z, w, u, hne, h0⟩ := h
    refine ⟨(x : ℚ_[(p : ℕ)]), (y : ℚ_[(p : ℕ)]), (z : ℚ_[(p : ℕ)]), (w : ℚ_[(p : ℕ)]),
      (u : ℚ_[(p : ℕ)]), ?_, ?_⟩
    · rintro ⟨hx, hy, hz, hw, hu⟩
      exact hne ⟨by exact_mod_cast hx, by exact_mod_cast hy, by exact_mod_cast hz,
        by exact_mod_cast hw, by exact_mod_cast hu⟩
    · exact_mod_cast congrArg (fun r : ℚ => ((r : ℚ_[(p : ℕ)]))) h0
  · obtain ⟨x, y, z, w, u, hne, h0⟩ := h
    refine ⟨(x : ℝ), (y : ℝ), (z : ℝ), (w : ℝ), (u : ℝ), ?_, ?_⟩
    · rintro ⟨hx, hy, hz, hw, hu⟩
      exact hne ⟨by exact_mod_cast hx, by exact_mod_cast hy, by exact_mod_cast hz,
        by exact_mod_cast hw, by exact_mod_cast hu⟩
    · exact_mod_cast congrArg (fun r : ℚ => ((r : ℝ))) h0

end InverseGalois.CFT
