import Mathlib
import InverseGalois.CFT.Global.RationalSquareClasses
import InverseGalois.CFT.Global.HilbertPlaces

/-!
# Weak approximation for square classes of the rationals

The squares of `ℚ_[p]` form an open subgroup, so a square class of `ℚ_[p]` is an open set and can
be hit by a rational number.  This file upgrades that one-place statement to a simultaneous one:
given finitely many primes and a prescribed nonzero target in each of the corresponding
completions, there is a single *integer* lying in the prescribed square class at every one of the
chosen places, and it can be taken as large or as negative as one likes.

The argument has two halves.  The arithmetic half is the Chinese remainder theorem over `ℤ` for
the pairwise coprime moduli `p ^ N`, together with the observation that a solution stays a
solution after adding a multiple of the product of the moduli, which makes the solution set
unbounded in both directions.  The analytic half is that an integer congruent to a nonzero
integer `m` modulo a large power of `p` lies in the square class of `m`: the crude bound
`p ^ |m| > |m|` forces `‖(m : ℚ_[p])‖ > p ^ (-|m|)`, so the congruence puts the two numbers well
inside the ball of radius `‖m‖ / (8 * p)` in which square classes are constant.

## Main results

* `InverseGalois.CFT.exists_int_modEq_prime_pow`: prescribed residues modulo prime powers can be
  matched simultaneously by an integer.
* `InverseGalois.CFT.exists_int_gt_and_modEq`: the same, with the solution above a given bound.
* `InverseGalois.CFT.exists_int_lt_and_modEq`: the same, with the solution below a given bound.
* `InverseGalois.CFT.exists_intCast_isSquare_div`: every square class of `ℚ_[p]` contains a
  nonzero integer.
* `InverseGalois.CFT.isSquare_intCast_div_intCast_of_dvd`: an integer congruent to a nonzero
  integer `m` modulo a sufficiently large power of `p` lies in the square class of `m`.
* `InverseGalois.CFT.exists_int_isSquare_div`: **weak approximation for square classes**, with an
  arbitrarily large positive solution.
* `InverseGalois.CFT.exists_int_lt_isSquare_div`: the same, with an arbitrarily negative solution.
* `InverseGalois.CFT.exists_rat_isSquare_div_sign`: the same, with the sign of the solution
  prescribed by that of a nonzero rational.
-/

namespace InverseGalois.CFT

open Local

/-! ### Square classes as an equivalence relation -/

/-- The square class relation is symmetric: if `a / b` is a square then so is `b / a`. -/
theorem isSquare_div_swap {K : Type*} [Field K] {a b : K} (h : IsSquare (a / b)) :
    IsSquare (b / a) := by
  rw [← inv_div]
  exact h.inv

/-- The square class relation is transitive along a nonzero middle term. -/
theorem isSquare_div_trans {K : Type*} [Field K] {a b c : K} (hb : b ≠ 0)
    (h₁ : IsSquare (a / b)) (h₂ : IsSquare (b / c)) : IsSquare (a / c) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have h : a / c = a / b * (b / c) := by field_simp
    rw [h]
    exact h₁.mul h₂

/-- Multiplying the denominator by a nonzero square does not change the square class. -/
theorem isSquare_div_mul_sq {K : Type*} [Field K] {a b d : K} (hd : d ≠ 0)
    (h : IsSquare (a / b)) : IsSquare (a / (b * d ^ 2)) := by
  have hrw : a / (b * d ^ 2) = a / b * (d⁻¹) ^ 2 := by
    field_simp
  rw [hrw]
  exact h.mul ⟨d⁻¹, pow_two d⁻¹⟩

/-! ### Integral representatives of local square classes -/

/-- Every square class of `ℚ_[p]` contains a nonzero integer: a rational representative may be
cleared of its denominator at the cost of a square factor. -/
theorem exists_intCast_isSquare_div {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ IsSquare (x / (m : ℚ_[p])) := by
  obtain ⟨r, hr0, hrs⟩ := exists_rat_isSquare_div hx
  have hden : ((r.den : ℚ_[p])) ≠ 0 := by
    have : (r.den : ℚ_[p]) = ((r.den : ℚ) : ℚ_[p]) := by push_cast; ring
    rw [this]
    exact_mod_cast (Nat.cast_ne_zero.mpr r.den_nz : (r.den : ℚ) ≠ 0)
  refine ⟨r.num * (r.den : ℤ), mul_ne_zero (Rat.num_ne_zero.mpr hr0) (by exact_mod_cast r.den_nz),
    ?_⟩
  have hcast : ((r.num * (r.den : ℤ) : ℤ) : ℚ_[p]) = (r : ℚ_[p]) * (r.den : ℚ_[p]) ^ 2 := by
    rw [Rat.cast_def]
    push_cast
    field_simp
  rw [hcast]
  exact isSquare_div_mul_sq hden hrs

/-- A nonzero integer has `p`-adic norm bigger than `p ^ (-|m|)`, since a power `p ^ n` dividing
it satisfies `p ^ n ≤ |m|` while `p ^ |m| > |m|`. -/
theorem zpow_neg_natAbs_lt_norm_intCast {p : ℕ} [Fact p.Prime] {m : ℤ} (hm : m ≠ 0) :
    ((p : ℝ)) ^ (-(m.natAbs : ℤ)) < ‖(m : ℚ_[p])‖ := by
  by_contra hcon
  push_neg at hcon
  have hdvd : ((p : ℤ)) ^ m.natAbs ∣ m := (Padic.norm_int_le_pow_iff_dvd m m.natAbs).mp hcon
  have hdvd' : p ^ m.natAbs ∣ m.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have hle : p ^ m.natAbs ≤ m.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hm) hdvd'
  have hlt : m.natAbs < 2 ^ m.natAbs := Nat.lt_two_pow_self
  have h2 : 2 ^ m.natAbs ≤ p ^ m.natAbs :=
    Nat.pow_le_pow_left (Fact.out : p.Prime).two_le m.natAbs
  omega

/-- An integer congruent to a nonzero integer `m` modulo a power of `p` exceeding `|m| + 5` lies
in the same `p`-adic square class as `m`. -/
theorem isSquare_intCast_div_intCast_of_dvd {p : ℕ} [Fact p.Prime] {m x : ℤ} (hm : m ≠ 0)
    {N : ℕ} (hN : m.natAbs + 5 ≤ N) (hdvd : ((p : ℤ)) ^ N ∣ x - m) :
    IsSquare (((x : ℚ_[p])) / (m : ℚ_[p])) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hPpos : (0 : ℝ) < (p : ℝ) := by linarith
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  set A : ℕ := m.natAbs with hA
  have hlow : ((p : ℝ) ^ A)⁻¹ < ‖(m : ℚ_[p])‖ := by
    have := zpow_neg_natAbs_lt_norm_intCast (p := p) hm
    rwa [zpow_neg, zpow_natCast] at this
  have hup : ‖((x : ℚ_[p])) - (m : ℚ_[p])‖ ≤ ((p : ℝ) ^ N)⁻¹ := by
    have hc : ((x - m : ℤ) : ℚ_[p]) = (x : ℚ_[p]) - (m : ℚ_[p]) := by push_cast; ring
    have := (Padic.norm_int_le_pow_iff_dvd (x - m) N).mpr hdvd
    rwa [hc, zpow_neg, zpow_natCast] at this
  have hAp : (0 : ℝ) < (p : ℝ) ^ A := pow_pos hPpos A
  have h16 : (2 : ℝ) ^ 4 ≤ (p : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hp2 4
  have h8 : (8 : ℝ) * (p : ℝ) ≤ (p : ℝ) ^ 5 := by
    nlinarith [mul_le_mul_of_nonneg_right h16 hPpos.le]
  have hchain : (p : ℝ) ^ A * (8 * (p : ℝ)) ≤ (p : ℝ) ^ N := by
    calc (p : ℝ) ^ A * (8 * (p : ℝ)) ≤ (p : ℝ) ^ A * (p : ℝ) ^ 5 := by nlinarith
      _ = (p : ℝ) ^ (A + 5) := by rw [pow_add]
      _ ≤ (p : ℝ) ^ N := pow_le_pow_right₀ hP1 hN
  have hden : (0 : ℝ) < 8 * (p : ℝ) := by linarith
  have hprodpos : (0 : ℝ) < (p : ℝ) ^ A * (8 * (p : ℝ)) := by positivity
  have hinv : ((p : ℝ) ^ N)⁻¹ ≤ ((p : ℝ) ^ A * (8 * (p : ℝ)))⁻¹ :=
    inv_anti₀ hprodpos hchain
  have heq : ((p : ℝ) ^ A * (8 * (p : ℝ)))⁻¹ = ((p : ℝ) ^ A)⁻¹ / (8 * (p : ℝ)) := by
    rw [mul_inv, div_eq_mul_inv]
  have hstrict : ((p : ℝ) ^ A)⁻¹ / (8 * (p : ℝ)) < ‖(m : ℚ_[p])‖ / (8 * (p : ℝ)) :=
    div_lt_div_of_pos_right hlow hden
  refine isSquare_div_of_dist_lt (Int.cast_ne_zero.mpr hm) ?_
  calc ‖((x : ℚ_[p])) - (m : ℚ_[p])‖ ≤ ((p : ℝ) ^ N)⁻¹ := hup
    _ ≤ ((p : ℝ) ^ A * (8 * (p : ℝ)))⁻¹ := hinv
    _ = ((p : ℝ) ^ A)⁻¹ / (8 * (p : ℝ)) := heq
    _ < ‖(m : ℚ_[p])‖ / (8 * (p : ℝ)) := hstrict

/-! ### The Chinese remainder step -/

/-- **Chinese remainder theorem for prime powers.**  Residues prescribed modulo `p ^ N` at
finitely many primes are realized simultaneously by an integer. -/
theorem exists_int_modEq_prime_pow (S : Finset Nat.Primes) (r : Nat.Primes → ℤ) (N : ℕ) :
    ∃ x : ℤ, ∀ p ∈ S, ((p : ℤ) ^ N ∣ x - r p) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a S ha ih =>
    obtain ⟨x₀, hx₀⟩ := ih
    have hcop : IsCoprime (((a : ℤ)) ^ N) (∏ q ∈ S, ((q : ℤ)) ^ N) := by
      refine IsCoprime.prod_right fun q hq => IsCoprime.pow ?_
      refine Nat.Coprime.isCoprime ?_
      refine (Nat.coprime_primes a.2 q.2).mpr ?_
      intro hcontra
      exact ha (by rwa [Nat.Primes.coe_nat_inj a q |>.mp hcontra])
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨x₀ + (r a - x₀) * (v * ∏ q ∈ S, ((q : ℤ)) ^ N), fun q hq => ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hqS
    · have hvm : v * ∏ t ∈ S, ((t : ℤ)) ^ N = 1 - u * ((q : ℤ)) ^ N := by linarith
      have hres : x₀ + (r q - x₀) * (v * ∏ t ∈ S, ((t : ℤ)) ^ N) - r q
          = ((q : ℤ)) ^ N * (-(r q - x₀) * u) := by
        rw [hvm]; ring
      rw [hres]
      exact Dvd.intro _ rfl
    · have hdvd : ((q : ℤ)) ^ N ∣ ∏ t ∈ S, ((t : ℤ)) ^ N :=
        Finset.dvd_prod_of_mem (fun t : Nat.Primes => ((t : ℤ)) ^ N) hqS
      have hres : x₀ + (r a - x₀) * (v * ∏ t ∈ S, ((t : ℤ)) ^ N) - r q
          = (x₀ - r q) + ((r a - x₀) * v) * ∏ t ∈ S, ((t : ℤ)) ^ N := by ring
      rw [hres]
      exact dvd_add (hx₀ q hqS) (hdvd.mul_left _)

/-- Chinese remainder with a lower bound: prescribed residues, and the solution can be taken
above any given bound. -/
theorem exists_int_gt_and_modEq (S : Finset Nat.Primes) (r : Nat.Primes → ℤ) (N : ℕ) (B : ℤ) :
    ∃ x : ℤ, B < x ∧ ∀ p ∈ S, ((p : ℤ) ^ N ∣ x - r p) := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_int_modEq_prime_pow S r N
  have hMpos : (0 : ℤ) < ∏ q ∈ S, ((q : ℤ)) ^ N :=
    Finset.prod_pos fun q _ => pow_pos (by exact_mod_cast q.2.pos) N
  refine ⟨x₀ + max 0 (B - x₀ + 1) * ∏ q ∈ S, ((q : ℤ)) ^ N, ?_, fun p hp => ?_⟩
  · have h1 : max 0 (B - x₀ + 1) ≤ max 0 (B - x₀ + 1) * ∏ q ∈ S, ((q : ℤ)) ^ N :=
      le_mul_of_one_le_right (le_max_left _ _) hMpos
    have h2 : B - x₀ + 1 ≤ max 0 (B - x₀ + 1) := le_max_right _ _
    linarith
  · have hdvd : ((p : ℤ)) ^ N ∣ ∏ q ∈ S, ((q : ℤ)) ^ N :=
      Finset.dvd_prod_of_mem (fun t : Nat.Primes => ((t : ℤ)) ^ N) hp
    have hres : x₀ + max 0 (B - x₀ + 1) * (∏ q ∈ S, ((q : ℤ)) ^ N) - r p
        = (x₀ - r p) + max 0 (B - x₀ + 1) * ∏ q ∈ S, ((q : ℤ)) ^ N := by ring
    rw [hres]
    exact dvd_add (hx₀ p hp) (hdvd.mul_left _)

/-- Chinese remainder with an upper bound: prescribed residues, and the solution can be taken
below any given bound. -/
theorem exists_int_lt_and_modEq (S : Finset Nat.Primes) (r : Nat.Primes → ℤ) (N : ℕ) (B : ℤ) :
    ∃ x : ℤ, x < B ∧ ∀ p ∈ S, ((p : ℤ) ^ N ∣ x - r p) := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_int_modEq_prime_pow S r N
  have hMpos : (0 : ℤ) < ∏ q ∈ S, ((q : ℤ)) ^ N :=
    Finset.prod_pos fun q _ => pow_pos (by exact_mod_cast q.2.pos) N
  refine ⟨x₀ + min 0 (B - x₀ - 1) * ∏ q ∈ S, ((q : ℤ)) ^ N, ?_, fun p hp => ?_⟩
  · have h1 : min 0 (B - x₀ - 1) * ∏ q ∈ S, ((q : ℤ)) ^ N
        ≤ min 0 (B - x₀ - 1) * 1 :=
      mul_le_mul_of_nonpos_left hMpos (min_le_left _ _)
    have h2 : min 0 (B - x₀ - 1) ≤ B - x₀ - 1 := min_le_right _ _
    rw [mul_one] at h1
    linarith
  · have hdvd : ((p : ℤ)) ^ N ∣ ∏ q ∈ S, ((q : ℤ)) ^ N :=
      Finset.dvd_prod_of_mem (fun t : Nat.Primes => ((t : ℤ)) ^ N) hp
    have hres : x₀ + min 0 (B - x₀ - 1) * (∏ q ∈ S, ((q : ℤ)) ^ N) - r p
        = (x₀ - r p) + min 0 (B - x₀ - 1) * ∏ q ∈ S, ((q : ℤ)) ^ N := by ring
    rw [hres]
    exact dvd_add (hx₀ p hp) (hdvd.mul_left _)

/-! ### Weak approximation -/

/-- The common core of the approximation statements: any family of congruence solutions
constrained by a predicate `P` yields a solution of the square class problem satisfying `P`. -/
theorem exists_int_isSquare_div_of_crt (S : Finset Nat.Primes)
    (y : ∀ p : Nat.Primes, ℚ_[(p : ℕ)]) (hy : ∀ p ∈ S, y p ≠ 0) (P : ℤ → Prop)
    (hP : ∀ (r : Nat.Primes → ℤ) (N : ℕ), ∃ x : ℤ, P x ∧ ∀ p ∈ S, ((p : ℤ) ^ N ∣ x - r p)) :
    ∃ x : ℤ, P x ∧ ∀ p ∈ S, IsSquare (((x : ℚ) : ℚ_[(p : ℕ)]) / y p) := by
  classical
  have key : ∀ p : Nat.Primes,
      ∃ m : ℤ, p ∈ S → m ≠ 0 ∧ IsSquare (y p / (m : ℚ_[(p : ℕ)])) := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨m, hm0, hms⟩ := exists_intCast_isSquare_div (hy p hp)
      exact ⟨m, fun _ => ⟨hm0, hms⟩⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose m hm using key
  obtain ⟨x, hPx, hx⟩ := hP m (5 + ∑ q ∈ S, (m q).natAbs)
  refine ⟨x, hPx, fun p hp => ?_⟩
  obtain ⟨hm0, hms⟩ := hm p hp
  have hsum : (m p).natAbs ≤ ∑ q ∈ S, (m q).natAbs :=
    Finset.single_le_sum (f := fun q => (m q).natAbs) (fun _ _ => Nat.zero_le _) hp
  have h₁ : IsSquare (((x : ℚ_[(p : ℕ)])) / (m p : ℚ_[(p : ℕ)])) :=
    isSquare_intCast_div_intCast_of_dvd hm0 (by omega) (hx p hp)
  have h₂ : IsSquare ((m p : ℚ_[(p : ℕ)]) / y p) := isSquare_div_swap hms
  have hcast : ((x : ℚ) : ℚ_[(p : ℕ)]) = ((x : ℚ_[(p : ℕ)])) := by push_cast; ring
  rw [hcast]
  exact isSquare_div_trans (Int.cast_ne_zero.mpr hm0) h₁ h₂

/-- **Weak approximation for square classes.**  Given a nonzero target in `ℚ_[p]` for each `p` in
a finite set of primes, some integer above any prescribed bound lies in the prescribed square
class at every one of them. -/
theorem exists_int_isSquare_div (S : Finset Nat.Primes) (y : ∀ p : Nat.Primes, ℚ_[(p : ℕ)])
    (hy : ∀ p ∈ S, y p ≠ 0) (B : ℤ) :
    ∃ x : ℤ, B < x ∧ ∀ p ∈ S, IsSquare (((x : ℚ) : ℚ_[(p : ℕ)]) / y p) :=
  exists_int_isSquare_div_of_crt S y hy (fun x => B < x)
    fun r N => exists_int_gt_and_modEq S r N B

/-- **Weak approximation for square classes**, negative version: the approximating integer can be
taken below any prescribed bound. -/
theorem exists_int_lt_isSquare_div (S : Finset Nat.Primes) (y : ∀ p : Nat.Primes, ℚ_[(p : ℕ)])
    (hy : ∀ p ∈ S, y p ≠ 0) (B : ℤ) :
    ∃ x : ℤ, x < B ∧ ∀ p ∈ S, IsSquare (((x : ℚ) : ℚ_[(p : ℕ)]) / y p) :=
  exists_int_isSquare_div_of_crt S y hy (fun x => x < B)
    fun r N => exists_int_lt_and_modEq S r N B

/-- **Weak approximation for square classes** with the sign prescribed by a nonzero rational. -/
theorem exists_rat_isSquare_div_sign (S : Finset Nat.Primes) (y : ∀ p : Nat.Primes, ℚ_[(p : ℕ)])
    (hy : ∀ p ∈ S, y p ≠ 0) {s : ℚ} (hs : s ≠ 0) :
    ∃ x : ℚ, x ≠ 0 ∧ (0 < x ↔ 0 < s) ∧ ∀ p ∈ S, IsSquare ((x : ℚ_[(p : ℕ)]) / y p) := by
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · obtain ⟨x, hxB, hxs⟩ := exists_int_lt_isSquare_div S y hy 0
    refine ⟨(x : ℚ), ?_, ?_, hxs⟩
    · exact_mod_cast hxB.ne
    · constructor
      · intro h
        exact absurd (by exact_mod_cast h : (0 : ℤ) < x) (by omega)
      · intro h
        exact absurd h (not_lt.mpr hneg.le)
  · obtain ⟨x, hxB, hxs⟩ := exists_int_isSquare_div S y hy 0
    refine ⟨(x : ℚ), ?_, ?_, hxs⟩
    · exact_mod_cast hxB.ne'
    · exact iff_of_true (by exact_mod_cast hxB) hpos

end InverseGalois.CFT
