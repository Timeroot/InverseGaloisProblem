import Mathlib

/-!
# The Davenport–Cassels descent for sums of two and three squares

A positive definite integral quadratic form `f` has the *Davenport–Cassels property* when every
rational point lies at `f`-distance strictly less than `1` from some integral point.  For such a
form, an integer represented by `f` over the rational field is already represented over the
integers: starting from a representation `x = v / t` with `v` integral and `t` a positive integer,
one replaces `v / t` by `V / T` where `V` and `T` are built out of the nearest integral point `w`
to `x`, and the identity `t * T = f(v - t * w)` forces `0 ≤ T < t`.  Iterating drives the
denominator down to `1`.

The sum of two squares has worst case `(1/2, 1/2)`, at distance `1/2 < 1` from the origin, and the
sum of three squares has worst case `(1/2, 1/2, 1/2)`, at distance `3/4 < 1`; both therefore enjoy
the property.  (For four squares the worst case is at distance exactly `1` and the descent stops
working.)

## Main results

* `InverseGalois.CFT.exists_int_sq_add_sq_of_int_sq_eq`: an integer `n` admitting integers
  `v₁, v₂, t` with `t > 0` and `v₁ ^ 2 + v₂ ^ 2 = n * t ^ 2` is a sum of two integer squares.
* `InverseGalois.CFT.exists_int_three_sq_of_int_sq_eq`: the same statement for three squares.
* `InverseGalois.CFT.exists_int_sq_add_sq_of_rat`: an integer that is a sum of two rational
  squares is a sum of two integer squares.
* `InverseGalois.CFT.exists_int_three_sq_of_rat`: an integer that is a sum of three rational
  squares is a sum of three integer squares.
-/

namespace InverseGalois.CFT

/-- Every integer `v` is within half of a multiple of a positive integer `t`: there are integers
`w` and `d` with `v = t * w + d` and `4 * d ^ 2 ≤ t ^ 2`. -/
theorem exists_nearest_multiple (t v : ℤ) (ht : 0 < t) :
    ∃ w d : ℤ, v = t * w + d ∧ 4 * d ^ 2 ≤ t ^ 2 := by
  obtain ⟨q, r, hv, h2, h3⟩ : ∃ q r : ℤ, v = t * q + r ∧ 0 ≤ r ∧ r < t :=
    ⟨v / t, v % t, by rw [Int.emod_def]; ring, Int.emod_nonneg v ht.ne',
      Int.emod_lt_of_pos v ht⟩
  subst hv
  rcases le_or_gt (2 * r) t with h | h
  · exact ⟨q, r, rfl, by nlinarith⟩
  · exact ⟨q + 1, r - t, by ring, by nlinarith⟩

/-- The Davenport–Cassels descent step for the sum of two squares.  From a representation
`(t * w₁ + d₁) ^ 2 + (t * w₂ + d₂) ^ 2 = n * t ^ 2` one manufactures a new representation with
denominator `T` satisfying `t * T = d₁ ^ 2 + d₂ ^ 2`. -/
theorem exists_descent_two (n w₁ w₂ d₁ d₂ t : ℤ)
    (hv : (t * w₁ + d₁) ^ 2 + (t * w₂ + d₂) ^ 2 = n * t ^ 2) :
    ∃ V₁ V₂ T : ℤ, V₁ ^ 2 + V₂ ^ 2 = n * T ^ 2 ∧ t * T = d₁ ^ 2 + d₂ ^ 2 := by
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = w₁ ^ 2 + w₂ ^ 2 - n := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ,
      B = 2 * (n * t - ((t * w₁ + d₁) * w₁ + (t * w₂ + d₂) * w₂)) := ⟨_, rfl⟩
  refine ⟨A * (t * w₁ + d₁) + B * w₁, A * (t * w₂ + d₂) + B * w₂, A * t + B, ?_, ?_⟩
  · subst hB; subst hA
    linear_combination (w₁ ^ 2 + w₂ ^ 2 - n) ^ 2 * hv
  · subst hB; subst hA
    linear_combination -hv

/-- The Davenport–Cassels descent step for the sum of three squares.  From a representation
`(t * w₁ + d₁) ^ 2 + (t * w₂ + d₂) ^ 2 + (t * w₃ + d₃) ^ 2 = n * t ^ 2` one manufactures a new
representation with denominator `T` satisfying `t * T = d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2`. -/
theorem exists_descent_three (n w₁ w₂ w₃ d₁ d₂ d₃ t : ℤ)
    (hv : (t * w₁ + d₁) ^ 2 + (t * w₂ + d₂) ^ 2 + (t * w₃ + d₃) ^ 2 = n * t ^ 2) :
    ∃ V₁ V₂ V₃ T : ℤ, V₁ ^ 2 + V₂ ^ 2 + V₃ ^ 2 = n * T ^ 2 ∧
      t * T = d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2 := by
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2 - n := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = 2 * (n * t -
      ((t * w₁ + d₁) * w₁ + (t * w₂ + d₂) * w₂ + (t * w₃ + d₃) * w₃)) := ⟨_, rfl⟩
  refine ⟨A * (t * w₁ + d₁) + B * w₁, A * (t * w₂ + d₂) + B * w₂,
    A * (t * w₃ + d₃) + B * w₃, A * t + B, ?_, ?_⟩
  · subst hB; subst hA
    linear_combination (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2 - n) ^ 2 * hv
  · subst hB; subst hA
    linear_combination -hv

/-- The two-square descent, run by induction on a bound `m` for the denominator `t`. -/
theorem exists_int_sq_add_sq_aux (m : ℕ) : ∀ n v₁ v₂ t : ℤ, t.toNat ≤ m → 0 < t →
    v₁ ^ 2 + v₂ ^ 2 = n * t ^ 2 → ∃ a b : ℤ, n = a ^ 2 + b ^ 2 := by
  induction m with
  | zero => intro _ _ _ t hm ht _; exact absurd hm (by omega)
  | succ m ih =>
    intro n v₁ v₂ t hm ht hv
    obtain ⟨w₁, d₁, rfl, hd₁⟩ := exists_nearest_multiple t v₁ ht
    obtain ⟨w₂, d₂, rfl, hd₂⟩ := exists_nearest_multiple t v₂ ht
    obtain ⟨V₁, V₂, T, hV, hT⟩ := exists_descent_two n w₁ w₂ d₁ d₂ t hv
    have hT0 : 0 ≤ T := by nlinarith [sq_nonneg d₁, sq_nonneg d₂]
    rcases eq_or_lt_of_le hT0 with hz | hz
    · have e1 : d₁ = 0 :=
        pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          (le_antisymm (by nlinarith [sq_nonneg d₂]) (sq_nonneg d₁))
      have e2 : d₂ = 0 :=
        pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          (le_antisymm (by nlinarith [sq_nonneg d₁]) (sq_nonneg d₂))
      subst e1; subst e2
      refine ⟨w₁, w₂, ?_⟩
      have ht2 : t ^ 2 ≠ 0 := pow_ne_zero _ ht.ne'
      have hc : t ^ 2 * (w₁ ^ 2 + w₂ ^ 2) = t ^ 2 * n := by linear_combination hv
      exact (mul_left_cancel₀ ht2 hc).symm
    · have hlt : T < t := by nlinarith
      exact ih n V₁ V₂ T (by omega) hz hV

/-- The three-square descent, run by induction on a bound `m` for the denominator `t`. -/
theorem exists_int_three_sq_aux (m : ℕ) : ∀ n v₁ v₂ v₃ t : ℤ, t.toNat ≤ m → 0 < t →
    v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2 = n * t ^ 2 → ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  induction m with
  | zero => intro _ _ _ _ t hm ht _; exact absurd hm (by omega)
  | succ m ih =>
    intro n v₁ v₂ v₃ t hm ht hv
    obtain ⟨w₁, d₁, rfl, hd₁⟩ := exists_nearest_multiple t v₁ ht
    obtain ⟨w₂, d₂, rfl, hd₂⟩ := exists_nearest_multiple t v₂ ht
    obtain ⟨w₃, d₃, rfl, hd₃⟩ := exists_nearest_multiple t v₃ ht
    obtain ⟨V₁, V₂, V₃, T, hV, hT⟩ := exists_descent_three n w₁ w₂ w₃ d₁ d₂ d₃ t hv
    have hT0 : 0 ≤ T := by nlinarith [sq_nonneg d₁, sq_nonneg d₂, sq_nonneg d₃]
    rcases eq_or_lt_of_le hT0 with hz | hz
    · have e1 : d₁ = 0 :=
        pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          (le_antisymm (by nlinarith [sq_nonneg d₂, sq_nonneg d₃]) (sq_nonneg d₁))
      have e2 : d₂ = 0 :=
        pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          (le_antisymm (by nlinarith [sq_nonneg d₁, sq_nonneg d₃]) (sq_nonneg d₂))
      have e3 : d₃ = 0 :=
        pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          (le_antisymm (by nlinarith [sq_nonneg d₁, sq_nonneg d₂]) (sq_nonneg d₃))
      subst e1; subst e2; subst e3
      refine ⟨w₁, w₂, w₃, ?_⟩
      have ht2 : t ^ 2 ≠ 0 := pow_ne_zero _ ht.ne'
      have hc : t ^ 2 * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2) = t ^ 2 * n := by linear_combination hv
      exact (mul_left_cancel₀ ht2 hc).symm
    · have hlt : T < t := by nlinarith
      exact ih n V₁ V₂ V₃ T (by omega) hz hV

/-- **Davenport–Cassels for sums of two squares, integral form.**  If some positive integer `t`
scales a two-square representation of `n` into the integers, then `n` is a sum of two integer
squares. -/
theorem exists_int_sq_add_sq_of_int_sq_eq (n : ℤ)
    (h : ∃ v₁ v₂ t : ℤ, 0 < t ∧ v₁ ^ 2 + v₂ ^ 2 = n * t ^ 2) :
    ∃ a b : ℤ, n = a ^ 2 + b ^ 2 := by
  obtain ⟨v₁, v₂, t, ht, hv⟩ := h
  exact exists_int_sq_add_sq_aux t.toNat n v₁ v₂ t le_rfl ht hv

/-- **Davenport–Cassels for sums of three squares, integral form.**  If some positive integer `t`
scales a three-square representation of `n` into the integers, then `n` is a sum of three integer
squares. -/
theorem exists_int_three_sq_of_int_sq_eq (n : ℤ)
    (h : ∃ v₁ v₂ v₃ t : ℤ, 0 < t ∧ v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2 = n * t ^ 2) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨v₁, v₂, v₃, t, ht, hv⟩ := h
  exact exists_int_three_sq_aux t.toNat n v₁ v₂ v₃ t le_rfl ht hv

/-- Every rational number becomes an integer after multiplication by a positive integer. -/
theorem exists_int_eq_mul_rat (x : ℚ) : ∃ v t : ℤ, 0 < t ∧ (v : ℚ) = (t : ℚ) * x := by
  refine ⟨x.num, (x.den : ℤ), by exact_mod_cast x.pos, ?_⟩
  push_cast
  rw [mul_comm, ← div_eq_iff (by exact_mod_cast x.den_ne_zero), Rat.num_div_den]

/-- **Davenport–Cassels for sums of two squares.**  An integer that is a sum of two rational
squares is a sum of two integer squares. -/
theorem exists_int_sq_add_sq_of_rat {n : ℤ} (h : ∃ x y : ℚ, (n : ℚ) = x ^ 2 + y ^ 2) :
    ∃ a b : ℤ, n = a ^ 2 + b ^ 2 := by
  obtain ⟨x, y, hxy⟩ := h
  obtain ⟨p, s, hs, hp⟩ := exists_int_eq_mul_rat x
  obtain ⟨q, u, hu, hq⟩ := exists_int_eq_mul_rat y
  refine exists_int_sq_add_sq_of_int_sq_eq n ⟨p * u, q * s, s * u, mul_pos hs hu, ?_⟩
  have key : ((p * u : ℤ) : ℚ) ^ 2 + ((q * s : ℤ) : ℚ) ^ 2 = (n : ℚ) * ((s * u : ℤ) : ℚ) ^ 2 := by
    push_cast
    rw [hp, hq, hxy]
    ring
  exact_mod_cast key

/-- **Davenport–Cassels for sums of three squares.**  An integer that is a sum of three rational
squares is a sum of three integer squares. -/
theorem exists_int_three_sq_of_rat {n : ℤ} (h : ∃ x y z : ℚ, (n : ℚ) = x ^ 2 + y ^ 2 + z ^ 2) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨x, y, z, hxyz⟩ := h
  obtain ⟨p, s, hs, hp⟩ := exists_int_eq_mul_rat x
  obtain ⟨q, u, hu, hq⟩ := exists_int_eq_mul_rat y
  obtain ⟨r, e, he, hr⟩ := exists_int_eq_mul_rat z
  refine exists_int_three_sq_of_int_sq_eq n
    ⟨p * u * e, q * s * e, r * s * u, s * u * e, mul_pos (mul_pos hs hu) he, ?_⟩
  have key : ((p * u * e : ℤ) : ℚ) ^ 2 + ((q * s * e : ℤ) : ℚ) ^ 2 + ((r * s * u : ℤ) : ℚ) ^ 2
      = (n : ℚ) * ((s * u * e : ℤ) : ℚ) ^ 2 := by
    push_cast
    rw [hp, hq, hr, hxyz]
    ring
  exact_mod_cast key

end InverseGalois.CFT
