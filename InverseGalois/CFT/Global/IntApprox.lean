import Mathlib
import InverseGalois.CFT.Global.SquareClassApprox

/-!
# Weak approximation of `p`-adic integers by a rational integer

Fix finitely many primes and, at each of them, a `p`-adic number of norm at most one.  This file
produces a single element of `ℤ` that is simultaneously as close as one likes to all of the
prescribed targets, and which in addition can be taken larger than any prescribed bound.

The proof has two halves.  On the analytic side, a `p`-adic integer is approximated to within
`p ^ (-N)` by an ordinary integer, namely one of the truncations `PadicInt.appr`; conversely, an
integer divisible by `p ^ N` has `p`-adic norm at most `p ^ (-N)`.  On the arithmetic side, the
Chinese remainder theorem of `InverseGalois.CFT.exists_int_modEq_prime_pow` matches prescribed
residues modulo `p ^ N` at all the chosen primes at once, and
`InverseGalois.CFT.exists_int_gt_and_modEq` does so with the solution above a given bound.  The
two halves are glued by the ultrametric inequality, and a single exponent `N` serving every prime
is obtained by summing the exponents required one prime at a time.

A separate, purely local statement records that any `p`-adic number becomes integral after
multiplication by a large enough power of `p`.

## Main results

* `InverseGalois.CFT.exists_pow_mul_norm_le_one`: multiplying by a sufficiently large power of `p`
  makes any element of `ℚ_[p]` have norm at most one.
* `InverseGalois.CFT.exists_int_norm_sub_le_pow`: an element of `ℚ_[p]` of norm at most one is
  approximated to within `p ^ (-N)` by a rational integer.
* `InverseGalois.CFT.norm_intCast_sub_le_pow`: integers congruent modulo `p ^ N` are within
  `p ^ (-N)` of each other in `ℚ_[p]`.
* `InverseGalois.CFT.exists_int_norm_sub_lt`: **weak approximation by an integer** at finitely
  many primes simultaneously.
* `InverseGalois.CFT.exists_int_gt_and_norm_sub_lt`: the same, with the approximating integer
  above a prescribed bound.
-/

namespace InverseGalois.CFT

/-! ### The local statements -/

/-- A power of `p` clears the denominator of any `p`-adic number: for every `u : ℚ_[p]` there is
an exponent `n` with `‖p ^ n * u‖ ≤ 1`. -/
theorem exists_pow_mul_norm_le_one {p : ℕ} [Fact p.Prime] (u : ℚ_[p]) :
    ∃ n : ℕ, ‖((p : ℚ_[p])) ^ n * u‖ ≤ 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := 1 / (‖u‖ + 1))
    (by positivity) (inv_lt_one_of_one_lt₀ hp1)
  refine ⟨n, ?_⟩
  rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast, ← inv_pow]
  have hu : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have h1 : ((p : ℝ)⁻¹) ^ n * ‖u‖ ≤ (1 / (‖u‖ + 1)) * ‖u‖ :=
    mul_le_mul_of_nonneg_right hn.le hu
  have h2 : (1 / (‖u‖ + 1)) * ‖u‖ ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  linarith

/-- An element of `ℚ_[p]` of norm at most one is approximated to within `p ^ (-N)` by an integer:
one may take a truncation of the corresponding element of `ℤ_[p]`. -/
theorem exists_int_norm_sub_le_pow {p : ℕ} [Fact p.Prime] {y : ℚ_[p]} (hy : ‖y‖ ≤ 1) (N : ℕ) :
    ∃ r : ℤ, ‖((r : ℚ_[p])) - y‖ ≤ ((p : ℝ)⁻¹) ^ N := by
  set z : ℤ_[p] := ⟨y, hy⟩
  refine ⟨((z.appr N : ℕ) : ℤ), ?_⟩
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow (z - (z.appr N : ℤ_[p])) N).mpr
    (PadicInt.appr_spec N z)
  rw [zpow_neg, zpow_natCast, ← inv_pow] at h
  have hc : ‖((z - (z.appr N : ℤ_[p]) : ℤ_[p]) : ℚ_[p])‖ = ‖z - (z.appr N : ℤ_[p])‖ :=
    PadicInt.padic_norm_e_of_padicInt _
  rw [← hc, PadicInt.coe_sub] at h
  have hzc : ((z : ℤ_[p]) : ℚ_[p]) = y := rfl
  have hac : (((z.appr N : ℤ_[p]) : ℚ_[p])) = ((((z.appr N : ℕ) : ℤ) : ℚ_[p])) := by
    push_cast
    rfl
  rw [hzc, hac] at h
  rwa [norm_sub_rev]

/-- Two integers congruent modulo `p ^ N` are at `p`-adic distance at most `p ^ (-N)`. -/
theorem norm_intCast_sub_le_pow {p : ℕ} [Fact p.Prime] {x r : ℤ} {N : ℕ}
    (h : ((p : ℤ)) ^ N ∣ x - r) : ‖((x : ℚ_[p])) - (r : ℚ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ N := by
  have hc : ((x - r : ℤ) : ℚ_[p]) = (x : ℚ_[p]) - (r : ℚ_[p]) := by push_cast; ring
  have hdvd := (Padic.norm_int_le_pow_iff_dvd (x - r) N).mpr h
  rwa [hc, zpow_neg, zpow_natCast, ← inv_pow] at hdvd

/-! ### Simultaneous approximation -/

/-- The common core of the approximation statements: any family of solutions of the simultaneous
congruences constrained by a predicate `P` yields an integer satisfying `P` and approximating the
prescribed `p`-adic targets to the prescribed accuracy. -/
private theorem exists_int_norm_sub_lt_of_crt (S : Finset Nat.Primes)
    (y : ∀ p : Nat.Primes, ℚ_[(p : ℕ)]) (hy : ∀ p ∈ S, ‖y p‖ ≤ 1) (ε : Nat.Primes → ℝ)
    (hε : ∀ p ∈ S, 0 < ε p) (P : ℤ → Prop)
    (hP : ∀ (r : Nat.Primes → ℤ) (N : ℕ), ∃ x : ℤ, P x ∧ ∀ p ∈ S, ((p : ℤ) ^ N ∣ x - r p)) :
    ∃ X : ℤ, P X ∧ ∀ p ∈ S, ‖((X : ℚ_[(p : ℕ)])) - y p‖ < ε p := by
  classical
  have hone : ∀ p : Nat.Primes, (1 : ℝ) < ((p : ℕ) : ℝ) := by
    intro p
    exact_mod_cast p.2.one_lt
  have hexp : ∀ p : Nat.Primes, ∃ n : ℕ, p ∈ S → ((((p : ℕ) : ℝ))⁻¹) ^ n < ε p := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (hε p hp) (inv_lt_one_of_one_lt₀ (hone p))
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose n hn using hexp
  set N : ℕ := ∑ q ∈ S, n q
  have hres : ∀ p : Nat.Primes, ∃ r : ℤ, p ∈ S →
      ‖((r : ℚ_[(p : ℕ)])) - y p‖ ≤ ((((p : ℕ) : ℝ))⁻¹) ^ N := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨r, hr⟩ := exists_int_norm_sub_le_pow (hy p hp) N
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose r hr using hres
  obtain ⟨X, hPX, hX⟩ := hP r N
  refine ⟨X, hPX, fun p hp => ?_⟩
  have hinv0 : (0 : ℝ) ≤ (((p : ℕ) : ℝ))⁻¹ := by positivity
  have hinv1 : (((p : ℕ) : ℝ))⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ (hone p)).le
  have hle : n p ≤ N := Finset.single_le_sum (f := fun q => n q) (fun _ _ => Nat.zero_le _) hp
  have hmono : ((((p : ℕ) : ℝ))⁻¹) ^ N ≤ ((((p : ℕ) : ℝ))⁻¹) ^ (n p) :=
    pow_le_pow_of_le_one hinv0 hinv1 hle
  have h1 : ‖((X : ℚ_[(p : ℕ)])) - (r p : ℚ_[(p : ℕ)])‖ ≤ ((((p : ℕ) : ℝ))⁻¹) ^ N :=
    norm_intCast_sub_le_pow (hX p hp)
  have h2 : ‖((r p : ℚ_[(p : ℕ)])) - y p‖ ≤ ((((p : ℕ) : ℝ))⁻¹) ^ N := hr p hp
  have hsplit : ((X : ℚ_[(p : ℕ)])) - y p
      = (((X : ℚ_[(p : ℕ)])) - (r p : ℚ_[(p : ℕ)])) + (((r p : ℚ_[(p : ℕ)])) - y p) := by
    ring
  have hult : ‖((X : ℚ_[(p : ℕ)])) - y p‖ ≤ ((((p : ℕ) : ℝ))⁻¹) ^ N := by
    rw [hsplit]
    exact (Padic.nonarchimedean _ _).trans (max_le h1 h2)
  exact lt_of_le_of_lt (hult.trans hmono) (hn p hp)

/-- **Weak approximation by an integer.**  Given, at each prime of a finite set, a `p`-adic target
of norm at most one and a positive accuracy, there is a single rational integer within the
prescribed accuracy of every target. -/
theorem exists_int_norm_sub_lt (S : Finset Nat.Primes) (y : ∀ p : Nat.Primes, ℚ_[(p : ℕ)])
    (hy : ∀ p ∈ S, ‖y p‖ ≤ 1) (ε : Nat.Primes → ℝ) (hε : ∀ p ∈ S, 0 < ε p) :
    ∃ X : ℤ, ∀ p ∈ S, ‖((X : ℚ_[(p : ℕ)])) - y p‖ < ε p := by
  obtain ⟨X, -, hX⟩ := exists_int_norm_sub_lt_of_crt S y hy ε hε (fun _ => True)
    fun r N => ⟨(exists_int_modEq_prime_pow S r N).choose, trivial,
      (exists_int_modEq_prime_pow S r N).choose_spec⟩
  exact ⟨X, hX⟩

/-- **Weak approximation by a large integer.**  The approximating integer of
`InverseGalois.CFT.exists_int_norm_sub_lt` can moreover be taken above any prescribed bound. -/
theorem exists_int_gt_and_norm_sub_lt (S : Finset Nat.Primes) (y : ∀ p : Nat.Primes, ℚ_[(p : ℕ)])
    (hy : ∀ p ∈ S, ‖y p‖ ≤ 1) (ε : Nat.Primes → ℝ) (hε : ∀ p ∈ S, 0 < ε p) (B : ℤ) :
    ∃ X : ℤ, B < X ∧ ∀ p ∈ S, ‖((X : ℚ_[(p : ℕ)])) - y p‖ < ε p :=
  exists_int_norm_sub_lt_of_crt S y hy ε hε (fun x => B < x)
    fun r N => exists_int_gt_and_modEq S r N B

end InverseGalois.CFT
