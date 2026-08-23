import Mathlib
import InverseGalois.CFT.Global.DavenportCassels
import InverseGalois.CFT.Global.ExistenceGeneral
import InverseGalois.CFT.Global.RationalSquareClasses
import InverseGalois.CFT.Global.SevenModEight
import InverseGalois.CFT.Global.TernaryForms
import InverseGalois.CFT.Global.ThreeSquaresOdd
import InverseGalois.CFT.Global.ThreeSquaresTwo

/-!
# The three-square theorem

A positive integer is a sum of three integer squares exactly when it is not of the shape
`4 ^ a * (8 * b + 7)`.

The quaternary form `X ^ 2 + Y ^ 2 + Z ^ 2` is not a scalar multiple of a ternary one, so the
Hasse principle for ternary forms does not apply to it directly.  The classical device is to write
a candidate `c` as `w + (a sum of one square)` where `w` is a value of `X ^ 2 + Y ^ 2` and
`c - w` is a square, that is, to find a rational `w` with

* `w` represented by the binary form `⟨1, 1⟩`, and
* `w` represented by the binary form `⟨-1, c⟩`, i.e. `w = -s ^ 2 + c t ^ 2`.

Both conditions are conditions on Hilbert symbols, namely `(-1, w) = 1` and `(-w, c) = 1`, so the
existence of `w` is exactly what Serre's existence theorem provides: one prescribes the symbols
place by place and asks for a global rational realising them.  The local witnesses come from the
fact that every `p`-adic number is a sum of three squares for `p` odd, and that a dyadic number is
one exactly when its negative is not a square: from a local representation `c = X ^ 2 + Y ^ 2 + Z ^
2` the element `W = X ^ 2 + Y ^ 2` satisfies both conditions on the nose, being visibly a value of
`⟨1, 1⟩` and equal to `-Z ^ 2 + c`, a value of `⟨-1, c⟩`.  Rational numbers meet every `p`-adic
square class, so `W` may be replaced by a rational.

The passage from rational to integral solutions is the Davenport–Cassels descent, and the dyadic
condition `-c` is not a square translates into the arithmetic shape `4 ^ a * (8 * b + 7)`.

## Main results

* `InverseGalois.CFT.hilbertSymbol_congr_of_isSquare_div`: the Hilbert symbol only depends on the
  square class of its second argument.
* `InverseGalois.CFT.exists_rat_witness_three_sq`: a local three-square representation yields a
  rational witness with the two prescribed local symbols.
* `InverseGalois.CFT.exists_three_sq_rat_of_int`: a positive integer whose negative is not a
  dyadic square is a sum of three rational squares.
* `InverseGalois.CFT.exists_three_sq_int`: **the three-square theorem**, a natural number is a sum
  of three integer squares exactly when it is not of the shape `4 ^ a * (8 * b + 7)`.
-/

namespace InverseGalois.CFT

open Local

/-- **The Hilbert symbol only depends on the square class of its second argument.** -/
theorem hilbertSymbol_congr_of_isSquare_div {K : Type*} [Field K] {a u v : K} (hu : u ≠ 0)
    (hv : v ≠ 0) (h : IsSquare (u / v)) : hilbertSymbol a u = hilbertSymbol a v := by
  obtain ⟨c, hc⟩ := h
  rw [div_eq_iff hv] at hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul] at hc
    exact hu hc
  rw [show u = v * c ^ 2 by linear_combination hc, hilbertSymbol_mul_sq_right _ _ _ hc0]

/-- **A local three-square representation produces a rational witness.**  If `c` is a sum of three
squares in `ℚ_[p]`, say `c = X ^ 2 + Y ^ 2 + Z ^ 2`, then the square class of `W = X ^ 2 + Y ^ 2`
contains a rational `w` with `(-1, w)_p = 1`, because `W` is a value of `⟨1, 1⟩`, and with
`(c, w)_p = (c, -1)_p`, because `W = -Z ^ 2 + c` is a value of `⟨-1, c⟩`.  When `W` vanishes the
number `c` is a square and every symbol involving it is trivial. -/
theorem exists_rat_witness_three_sq {c : ℚ} (hc : c ≠ 0) (p : Nat.Primes)
    (h : ∃ X Y Z : ℚ_[(p : ℕ)], ((c : ℚ_[(p : ℕ)])) = X ^ 2 + Y ^ 2 + Z ^ 2) :
    ∃ w : ℚ, w ≠ 0 ∧ hilbertSymbolAt p ((-1 : ℚ)) w = 1 ∧
      hilbertSymbolAt p c w = hilbertSymbolAt p c ((-1 : ℚ)) := by
  obtain ⟨X, Y, Z, hXYZ⟩ := h
  have hcp : ((c : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using hc
  by_cases hW : X ^ 2 + Y ^ 2 = 0
  · have hcsq : IsSquare ((c : ℚ_[(p : ℕ)])) := ⟨Z, by rw [hXYZ, hW]; ring⟩
    refine ⟨1, one_ne_zero, ?_, ?_⟩
    · unfold hilbertSymbolAt
      exact hilbertSymbol_of_isSquare_right _ _ ⟨1, by push_cast; ring⟩
    · unfold hilbertSymbolAt
      rw [hilbertSymbol_of_isSquare_left _ _ hcsq, hilbertSymbol_of_isSquare_left _ _ hcsq]
  · obtain ⟨w, hw0, hwsq⟩ := exists_rat_isSquare_div hW
    have hwp : ((w : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using hw0
    have h1 : hilbertSymbol ((-1 : ℚ_[(p : ℕ)])) (X ^ 2 + Y ^ 2) = 1 := by
      rw [hilbertSymbol_comm]
      have hrep := (exists_repr_iff_hilbertSymbol (K := ℚ_[(p : ℕ)]) (α := 1) (β := 1)
        (c := X ^ 2 + Y ^ 2) one_ne_zero one_ne_zero).1 ⟨X, Y, by ring⟩
      simpa using hrep
    have h2 : hilbertSymbol (-(X ^ 2 + Y ^ 2)) ((c : ℚ_[(p : ℕ)])) = 1 := by
      have hrep := (exists_repr_iff_hilbertSymbol (K := ℚ_[(p : ℕ)]) (α := -1)
        (β := ((c : ℚ_[(p : ℕ)]))) (c := X ^ 2 + Y ^ 2) (by norm_num) hcp).1
        ⟨Z, 1, by linear_combination -hXYZ⟩
      simpa using hrep
    refine ⟨w, hw0, ?_, ?_⟩
    · unfold hilbertSymbolAt
      rw [show (((-1 : ℚ)) : ℚ_[(p : ℕ)]) = -1 by push_cast; ring,
        ← hilbertSymbol_congr_of_isSquare_div hW hwp hwsq]
      exact h1
    · have hsq' : IsSquare ((-(X ^ 2 + Y ^ 2)) / (-((w : ℚ_[(p : ℕ)])))) := by
        rw [neg_div_neg_eq]
        exact hwsq
      have h3 : hilbertSymbolAt p c ((-w : ℚ)) = 1 := by
        unfold hilbertSymbolAt
        rw [show (((-w : ℚ)) : ℚ_[(p : ℕ)]) = -((w : ℚ_[(p : ℕ)])) by push_cast; ring,
          ← hilbertSymbol_congr_of_isSquare_div (neg_ne_zero.2 hW) (neg_ne_zero.2 hwp) hsq',
          hilbertSymbol_comm]
        exact h2
      have h4 := hilbertSymbolAt_mul_right' (p := p) (a := c) (b := ((-1 : ℚ))) (b' := w) hc
        (by norm_num) hw0
      rw [show ((-1 : ℚ) * w) = -w by ring, h3] at h4
      rcases hilbertSymbolAt_eq_one_or p c ((-1 : ℚ)) with hA | hA
      · rw [hA] at h4 ⊢
        linarith
      · rw [hA] at h4 ⊢
        linarith

/-- **Three squares over the rational field.**  A positive integer whose negative is not a square
in the dyadic field is a sum of three rational squares. -/
theorem exists_three_sq_rat_of_int {c : ℤ} (hc : 0 < c)
    (h2 : ¬ IsSquare (-(((c : ℚ)) : ℚ_[2]))) :
    ∃ x y z : ℚ, ((c : ℚ)) = x ^ 2 + y ^ 2 + z ^ 2 := by
  classical
  have hcQ : ((c : ℚ)) ≠ 0 := Int.cast_ne_zero.2 hc.ne'
  have hcpos : (0 : ℚ) < ((c : ℚ)) := Int.cast_pos.2 hc
  have hm1 : (((-1 : ℤ)) : ℚ) = ((-1 : ℚ)) := by norm_num
  have hneg1 : ((-1 : ℚ)) ≠ 0 := by norm_num
  have hloc : ∀ p : Nat.Primes, ∃ X Y Z : ℚ_[(p : ℕ)],
      ((((c : ℚ)) : ℚ_[(p : ℕ)])) = X ^ 2 + Y ^ 2 + Z ^ 2 := by
    intro p
    rcases eq_or_ne ((p : ℕ)) 2 with hp | hp
    · have hpe : p = primeTwo := Subtype.ext hp
      subst hpe
      have hcp : ((((c : ℚ)) : ℚ_[2])) ≠ 0 := by simpa using hcQ
      exact exists_three_sq_two_of_not_isSquare_neg hcp h2
    · exact exists_three_sq_of_odd hp _
  set T : Finset Nat.Primes := (finite_mulSupport_hilbertSymbolAt hcQ hneg1).toFinset with hTdef
  have hTout : ∀ p ∉ T, hilbertSymbolAt p ((c : ℚ)) ((-1 : ℚ)) = 1 := by
    intro p hp
    by_contra hne
    exact hp (by rw [hTdef]; exact Set.Finite.mem_toFinset _ |>.2 hne)
  have hprodb : (1 : ℤ) * ∏ p ∈ T, hilbertSymbolAt p ((c : ℚ)) ((-1 : ℚ)) = 1 := by
    have hrec := hilbertProduct_eq_one hcQ hneg1
    rw [hilbertProduct_eq_prod_of_subset _ _ T hTout] at hrec
    have hreal : hilbertSymbol ((((c : ℚ)) : ℝ)) ((((-1 : ℚ)) : ℝ)) = 1 := by
      rw [hilbertSymbol_comm]
      exact hilbertSymbol_real_of_pos_right (by norm_num) (by exact_mod_cast hcpos)
    rwa [hreal] at hrec
  have hlocp : ∀ p : Nat.Primes, ∃ w : ℚ, w ≠ 0 ∧
      hilbertSymbolAt p (((-1 : ℤ) : ℚ)) w = (1 : ℤ) ∧
      hilbertSymbolAt p ((c : ℚ)) w = hilbertSymbolAt p ((c : ℚ)) ((-1 : ℚ)) := by
    intro p
    obtain ⟨w, hw0, hw1, hw2⟩ := exists_rat_witness_three_sq hcQ p (hloc p)
    exact ⟨w, hw0, by rw [hm1]; exact hw1, hw2⟩
  have hlocr : ∃ w : ℚ, w ≠ 0 ∧
      hilbertSymbol (((((-1 : ℤ) : ℚ)) : ℝ)) ((w : ℝ)) = (1 : ℤ) ∧
      hilbertSymbol (((((c : ℤ) : ℚ)) : ℝ)) ((w : ℝ)) = (1 : ℤ) := by
    refine ⟨1, one_ne_zero, ?_, ?_⟩
    · exact hilbertSymbol_real_of_pos_right (by norm_num) (by norm_num)
    · exact hilbertSymbol_real_of_pos_right (by exact_mod_cast hc.ne') (by norm_num)
  obtain ⟨x, hx0, hxa, hxb, -, -⟩ :=
    exists_rat_hilbert_prescribed_two (a := (-1 : ℤ)) (b := c) (by norm_num) hc.ne'
      (fun _ => (1 : ℤ)) (fun p => hilbertSymbolAt p ((c : ℚ)) ((-1 : ℚ))) 1 1 T
      (fun _ _ => rfl) hTout (by simp) hprodb hlocp hlocr
  have hg1 : hilbertSymbol ((-1 : ℚ)) x = 1 :=
    hilbertSymbol_rat_of_forall_finite hneg1 hx0 fun p => by simpa using hxa p
  have hg2 : hilbertSymbol (-x) ((c : ℚ)) = 1 := by
    refine hilbertSymbol_rat_of_forall_finite (neg_ne_zero.2 hx0) hcQ fun p => ?_
    have h4 := hilbertSymbolAt_mul_right' (p := p) (a := ((c : ℚ))) (b := ((-1 : ℚ)))
      (b' := x) hcQ hneg1 hx0
    rw [show ((-1 : ℚ) * x) = -x by ring, hxb p] at h4
    rw [hilbertSymbolAt_comm, h4]
    rcases hilbertSymbolAt_eq_one_or p ((c : ℚ)) ((-1 : ℚ)) with hA | hA
    · rw [hA]; norm_num
    · rw [hA]; norm_num
  obtain ⟨u, v, huv⟩ := (exists_repr_iff_hilbertSymbol (K := ℚ) (α := 1) (β := 1) (c := x)
    one_ne_zero one_ne_zero).2 (by
      rw [one_mul, show (-((1 : ℚ) * 1)) = -1 by norm_num, hilbertSymbol_comm]
      exact hg1)
  obtain ⟨s, t, hst⟩ := (exists_repr_iff_hilbertSymbol (K := ℚ) (α := -1) (β := ((c : ℚ)))
    (c := x) (by norm_num) hcQ).2 (by
      rw [show ((-1 : ℚ) * x) = -x by ring, show (-((-1 : ℚ) * ((c : ℚ)))) = ((c : ℚ)) by ring]
      exact hg2)
  have ht : t ≠ 0 := by
    rintro rfl
    refine hx0 ?_
    have hx : x = u ^ 2 + v ^ 2 := by linear_combination huv
    have hx' : x = -s ^ 2 := by rw [hst]; ring
    linarith [sq_nonneg u, sq_nonneg v, sq_nonneg s]
  have hct : ((c : ℚ)) * t ^ 2 = u ^ 2 + v ^ 2 + s ^ 2 := by linear_combination huv - hst
  refine ⟨u / t, v / t, s / t, ?_⟩
  field_simp
  linear_combination hct

/-- **The three-square theorem.**  A natural number is a sum of three integer squares exactly when
it is not of the shape `4 ^ a * (8 * b + 7)`. -/
theorem exists_three_sq_int {n : ℕ} :
    (∃ x y z : ℤ, (n : ℤ) = x ^ 2 + y ^ 2 + z ^ 2) ↔ ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) := by
  constructor
  · rintro ⟨x, y, z, hxyz⟩ ⟨a, b, hab⟩
    have hn : 0 < n := by
      rw [hab]
      positivity
    have hne : ((n : ℚ_[2])) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    refine not_exists_three_sq_two_of_isSquare_neg hne
      ((isSquare_neg_natCast_padic_two_iff hn).2 ⟨a, b, hab⟩) ?_
    refine ⟨((x : ℚ_[2])), ((y : ℚ_[2])), ((z : ℚ_[2])), ?_⟩
    have hcast := congrArg (fun m : ℤ => ((m : ℚ_[2]))) hxyz
    push_cast at hcast
    linear_combination hcast
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, 0, 0, by norm_num⟩
    have h2 : ¬ IsSquare (-(((((n : ℤ)) : ℚ)) : ℚ_[2])) := by
      rw [show (((((n : ℤ)) : ℚ)) : ℚ_[2]) = ((n : ℚ_[2])) by push_cast; ring,
        isSquare_neg_natCast_padic_two_iff hn]
      exact h
    exact exists_int_three_sq_of_rat (exists_three_sq_rat_of_int (by exact_mod_cast hn) h2)

/-- **Every natural number not of the shape `4 ^ a * (8 * b + 7)` is a sum of three squares.** -/
theorem exists_three_sq_of_not_four_pow_mul {n : ℕ} (h : ∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) :
    ∃ x y z : ℤ, (n : ℤ) = x ^ 2 + y ^ 2 + z ^ 2 :=
  exists_three_sq_int.2 fun ⟨a, b, hab⟩ => h a b hab

end InverseGalois.CFT
