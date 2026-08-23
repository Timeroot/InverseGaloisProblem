import Mathlib
import InverseGalois.CFT.Global.DiagRepr
import InverseGalois.CFT.Global.OddUnitIsotropy

/-!
# Diagonal forms in five variables over the `p`-adic numbers

At an odd finite place, a diagonal quadratic form in five or more variables is always isotropic.
Writing each coefficient as a power of `p` times a number of absolute value one, the exponents of
five coefficients cannot avoid having three of the same parity; the corresponding ternary subform
is, after the substitution that removes the even part of those powers, a form in three coefficients
of absolute value one, hence isotropic at an odd place.  Rescaling the solution by the removed
powers of `p` returns a solution of the original form.

Combined with the Hasse principle, this cuts the list of places to be examined down to two: a
diagonal form over the rational field in at least five variables is isotropic as soon as it is
isotropic over the real field and over the field of dyadic numbers, and a form in at least four
variables represents a rational number as soon as it does so over those two fields.

## Main results

* `InverseGalois.CFT.exists_unit_zpow`: a nonzero `p`-adic number is a power of `p` times a number
  of absolute value one.
* `InverseGalois.CFT.isDiagIsotropic_padic_of_odd`: at an odd finite place, a diagonal form in at
  least five variables is isotropic.
* `InverseGalois.CFT.isDiagIsotropic_rat_iff_two_real`: the Hasse principle for a diagonal form in
  at least five variables involves only the real and the dyadic place.
* `InverseGalois.CFT.exists_repr_rat_iff_two_real`: the Hasse principle for the representation of a
  rational number by a diagonal form in at least four variables involves only the real and the
  dyadic place.
-/

namespace InverseGalois.CFT

open Local

/-- **Every nonzero `p`-adic number is a power of `p` times a number of absolute value one.**
The exponent is the valuation, and the remaining factor is the number divided by that power. -/
theorem exists_unit_zpow {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ (m : ℤ) (u : ℚ_[p]), ‖u‖ = 1 ∧ x = (p : ℚ_[p]) ^ m * u := by
  have hp0 : ((p : ℕ) : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out : p.Prime))
  refine ⟨x.valuation, x / (p : ℚ_[p]) ^ x.valuation, ?_, by field_simp⟩
  rw [norm_div, Padic.norm_eq_zpow_neg_valuation hx, norm_zpow, Padic.norm_p, inv_zpow,
    ← zpow_neg]
  have : ((p : ℝ)) ^ (-x.valuation) ≠ 0 := by
    refine zpow_ne_zero _ ?_
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact div_self this

/-- **Three coefficients whose valuations share a parity make a form isotropic at an odd place.**
Removing from each of the three an even power of `p` leaves a common power of `p` times three
numbers of absolute value one, and a ternary form in such numbers is isotropic. -/
theorem isotropic_of_three_parity {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ} {a : Fin n → ℚ_[p]}
    {j₀ j₁ j₂ : Fin n} (h01 : j₀ ≠ j₁) (h02 : j₀ ≠ j₂) (h12 : j₁ ≠ j₂) (s : ℤ)
    (h₀ : ∃ (k : ℤ) (v : ℚ_[p]), ‖v‖ = 1 ∧ a j₀ = (p : ℚ_[p]) ^ (2 * k) * ((p : ℚ_[p]) ^ s * v))
    (h₁ : ∃ (k : ℤ) (v : ℚ_[p]), ‖v‖ = 1 ∧ a j₁ = (p : ℚ_[p]) ^ (2 * k) * ((p : ℚ_[p]) ^ s * v))
    (h₂ : ∃ (k : ℤ) (v : ℚ_[p]), ‖v‖ = 1 ∧ a j₂ = (p : ℚ_[p]) ^ (2 * k) * ((p : ℚ_[p]) ^ s * v)) :
    IsDiagIsotropic a := by
  have hp0 : ((p : ℕ) : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out : p.Prime))
  have hsq : ∀ k : ℤ, ((p : ℚ_[p]) ^ k) ^ 2 = (p : ℚ_[p]) ^ (2 * k) := by
    intro k
    rw [← zpow_natCast ((p : ℚ_[p]) ^ k) 2, ← zpow_mul, mul_comm]
    norm_cast
  obtain ⟨k₀, v₀, hv₀, he₀⟩ := h₀
  obtain ⟨k₁, v₁, hv₁, he₁⟩ := h₁
  obtain ⟨k₂, v₂, hv₂, he₂⟩ := h₂
  obtain ⟨x, y, z, hne, hxyz⟩ := isotropic_ternary_of_norm_one hp hv₀ hv₁ hv₂
  have hstep : ∀ (k : ℤ) (v w : ℚ_[p]),
      (p : ℚ_[p]) ^ (2 * k) * ((p : ℚ_[p]) ^ s * v) * (w / (p : ℚ_[p]) ^ k) ^ 2
        = (p : ℚ_[p]) ^ s * (v * w ^ 2) := by
    intro k v w
    have hk : ((p : ℚ_[p]) ^ (2 * k)) ≠ 0 := zpow_ne_zero _ hp0
    rw [div_pow, hsq]
    field_simp
  refine isDiagIsotropic_of_three h01 h02 h12 (x := x / (p : ℚ_[p]) ^ k₀)
    (y := y / (p : ℚ_[p]) ^ k₁) (z := z / (p : ℚ_[p]) ^ k₂) ?_ ?_
  · rintro ⟨hx, hy, hz⟩
    refine hne ⟨?_, ?_, ?_⟩
    · exact (div_eq_zero_iff.mp hx).resolve_right (zpow_ne_zero _ hp0)
    · exact (div_eq_zero_iff.mp hy).resolve_right (zpow_ne_zero _ hp0)
    · exact (div_eq_zero_iff.mp hz).resolve_right (zpow_ne_zero _ hp0)
  · rw [he₀, he₁, he₂, hstep, hstep, hstep]
    linear_combination (p : ℚ_[p]) ^ s * hxyz

/-- **A diagonal form in at least five variables is isotropic at an odd finite place.**  Among
five valuations, three share a parity. -/
theorem isDiagIsotropic_padic_of_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ} (hn : 5 ≤ n)
    (a : Fin n → ℚ_[p]) : IsDiagIsotropic a := by
  classical
  have hp0 : ((p : ℕ) : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out : p.Prime))
  by_cases hzero : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hzero
    exact isDiagIsotropic_of_coeff_eq_zero hi
  push_neg at hzero
  choose m u hu hmu using fun i => exists_unit_zpow (hzero i)
  have hrepr : ∀ (s : ℤ) (j : Fin n), (∃ k : ℤ, m j = 2 * k + s) →
      ∃ (k : ℤ) (v : ℚ_[p]), ‖v‖ = 1 ∧
        a j = (p : ℚ_[p]) ^ (2 * k) * ((p : ℚ_[p]) ^ s * v) := by
    rintro s j ⟨k, hk⟩
    exact ⟨k, u j, hu j, by rw [hmu j, hk, zpow_add₀ hp0, mul_assoc]⟩
  have key : ∀ (s : ℤ) (S : Finset (Fin n)), 3 ≤ S.card →
      (∀ j ∈ S, ∃ k : ℤ, m j = 2 * k + s) → IsDiagIsotropic a := by
    intro s S hS hpar
    obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hS
    obtain ⟨j₀, j₁, j₂, h01, h02, h12, rfl⟩ := Finset.card_eq_three.mp hT
    refine isotropic_of_three_parity hp h01 h02 h12 s (hrepr s _ (hpar _ (hTS ?_)))
      (hrepr s _ (hpar _ (hTS ?_))) (hrepr s _ (hpar _ (hTS ?_)))
    · simp
    · simp
    · simp
  have hcard : (Finset.univ.filter fun i : Fin n => Even (m i)).card
      + (Finset.univ.filter fun i : Fin n => ¬ Even (m i)).card = n := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  rcases (by omega : 3 ≤ (Finset.univ.filter fun i : Fin n => Even (m i)).card ∨
      3 ≤ (Finset.univ.filter fun i : Fin n => ¬ Even (m i)).card) with h | h
  · refine key 0 _ h fun j hj => ?_
    obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hj).2
    exact ⟨k, by omega⟩
  · refine key 1 _ h fun j hj => ?_
    have hodd := (Finset.mem_filter.mp hj).2
    rw [Int.not_even_iff_odd] at hodd
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩

/-- **The Hasse principle in five or more variables involves only the real and the dyadic
place.**  Isotropy at every odd finite place is automatic. -/
theorem isDiagIsotropic_rat_iff_two_real {n : ℕ} (hn : 5 ≤ n) (a : Fin n → ℚ) :
    IsDiagIsotropic a ↔ (IsDiagIsotropic fun i => ((a i : ℚ_[2]))) ∧
      IsDiagIsotropic fun i => ((a i : ℝ)) := by
  refine ⟨fun h => ⟨h.map (Rat.castHom ℚ_[2]), h.map (Rat.castHom ℝ)⟩, fun h => ?_⟩
  refine (isDiagIsotropic_rat_iff a).mpr ⟨fun p => ?_, h.2⟩
  obtain ⟨q, hq⟩ := p
  haveI : Fact q.Prime := ⟨hq⟩
  rcases eq_or_ne q 2 with rfl | hne
  · exact h.1
  · exact isDiagIsotropic_padic_of_odd hne hn _

/-- **Representation in four or more variables involves only the real and the dyadic place.**
Adjoining a variable with the negated value turns representation into isotropy in five or more
variables. -/
theorem exists_repr_rat_iff_two_real {n : ℕ} (hn : 4 ≤ n) {a : Fin n → ℚ} (ha : ∀ i, a i ≠ 0)
    (s : ℚ) :
    (∃ x : Fin n → ℚ, s = ∑ i, a i * x i ^ 2) ↔
      (∃ x : Fin n → ℚ_[2], ((s : ℚ_[2])) = ∑ i, ((a i : ℚ_[2])) * x i ^ 2) ∧
        ∃ x : Fin n → ℝ, ((s : ℝ)) = ∑ i, ((a i : ℝ)) * x i ^ 2 := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨⟨fun i => ((x i : ℚ_[2])), ?_⟩, ⟨fun i => ((x i : ℝ)), ?_⟩⟩
    · rw [← cast_sum_sq a x, ← hx]
    · rw [← cast_sum_sq a x, ← hx]
  · rintro ⟨h2, hr⟩
    rcases eq_or_ne s 0 with rfl | _hs
    · exact ⟨0, by simp⟩
    have hb2 : IsDiagIsotropic fun i => (((Fin.cons (-s) a : Fin (n + 1) → ℚ) i : ℚ_[2])) := by
      rw [cast_cons, Rat.cast_neg]
      obtain ⟨x, hx⟩ := h2
      exact isDiagIsotropic_cons_of_repr hx
    have hbreal : IsDiagIsotropic fun i => (((Fin.cons (-s) a : Fin (n + 1) → ℚ) i : ℝ)) := by
      rw [cast_cons, Rat.cast_neg]
      obtain ⟨x, hx⟩ := hr
      exact isDiagIsotropic_cons_of_repr hx
    have hiso := (isDiagIsotropic_rat_iff_two_real (n := n + 1) (by omega) _).mpr ⟨hb2, hbreal⟩
    exact exists_repr_of_isDiagIsotropic_cons (by norm_num) ha hiso

end InverseGalois.CFT
