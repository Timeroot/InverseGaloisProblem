import Mathlib
import InverseGalois.CFT.Local.DyadicAnisotropic
import InverseGalois.CFT.Local.DyadicQuaternary
import InverseGalois.CFT.Local.OddAnisotropic
import InverseGalois.CFT.Global.DiagScale
import InverseGalois.CFT.Global.DiagRepr
import InverseGalois.CFT.Global.MatHasse
import InverseGalois.CFT.Global.OddQuinary
import InverseGalois.CFT.Global.RealSigns

/-!
# The `u`-invariant of the dyadic numbers, and Meyer's theorem

A diagonal quadratic form over `ℚ_[2]` in at least five variables is isotropic.  Every nonzero
`2`-adic number is a square times a unit or a square times twice a unit, and among five such
coefficients either all five are of the same kind — settled by the quinary unit form, after
dividing the whole form by two in the second case — or three are of one kind and one of the
other, which is the quaternary form of `DyadicQuaternary`.

Combined with the computation at the odd places and the sign criterion at the real place, this
gives **Meyer's theorem**: a diagonal quadratic form over `ℚ` in at least five variables is
isotropic exactly when it is indefinite.

## Main results

* `InverseGalois.CFT.Local.isDiagIsotropic_two`: a diagonal form over `ℚ_[2]` in at least five
  variables is isotropic; equivalently the `u`-invariant of `ℚ_[2]` is at most four.
* `InverseGalois.CFT.isDiagIsotropic_rat_iff_indefinite`: **Meyer's theorem**, a diagonal rational form in at
  least five variables is isotropic exactly when its coefficients are not all of one sign.
* `InverseGalois.CFT.exists_repr_rat_of_signs`: the representation form of the same statement.
* `InverseGalois.CFT.Local.isDiagIsotropic_padic`: the same at every finite place, so the
  `u`-invariant of a field of `p`-adic numbers is at most four.
* `InverseGalois.CFT.Local.exists_not_isDiagIsotropic_four_padic`: the bound is attained at every
  finite place, so that `u`-invariant is exactly four.
* `InverseGalois.CFT.isMatIsotropic_rat_iff_real`: Meyer's theorem for a form presented by an
  arbitrary symmetric rational matrix — such a form in at least five variables has a rational
  zero exactly when it has a real one.
* `InverseGalois.CFT.exists_repr_padic`: a `p`-adic diagonal form in at least five variables with
  nonvanishing coefficients represents every `p`-adic number.
* `InverseGalois.CFT.isMatIsotropic_padic`: the same isotropy statement for a form presented by an
  arbitrary symmetric `p`-adic matrix.
* `InverseGalois.CFT.not_isDiagIsotropic_one_rat`: over the rational field itself there is no such
  bound, a sum of squares in any number of variables being anisotropic.
-/

namespace InverseGalois.CFT.Local

open scoped Classical

/-- The norm of two in the dyadic numbers. -/
theorem norm_two_padic : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
  have := Padic.norm_p (p := 2)
  simpa using this

set_option maxRecDepth 8000 in
/-- Among five booleans that are not all equal, three agree and a fourth differs from them. -/
theorem exists_inj_pattern {e : Fin 5 → Bool} (h : ¬ ∀ i, e i = e 0) :
    ∃ f : Fin 4 → Fin 5, Function.Injective f ∧
      e (f 1) = e (f 0) ∧ e (f 2) = e (f 0) ∧ e (f 3) = !(e (f 0)) := by
  revert h
  revert e
  decide

/-- A diagonal dyadic form in four variables whose first three coefficients have valuation one
and whose last has valuation zero is isotropic. -/
theorem isDiagIsotropic_two_quaternary_swap {a : Fin 4 → ℚ_[2]} (h0 : ‖a 0‖ = (2 : ℝ)⁻¹)
    (h1 : ‖a 1‖ = (2 : ℝ)⁻¹) (h2 : ‖a 2‖ = (2 : ℝ)⁻¹) (h3 : ‖a 3‖ = 1) :
    IsDiagIsotropic a := by
  have hs : ∀ i : Fin 4, (![1, 1, 1, 2] : Fin 4 → ℚ_[2]) i ≠ 0 := by
    intro i
    fin_cases i <;> norm_num
  have hc : ((2 : ℚ_[2])⁻¹) ≠ 0 := by norm_num
  rw [← isDiagIsotropic_mul_sq (a := a) hs, ← isDiagIsotropic_const_mul hc]
  refine isDiagIsotropic_two_quaternary ?_ ?_ ?_ ?_ <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_three, one_pow, mul_one, norm_mul, norm_inv,
      norm_two_padic, h0, h1, h2, h3, norm_pow]
  · norm_num
  · norm_num
  · norm_num
  · norm_num

/-- A diagonal dyadic form in five variables with nonzero coefficients is isotropic. -/
theorem isDiagIsotropic_two_of_ne_zero_five {a : Fin 5 → ℚ_[2]} (ha : ∀ i, a i ≠ 0) :
    IsDiagIsotropic a := by
  choose s hs hns using fun i => exists_sq_mul_norm_eq (ha i)
  rw [← isDiagIsotropic_mul_sq hs]
  set b : Fin 5 → ℚ_[2] := fun i => a i * s i ^ 2 with hb
  have hbn : ∀ i, ‖b i‖ = 1 ∨ ‖b i‖ = (2 : ℝ)⁻¹ := hns
  set e : Fin 5 → Bool := fun i => if ‖b i‖ = 1 then false else true with he
  have hef : ∀ i, e i = false → ‖b i‖ = 1 := by
    intro i hi
    by_contra hne
    simp [he, hne] at hi
  have het : ∀ i, e i = true → ‖b i‖ = (2 : ℝ)⁻¹ := by
    intro i hi
    rcases hbn i with h | h
    · simp [he, h] at hi
    · exact h
  have hc : ((2 : ℚ_[2])⁻¹) ≠ 0 := by norm_num
  by_cases hconst : ∀ i, e i = e 0
  · cases h0 : e 0 with
    | false => exact isDiagIsotropic_two_of_norm_one_five fun i => hef i (by rw [hconst i, h0])
    | true =>
      rw [← isDiagIsotropic_const_mul hc]
      refine isDiagIsotropic_two_of_norm_one_five fun i => ?_
      rw [norm_mul, norm_inv, norm_two_padic, het i (by rw [hconst i, h0])]
      norm_num
  · obtain ⟨f, hf, h1, h2, h3⟩ := exists_inj_pattern hconst
    refine isDiagIsotropic_comp hf ?_
    cases h0 : e (f 0) with
    | false =>
      exact isDiagIsotropic_two_quaternary (hef _ h0) (hef _ (by rw [h1, h0]))
        (hef _ (by rw [h2, h0])) (het _ (by rw [h3, h0]; rfl))
    | true =>
      exact isDiagIsotropic_two_quaternary_swap (het _ h0) (het _ (by rw [h1, h0]))
        (het _ (by rw [h2, h0])) (hef _ (by rw [h3, h0]; rfl))

/-- A diagonal dyadic form in at least five variables is isotropic. -/
theorem isDiagIsotropic_two {n : ℕ} (hn : 5 ≤ n) (a : Fin n → ℚ_[2]) : IsDiagIsotropic a := by
  by_cases hz : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hz
    exact isDiagIsotropic_of_coeff_eq_zero hi
  · push_neg at hz
    refine isDiagIsotropic_comp
      (f := fun j : Fin 5 => (⟨j, lt_of_lt_of_le j.isLt hn⟩ : Fin n)) ?_
      (isDiagIsotropic_two_of_ne_zero_five fun j => hz _)
    intro i j hij
    have hval := congrArg Fin.val hij
    exact Fin.val_injective hval

/-- **The `u`-invariant of a field of `p`-adic numbers is at most four.**  A diagonal form in at
least five variables is isotropic at every finite place. -/
theorem isDiagIsotropic_padic {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 5 ≤ n) (a : Fin n → ℚ_[p]) :
    IsDiagIsotropic a := by
  rcases eq_or_ne p 2 with rfl | hne
  · exact isDiagIsotropic_two hn a
  · exact isDiagIsotropic_padic_of_odd hne hn a

/-- **The `u`-invariant of a field of `p`-adic numbers is exactly four.**  At the dyadic place the
sum of four squares is anisotropic, and at an odd place the norm form of the unramified quadratic
extension, summed with its multiple by the uniformiser, is. -/
theorem exists_not_isDiagIsotropic_four_padic {p : ℕ} [Fact p.Prime] :
    ∃ a : Fin 4 → ℚ_[p], (∀ i, a i ≠ 0) ∧ ¬ IsDiagIsotropic a := by
  rcases eq_or_ne p 2 with rfl | hne
  · exact exists_not_isDiagIsotropic_four
  · exact exists_not_isDiagIsotropic_four_odd hne

end InverseGalois.CFT.Local

namespace InverseGalois.CFT

open Local

/-- **Meyer's theorem.**  A diagonal quadratic form over the rational numbers in at least five
variables is isotropic exactly when it is indefinite: either a coefficient vanishes, or one
coefficient is negative and another positive. -/
theorem isDiagIsotropic_rat_iff_indefinite {n : ℕ} (hn : 5 ≤ n) (a : Fin n → ℚ) :
    IsDiagIsotropic a ↔ (∃ i, a i = 0) ∨ ∃ i j, a i < 0 ∧ 0 < a j := by
  rw [isDiagIsotropic_rat_iff_signs hn, and_iff_left (isDiagIsotropic_two hn _)]

/-- The representation form of Meyer's theorem: a diagonal rational form in at least five
variables with nonzero coefficients represents every nonzero rational number that the sign
condition at the real place allows. -/
theorem exists_repr_rat_of_signs {n : ℕ} (hn : 5 ≤ n) {a : Fin n → ℚ} (ha : ∀ i, a i ≠ 0)
    {t : ℚ} (ht : t ≠ 0) (hsign : ∃ i, 0 < a i * t) :
    ∃ x : Fin n → ℚ, t = ∑ i, a i * x i ^ 2 := by
  refine (exists_repr_rat_iff_signs (by omega) ha ht).mpr ⟨hsign, ?_⟩
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have haq : ∀ i, ((a i : ℚ_[2])) ≠ 0 := fun i => by exact_mod_cast ha i
  exact exists_repr_of_isDiagIsotropic h2 haq (isDiagIsotropic_two hn _) _

/-- **Meyer's theorem for an arbitrary rational quadratic form.**  A form presented by a symmetric
rational matrix in at least five variables has a nontrivial rational zero exactly when it has a
nontrivial real one. -/
theorem isMatIsotropic_rat_iff_real {n : ℕ} (hn : 5 ≤ n) {M : Matrix (Fin n) (Fin n) ℚ}
    (hM : M.IsSymm) :
    IsMatIsotropic M ↔ IsMatIsotropic (M.map fun q : ℚ => (q : ℝ)) := by
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  obtain ⟨P, d, hP, hPd⟩ := exists_transpose_mul_mul_eq_diagonal hM
  rw [isMatIsotropic_rat_iff hM]
  refine and_iff_right fun p => ?_
  obtain ⟨q, hq⟩ := p
  haveI : Fact q.Prime := ⟨hq⟩
  have key : IsMatIsotropic (M.map fun r : ℚ => (r : ℚ_[q])) ↔
      IsDiagIsotropic fun i => ((d i : ℚ) : ℚ_[q]) := by
    simpa [Rat.coe_castHom] using isMatIsotropic_map_iff (Rat.castHom ℚ_[q]) hP hPd
  exact key.mpr (isDiagIsotropic_padic hn _)

/-- **There is no bound on the number of variables of an anisotropic rational form.**  A sum of
squares vanishes only at the origin, so the `u`-invariant of the rational field is infinite, in
contrast with the value four at every finite place. -/
theorem not_isDiagIsotropic_one_rat {n : ℕ} : ¬ IsDiagIsotropic (fun _ : Fin n => (1 : ℚ)) := by
  rintro ⟨x, hx, hsum⟩
  simp only [one_mul] at hsum
  refine hx (funext fun i => ?_)
  have hnn : ∀ i ∈ Finset.univ, (0 : ℚ) ≤ x i ^ 2 := fun i _ => sq_nonneg (x i)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero

/-- **A `p`-adic diagonal form in at least five variables is universal.**  If none of its
coefficients vanishes it represents every `p`-adic number. -/
theorem exists_repr_padic {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 5 ≤ n) {a : Fin n → ℚ_[p]}
    (ha : ∀ i, a i ≠ 0) (c : ℚ_[p]) : ∃ x : Fin n → ℚ_[p], c = ∑ i, a i * x i ^ 2 :=
  exists_repr_of_isDiagIsotropic (by norm_num) ha (isDiagIsotropic_padic hn a) c

/-- **A symmetric `p`-adic form in at least five variables is isotropic**, whether or not it is
presented diagonally. -/
theorem isMatIsotropic_padic {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 5 ≤ n)
    {M : Matrix (Fin n) (Fin n) ℚ_[p]} (hM : M.IsSymm) : IsMatIsotropic M := by
  haveI : Invertible (2 : ℚ_[p]) := invertibleOfNonzero (by norm_num)
  obtain ⟨P, d, hP, hPd⟩ := exists_transpose_mul_mul_eq_diagonal hM
  rw [← isMatIsotropic_transpose_mul_mul_iff (M := M) hP, hPd, isMatIsotropic_diagonal_iff]
  exact isDiagIsotropic_padic hn d

end InverseGalois.CFT
