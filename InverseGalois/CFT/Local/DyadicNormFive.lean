import Mathlib
import InverseGalois.CFT.Global.DiagForm

/-!
# A quaternary form that only the dyadic place sees

The Hasse–Minkowski theorem decides isotropy of a rational quadratic form by looking at every
completion of `ℚ` at once, and in four variables no single place can be dispensed with.  This
file exhibits a form for which the dyadic place is the only obstruction: the quaternary form
`⟨1, -5, -2, 10⟩` has coefficient signs `+, -, -, +`, so it is visibly isotropic over `ℝ`, yet it
is anisotropic over `ℚ_[2]` and therefore over `ℚ`.

The form is the transfer `N - 2 N` of the norm form `N(u, v) = u ^ 2 - 5 v ^ 2` of the unramified
quadratic extension `ℚ_[2](√5)`, the residue `5` being a unit that is not a square modulo `8`.
Norms from an unramified extension have even valuation, while the factor `2` shifts a valuation by
one, so the two halves of the form can never cancel.

The proof carried out here packages that valuation count into a single congruence modulo `16`.
Scaling a hypothetical zero by a coordinate of largest absolute value produces a zero all of whose
entries are dyadic integers, one of them equal to `1`; reducing modulo `16` leaves four residues,
one of them `1`, for which `c₀ ^ 2 - 5 c₁ ^ 2 - 2 c₂ ^ 2 + 10 c₃ ^ 2` must vanish.  A finite check
shows no such quadruple exists.  Sixteen is the smallest modulus that works: modulo `8` the
residues `2, 2, 1, 1` do satisfy the congruence.

## Main results

* `InverseGalois.CFT.Local.no_dyadic_norm_five_zmod_sixteen`: four residues modulo `16`, one of
  which is `1`, never satisfy `c₀ ^ 2 - 5 c₁ ^ 2 - 2 c₂ ^ 2 + 10 c₃ ^ 2 = 0`.
* `InverseGalois.CFT.Local.not_isDiagIsotropic_norm_five`: **the form `⟨1, -5, -2, 10⟩` is
  anisotropic over `ℚ_[2]`.**
* `InverseGalois.CFT.Local.isDiagIsotropic_real_norm_five`: the same form is isotropic over `ℝ`.
* `InverseGalois.CFT.Local.not_isDiagIsotropic_rat_quaternary`: **the form `⟨1, -5, -2, 10⟩` is
  anisotropic over `ℚ`**, so in four variables the real place alone does not decide isotropy of a
  rational form.
-/

namespace InverseGalois.CFT.Local

set_option maxRecDepth 20000 in
/-- **The congruence obstruction modulo `16`.**  If one of four residues modulo `16` equals `1`,
then `c₀ ^ 2 - 5 c₁ ^ 2 - 2 c₂ ^ 2 + 10 c₃ ^ 2` is nonzero.  Each of the four positions of the
distinguished residue is settled by an exhaustive check over the remaining three. -/
theorem no_dyadic_norm_five_zmod_sixteen (c0 c1 c2 c3 : ZMod 16)
    (h : c0 = 1 ∨ c1 = 1 ∨ c2 = 1 ∨ c3 = 1) :
    c0 ^ 2 - 5 * c1 ^ 2 - 2 * c2 ^ 2 + 10 * c3 ^ 2 ≠ 0 := by
  rcases h with rfl | rfl | rfl | rfl
  · revert c1 c2 c3; decide
  · revert c0 c2 c3; decide
  · revert c0 c1 c3; decide
  · revert c0 c1 c2; decide

/-- **The form `⟨1, -5, -2, 10⟩` is anisotropic over `ℚ_[2]`.**  Dividing a nontrivial zero by a
coordinate of largest absolute value gives a zero with dyadic integer coordinates one of which is
`1`, and reducing modulo `16` contradicts the congruence obstruction. -/
theorem not_isDiagIsotropic_norm_five :
    ¬ IsDiagIsotropic (![1, -5, -2, 10] : Fin 4 → ℚ_[2]) := by
  rintro ⟨x, hx, hsum⟩
  have e0 : (![1, -5, -2, 10] : Fin 4 → ℚ_[2]) 0 = 1 := rfl
  have e1 : (![1, -5, -2, 10] : Fin 4 → ℚ_[2]) 1 = -5 := rfl
  have e2 : (![1, -5, -2, 10] : Fin 4 → ℚ_[2]) 2 = -2 := rfl
  have e3 : (![1, -5, -2, 10] : Fin 4 → ℚ_[2]) 3 = 10 := rfl
  rw [Fin.sum_univ_four, e0, e1, e2, e3] at hsum
  have hsum4 : x 0 ^ 2 - 5 * x 1 ^ 2 - 2 * x 2 ^ 2 + 10 * x 3 ^ 2 = 0 := by
    linear_combination hsum
  obtain ⟨j, hj⟩ := Finite.exists_max (fun i => ‖x i‖)
  have hxj : x j ≠ 0 := by
    intro h0
    apply hx
    funext i
    have := hj i
    rw [h0] at this
    simpa using this
  set y : Fin 4 → ℚ_[2] := fun i => x i / x j with hy
  have hyle : ∀ i, ‖y i‖ ≤ 1 := by
    intro i
    rw [hy]
    simp only [norm_div]
    exact div_le_one_of_le₀ (hj i) (norm_nonneg _)
  have hyj : y j = 1 := by
    rw [hy]
    exact div_self hxj
  have hx2 : x j ^ 2 ≠ 0 := pow_ne_zero 2 hxj
  have hysum : y 0 ^ 2 - 5 * y 1 ^ 2 - 2 * y 2 ^ 2 + 10 * y 3 ^ 2 = 0 := by
    have hexp : ∀ i, y i ^ 2 = x i ^ 2 / x j ^ 2 := fun i => by simp only [hy, div_pow]
    rw [hexp 0, hexp 1, hexp 2, hexp 3]
    field_simp
    linear_combination hsum4
  set z : Fin 4 → ℤ_[2] := fun i => ⟨y i, hyle i⟩ with hz
  have hzj : z j = 1 := by
    rw [hz]
    exact Subtype.ext (by simpa using hyj)
  have hzsum : z 0 ^ 2 - 5 * z 1 ^ 2 - 2 * z 2 ^ 2 + 10 * z 3 ^ 2 = 0 := by
    rw [← PadicInt.coe_eq_zero]
    push_cast
    exact hysum
  set c : Fin 4 → ZMod 16 := fun i => PadicInt.toZModPow 4 (z i) with hc
  have hcj : c j = 1 := by rw [hc]; simp [hzj]
  have hcsum : c 0 ^ 2 - 5 * c 1 ^ 2 - 2 * c 2 ^ 2 + 10 * c 3 ^ 2 = 0 := by
    have hmap := congrArg (PadicInt.toZModPow (p := 2) 4) hzsum
    simpa [hc, map_ofNat] using hmap
  refine no_dyadic_norm_five_zmod_sixteen (c 0) (c 1) (c 2) (c 3) ?_ hcsum
  fin_cases j
  · exact Or.inl hcj
  · exact Or.inr (Or.inl hcj)
  · exact Or.inr (Or.inr (Or.inl hcj))
  · exact Or.inr (Or.inr (Or.inr hcj))

/-- **The form `⟨1, -5, -2, 10⟩` is anisotropic over `ℚ`.**  Its coefficients have the signs
`+, -, -, +`, so the form does represent zero nontrivially over `ℝ`: in four variables the real
place alone cannot decide isotropy, and here the dyadic place is what rules it out. -/
theorem not_isDiagIsotropic_rat_quaternary :
    ¬ IsDiagIsotropic (![1, -5, -2, 10] : Fin 4 → ℚ) := by
  intro h
  refine not_isDiagIsotropic_norm_five ?_
  have hmap := h.map (Rat.castHom ℚ_[2])
  have he : (fun i => (Rat.castHom ℚ_[2]) ((![1, -5, -2, 10] : Fin 4 → ℚ) i))
      = (![1, -5, -2, 10] : Fin 4 → ℚ_[2]) := by
    funext i
    fin_cases i <;> simp
  rwa [he] at hmap

/-- **The same form is isotropic over `ℝ`.**  A square root of five and a one annihilate its
first two coefficients. -/
theorem isDiagIsotropic_real_norm_five :
    IsDiagIsotropic (![1, -5, -2, 10] : Fin 4 → ℝ) := by
  refine ⟨![Real.sqrt 5, 1, 0, 0], ?_, ?_⟩
  · intro h
    have h1 := congrFun h 1
    simp at h1
  · rw [Fin.sum_univ_four]
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_three, h5]
    norm_num

end InverseGalois.CFT.Local
