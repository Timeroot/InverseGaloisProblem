import Mathlib
import InverseGalois.CFT.Local.PadicSquaresTwo
import InverseGalois.CFT.Global.DiagForm
import InverseGalois.CFT.Global.RealSigns

/-!
# Unit forms in five variables at the dyadic place

At an odd finite place a diagonal form in five variables is always isotropic, because among five
valuations three share a parity and a ternary unit form over an odd `p`-adic field is isotropic.
Neither half of that argument survives at `p = 2`: the ternary form `⟨1, 1, 1⟩` is anisotropic
over `ℚ_[2]`.  What replaces it is a congruence argument one step further into the filtration.

The squares of `ℤ_[2]` are recognised modulo `8`, and modulo `8` a unit is one of `1, 3, 5, 7`
while the square of an element of `{0, 1, 2}` is one of `0, 1, 4`.  Given five units, some
sub-sum of their residues is `0` or `4` modulo `8`: two residues that differ modulo `4` already
add up to `0` or `4`, and if all five agree modulo `4` then any four of them do.  Setting the
corresponding variables to `1`, one spare variable to `2` when the sub-sum is `4`, and the rest
to `0` produces a vector at which the form is divisible by `8`; solving for one remaining
variable leaves a unit congruent to `1` modulo `8`, which is a square.  So the form vanishes at a
point whose first coordinate is nonzero.

Combined with the theorem that at an odd place five variables always suffice and with the sign
criterion at the real place, this settles the Hasse principle for a rational diagonal form in at
least five variables whose coefficients are odd integers: such a form is isotropic exactly when
its coefficients are not all of one sign.

## Main results

* `InverseGalois.CFT.Local.exists_dyadicPattern`: the congruence combinatorics modulo `8`.
* `InverseGalois.CFT.Local.exists_sum_eq_zero_five`: five units of `ℤ_[2]` are the coefficients
  of a diagonal form vanishing at a point with a nonzero coordinate.
* `InverseGalois.CFT.Local.isDiagIsotropic_comp`: a diagonal form is isotropic as soon as the
  subform on an injective family of indices is.
* `InverseGalois.CFT.Local.isDiagIsotropic_two_of_norm_one`: **a diagonal form over `ℚ_[2]` in at
  least five variables whose coefficients have absolute value one is isotropic.**
* `InverseGalois.CFT.isDiagIsotropic_rat_of_odd`: **a diagonal form over `ℚ` in at least five
  variables with odd integer coefficients is isotropic exactly when its coefficients are not all
  of one sign.**
-/

namespace InverseGalois.CFT.Local

/-- The four odd residues modulo `8`, which are the residues of the units of `ℤ_[2]`. -/
def oddResidue : Fin 4 → ZMod 8 := ![1, 3, 5, 7]

/-- The three values `0, 1, 2`, whose squares modulo `8` are `0, 1, 4`. -/
def smallValue : Fin 3 → ℕ := ![0, 1, 2]

/-- Every unit modulo `8` is one of the four odd residues. -/
theorem exists_oddResidue {x : ZMod 8} (hx : IsUnit x) : ∃ k : Fin 4, oddResidue k = x := by
  revert hx
  revert x
  decide

set_option maxRecDepth 4000 in
/-- **The congruence combinatorics at the dyadic place.**  Given five odd residues modulo `8`,
the first of them together with suitable values `0, 1, 2` for the four others makes the diagonal
form vanish modulo `8`. -/
theorem exists_dyadicPattern (k0 k1 k2 k3 k4 : Fin 4) :
    ∃ c1 c2 c3 c4 : Fin 3,
      oddResidue k0 * 1 + oddResidue k1 * ((smallValue c1 : ℕ) : ZMod 8) ^ 2
        + oddResidue k2 * ((smallValue c2 : ℕ) : ZMod 8) ^ 2
        + oddResidue k3 * ((smallValue c3 : ℕ) : ZMod 8) ^ 2
        + oddResidue k4 * ((smallValue c4 : ℕ) : ZMod 8) ^ 2 = 0 := by
  revert k0 k1 k2 k3 k4
  decide

/-- Reduction of a dyadic integer modulo `8`. -/
noncomputable def dyadicReduction : ℤ_[2] →+* ZMod 8 := PadicInt.toZModPow 3

/-- **A diagonal form in five variables with unit coefficients vanishes nontrivially over
`ℤ_[2]`.**  The congruence pattern is lifted by Hensel's lemma: after fixing the last four
variables the remaining unit is congruent to `1` modulo `8`, hence a square. -/
theorem exists_sum_eq_zero_five {a0 a1 a2 a3 a4 : ℤ_[2]} (h0 : IsUnit a0) (h1 : IsUnit a1)
    (h2 : IsUnit a2) (h3 : IsUnit a3) (h4 : IsUnit a4) :
    ∃ x0 x1 x2 x3 x4 : ℤ_[2], x0 ≠ 0 ∧
      a0 * x0 ^ 2 + a1 * x1 ^ 2 + a2 * x2 ^ 2 + a3 * x3 ^ 2 + a4 * x4 ^ 2 = 0 := by
  obtain ⟨k0, hk0⟩ := exists_oddResidue (h0.map dyadicReduction)
  obtain ⟨k1, hk1⟩ := exists_oddResidue (h1.map dyadicReduction)
  obtain ⟨k2, hk2⟩ := exists_oddResidue (h2.map dyadicReduction)
  obtain ⟨k3, hk3⟩ := exists_oddResidue (h3.map dyadicReduction)
  obtain ⟨k4, hk4⟩ := exists_oddResidue (h4.map dyadicReduction)
  obtain ⟨c1, c2, c3, c4, hc⟩ := exists_dyadicPattern k0 k1 k2 k3 k4
  set v : Fin 3 → ℤ_[2] := fun c => ((smallValue c : ℕ) : ℤ_[2]) with hv
  have hred : ∀ c : Fin 3, dyadicReduction (v c) = ((smallValue c : ℕ) : ZMod 8) := by
    intro c
    simp [hv]
  set R : ℤ_[2] := a1 * v c1 ^ 2 + a2 * v c2 ^ 2 + a3 * v c3 ^ 2 + a4 * v c4 ^ 2 with hR
  set w : ℤ_[2] := ((h0.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (-R) with hw
  have h0w : a0 * w = -R := by
    rw [hw, ← mul_assoc, h0.mul_val_inv, one_mul]
  rw [hk0, hk1, hk2, hk3, hk4] at hc
  have hredw : dyadicReduction w = 1 := by
    refine (h0.map dyadicReduction).mul_left_cancel ?_
    rw [← map_mul, h0w, mul_one, map_neg, hR]
    simp only [map_add, map_mul, map_pow, hred]
    linear_combination -hc
  obtain ⟨t, ht⟩ := isSquare_of_toZModPow_three_eq_one hredw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hredw
    exact absurd hredw (by decide)
  refine ⟨t, v c1, v c2, v c3, v c4, ?_, ?_⟩
  · intro h
    rw [h, mul_zero] at ht
    exact hw0 ht
  · have hts : t ^ 2 = w := by rw [ht]; ring
    rw [hts, h0w, hR]
    ring

/-- **Isotropy passes from a subform to the whole form.**  The variables outside the given family
of indices are set to zero. -/
theorem isDiagIsotropic_comp {K : Type*} [Field K] {n m : ℕ} {a : Fin n → K} {f : Fin m → Fin n}
    (hf : Function.Injective f) (h : IsDiagIsotropic (a ∘ f)) : IsDiagIsotropic a := by
  classical
  obtain ⟨y, hy, hsum⟩ := h
  refine ⟨Function.extend f y 0, ?_, ?_⟩
  · intro h0
    refine hy (funext fun j => ?_)
    have := congrFun h0 (f j)
    rwa [hf.extend_apply] at this
  · have hout : ∀ i ∈ Finset.univ, i ∉ Finset.univ.image f →
        a i * Function.extend f y 0 i ^ 2 = 0 := by
      intro i _ hi
      have hni : ¬ ∃ j, f j = i := by
        intro hj
        exact hi (Finset.mem_image.mpr (by obtain ⟨j, hj⟩ := hj; exact ⟨j, Finset.mem_univ j, hj⟩))
      rw [Function.extend_apply' _ _ _ hni]
      simp
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f)) hout,
      Finset.sum_image (fun x _ z _ hxz => hf hxz)]
    rw [← hsum]
    exact Finset.sum_congr rfl fun j _ => by rw [hf.extend_apply]; rfl

/-- **A diagonal form over `ℚ_[2]` in five variables with coefficients of absolute value one is
isotropic.** -/
theorem isDiagIsotropic_two_of_norm_one_five {a : Fin 5 → ℚ_[2]} (ha : ∀ i, ‖a i‖ = 1) :
    IsDiagIsotropic a := by
  set b : Fin 5 → ℤ_[2] := fun i => ⟨a i, le_of_eq (ha i)⟩ with hbdef
  have hb : ∀ i, IsUnit (b i) := fun i => PadicInt.isUnit_iff.mpr (ha i)
  have hba : ∀ i, ((b i : ℤ_[2]) : ℚ_[2]) = a i := fun i => rfl
  obtain ⟨x0, x1, x2, x3, x4, hx0, hsum⟩ :=
    exists_sum_eq_zero_five (hb 0) (hb 1) (hb 2) (hb 3) (hb 4)
  refine ⟨fun i => ((![x0, x1, x2, x3, x4] i : ℤ_[2]) : ℚ_[2]), ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at h0
    refine hx0 (Subtype.coe_injective ?_)
    simpa using h0
  · have hcast : (((b 0 * x0 ^ 2 + b 1 * x1 ^ 2 + b 2 * x2 ^ 2 + b 3 * x3 ^ 2
        + b 4 * x4 ^ 2 : ℤ_[2])) : ℚ_[2]) = 0 := by rw [hsum]; norm_cast
    rw [Fin.sum_univ_five]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
    rw [← hba 0, ← hba 1, ← hba 2, ← hba 3, ← hba 4]
    push_cast at hcast ⊢
    linear_combination hcast

/-- **A diagonal form over `ℚ_[2]` in at least five variables whose coefficients have absolute
value one is isotropic.**  This is the dyadic half of the statement that the `u`-invariant of a
`p`-adic field is four, for forms with unit coefficients. -/
theorem isDiagIsotropic_two_of_norm_one {n : ℕ} (hn : 5 ≤ n) {a : Fin n → ℚ_[2]}
    (ha : ∀ i, ‖a i‖ = 1) : IsDiagIsotropic a := by
  refine isDiagIsotropic_comp (f := fun j : Fin 5 => (⟨j, lt_of_lt_of_le j.isLt hn⟩ : Fin n)) ?_
    (isDiagIsotropic_two_of_norm_one_five fun j => ha _)
  intro i j hij
  have hval := congrArg Fin.val hij
  exact Fin.val_injective hval

/-- An odd integer has dyadic absolute value one. -/
theorem norm_intCast_two_eq_one {k : ℤ} (hk : ¬ (2 : ℤ) ∣ k) : ‖((k : ℤ) : ℚ_[2])‖ = 1 := by
  refine le_antisymm (Padic.norm_int_le_one k) ?_
  by_contra hlt
  push_neg at hlt
  have hcast : ((k : ℤ) : ℚ_[2]) = ((k : ℤ_[2]) : ℚ_[2]) := by push_cast; ring
  rw [hcast, PadicInt.padic_norm_e_of_padicInt] at hlt
  exact hk (by exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd k).mp hlt)

end InverseGalois.CFT.Local

namespace InverseGalois.CFT

open Local

/-- **The Hasse principle for a diagonal form with odd integer coefficients.**  A diagonal form
over the rational field in at least five variables whose coefficients are odd integers is
isotropic exactly when they are not all of one sign: the odd finite places and the dyadic place
impose no condition at all. -/
theorem isDiagIsotropic_rat_of_odd {n : ℕ} (hn : 5 ≤ n) {a : Fin n → ℤ}
    (hodd : ∀ i, ¬ (2 : ℤ) ∣ a i) (hsign : ∃ i j, a i < 0 ∧ 0 < a j) :
    IsDiagIsotropic fun i => ((a i : ℚ)) := by
  refine (isDiagIsotropic_rat_iff_signs hn _).mpr ⟨Or.inr ?_, ?_⟩
  · obtain ⟨i, j, hi, hj⟩ := hsign
    exact ⟨i, j, by exact_mod_cast hi, by exact_mod_cast hj⟩
  · refine isDiagIsotropic_two_of_norm_one hn fun i => ?_
    have : (((a i : ℚ)) : ℚ_[2]) = ((a i : ℤ) : ℚ_[2]) := by push_cast; ring
    rw [this]
    exact norm_intCast_two_eq_one (hodd i)

end InverseGalois.CFT
