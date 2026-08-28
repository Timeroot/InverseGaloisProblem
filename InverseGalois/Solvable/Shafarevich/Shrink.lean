/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The shrinking lemma

Shafarevich's induction never solves an embedding problem on the nose.  Instead it poses the
problem for a free operator group of very large rank `m`, solves it there, and then transports the
solution down to the intended rank `n` along a surjection chosen so as to annihilate whatever
obstruction stood in the way.  The surjections available are the linear combinations
`(x₁, …, x_r) ↦ a₁x₁ + ⋯ + a_rx_r` of `r = m / n` copies of the rank `n` group, and the obstruction
transforms under such a combination as a homogeneous polynomial of a fixed degree `s` in the
coefficient vector `a`.  There are only finitely many obstructions to kill, each contributing
`dim W` polynomial equations, so once `r` exceeds `s` times the total number of equations the
Chevalley–Warning theorem produces a nonzero `a` solving all of them at once.

This file proves that counting argument in the form it is used: a nonzero vector of scalars
annihilating finitely many prescribed degree-`s` forms with vector coefficients, together with the
observation that a nonzero coefficient vector does give a surjection.  The count needs only a bound
on the total degree, so it is also carried out for combinations of monomials of mixed degree, which
is the form the obstruction takes when the layer is described by words rather than by tensors.

## Main results

* `InverseGalois.Shafarevich.exists_ne_zero_forall_eval_eq_zero` — finitely many polynomials over a
  finite field without constant term and with small total degree have a common nonzero root.
* `InverseGalois.Shafarevich.exists_ne_zero_forall_sum_prod_smul_eq_zero` — **the shrinking
  lemma**: for `r` large there is a nonzero `a : Fin r → K` annihilating finitely many prescribed
  degree-`s` forms with coefficients in a finite dimensional space.
* `InverseGalois.Shafarevich.exists_ne_zero_forall_sum_multiset_prod_smul_eq_zero` — the same count
  for a combination of monomials of mixed degree, each named by the multiset of variables it
  involves.
* `InverseGalois.Shafarevich.sumSmul_surjective` — a nonzero coefficient vector combines `r` copies
  of a module onto it.

## Tags

Chevalley-Warning, shrinking lemma, Shafarevich's theorem, embedding problem
-/

namespace InverseGalois.Shafarevich

open MvPolynomial

/-! ### A nonzero common root -/

/-- **Finitely many polynomials over a finite field, all vanishing at the origin and of small total
degree in total, have a common root other than the origin.**  This is the Chevalley–Warning theorem
together with the observation that the number of common roots is a positive multiple of the
characteristic. -/
theorem exists_ne_zero_forall_eval_eq_zero {K σ ι : Type*} [Field K] [Finite K] [Fintype σ]
    [Fintype ι] {f : ι → MvPolynomial σ K} (h0 : ∀ i, eval 0 (f i) = 0)
    (hdeg : (∑ i, (f i).totalDegree) < Fintype.card σ) :
    ∃ a : σ → K, a ≠ 0 ∧ ∀ i, eval a (f i) = 0 := by
  classical
  letI := Fintype.ofFinite K
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hprime : (ringChar K).Prime := CharP.char_is_prime K _
  have hdvd : ringChar K ∣ Nat.card { x : σ → K // ∀ i, eval x (f i) = 0 } := by
    simpa [Nat.card_eq_fintype_card] using
      char_dvd_card_solutions_of_fintype_sum_lt (K := K) (σ := σ) (ringChar K) hdeg
  haveI : Nonempty { x : σ → K // ∀ i, eval x (f i) = 0 } := ⟨⟨0, h0⟩⟩
  have hpos : 0 < Nat.card { x : σ → K // ∀ i, eval x (f i) = 0 } := Nat.card_pos
  haveI : Nontrivial { x : σ → K // ∀ i, eval x (f i) = 0 } := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    have := Nat.le_of_dvd hpos hdvd
    have := hprime.two_le
    omega
  obtain ⟨b, hb⟩ := exists_ne (⟨0, h0⟩ : { x : σ → K // ∀ i, eval x (f i) = 0 })
  exact ⟨b.1, fun h => hb (Subtype.ext h), b.2⟩

/-! ### The shrinking lemma -/

section Shrink

variable {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

/-- **The shrinking lemma.**  Given finitely many families of vectors indexed by the `s`-tuples
drawn from `Fin r`, there is a nonzero vector of scalars `a` for which every one of the associated
degree-`s` forms `∑_I a_{I₁} ⋯ a_{I_s} • w_I` vanishes, provided `r` exceeds `s` times the total
number of scalar equations involved. -/
theorem exists_ne_zero_forall_sum_prod_smul_eq_zero {r s t : ℕ} (hs : s ≠ 0)
    (hr : s * (t * Module.finrank K W) < r) (w : Fin t → (Fin s → Fin r) → W) :
    ∃ a : Fin r → K, a ≠ 0 ∧
      ∀ ν, ∑ I : Fin s → Fin r, (∏ j, a (I j)) • w ν I = 0 := by
  classical
  haveI : NeZero s := ⟨hs⟩
  set d := Module.finrank K W with hd
  set b := Module.finBasis K W with hb
  set f : Fin t × Fin d → MvPolynomial (Fin r) K := fun νl =>
    ∑ I : Fin s → Fin r, C (b.repr (w νl.1 I) νl.2) * ∏ j, X (I j) with hf
  have hfa : ∀ νl, f νl
      = ∑ I : Fin s → Fin r, C (b.repr (w νl.1 I) νl.2) * ∏ j, X (I j) := fun νl => by rw [hf]
  -- every one of these forms vanishes at the origin, since `s` is positive
  have h0 : ∀ νl, eval 0 (f νl) = 0 := by
    intro νl
    rw [hfa, eval_sum]
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [eval_mul, eval_prod,
      Finset.prod_eq_zero (Finset.mem_univ (0 : Fin s)) (by simp : eval 0 (X (I 0)) = (0 : K)),
      mul_zero]
  -- and each has total degree at most `s`
  have hdeg1 : ∀ νl, (f νl).totalDegree ≤ s := by
    intro νl
    rw [hfa]
    refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun I _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_finset_prod _ _).trans ?_
    calc ∑ j : Fin s, (X (I j) : MvPolynomial (Fin r) K).totalDegree
        ≤ ∑ _j : Fin s, 1 := Finset.sum_le_sum fun j _ => le_of_eq (totalDegree_X (I j))
      _ = s := by simp
  have hsum : (∑ νl : Fin t × Fin d, (f νl).totalDegree) < Fintype.card (Fin r) := by
    refine lt_of_le_of_lt (Finset.sum_le_sum fun νl _ => hdeg1 νl) ?_
    have hcard : (∑ _νl : Fin t × Fin d, s) = s * (t * d) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        smul_eq_mul]
      ring
    rw [hcard, Fintype.card_fin]
    exact hr
  obtain ⟨a, ha, hroot⟩ := exists_ne_zero_forall_eval_eq_zero h0 hsum
  refine ⟨a, ha, fun ν => ?_⟩
  refine (map_eq_zero_iff b.repr b.repr.injective).mp (Finsupp.ext fun l => ?_)
  have hν := hroot (ν, l)
  rw [hfa, eval_sum] at hν
  simp only [eval_mul, eval_C, eval_prod, eval_X] at hν
  simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
  rw [← hν]
  exact Finset.sum_congr rfl fun I _ => mul_comm _ _

/-! ### Monomials of mixed degree -/

omit [Finite K] in
/-- Evaluating the product of the variables named by a multiset. -/
private theorem eval_multiset_prod_X {r : ℕ} (a : Fin r → K) (s : Multiset (Fin r)) :
    eval a ((s.map X).prod : MvPolynomial (Fin r) K) = (s.map a).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih => simp [ih]

omit [Finite K] in
/-- The product of the variables named by a multiset has total degree the size of the multiset. -/
private theorem totalDegree_multiset_prod_X_le {r : ℕ} (s : Multiset (Fin r)) :
    ((s.map X).prod : MvPolynomial (Fin r) K).totalDegree ≤ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    omega

/-- **The shrinking lemma for monomials of mixed degree.**  Given finitely many terms, each a
vector of `W` tagged with a monomial in the coordinates of `a`, there is a nonzero vector of
scalars `a` for which every one of the associated sums vanishes, provided no monomial is constant,
every monomial has degree at most `s`, and `r` exceeds `s` times the total number of scalar
equations involved.  Unlike the homogeneous form, the monomials here are allowed to have different
degrees. -/
theorem exists_ne_zero_forall_sum_multiset_prod_smul_eq_zero {α : Type*} [Fintype α] {r s t : ℕ}
    {μ : α → Multiset (Fin r)} (hμ0 : ∀ A, μ A ≠ 0) (hμs : ∀ A, Multiset.card (μ A) ≤ s)
    (hr : s * (t * Module.finrank K W) < r) (w : Fin t → α → W) :
    ∃ a : Fin r → K, a ≠ 0 ∧ ∀ ν, ∑ A, ((μ A).map a).prod • w ν A = 0 := by
  classical
  set d := Module.finrank K W with hd
  set b := Module.finBasis K W with hb
  set f : Fin t × Fin d → MvPolynomial (Fin r) K := fun νl =>
    ∑ A : α, C (b.repr (w νl.1 A) νl.2) * ((μ A).map X).prod with hf
  have hfa : ∀ νl, f νl = ∑ A : α, C (b.repr (w νl.1 A) νl.2) * ((μ A).map X).prod :=
    fun νl => by rw [hf]
  -- no monomial is constant, so every one of these forms vanishes at the origin
  have h0 : ∀ νl, eval 0 (f νl) = 0 := by
    intro νl
    rw [hfa, eval_sum]
    refine Finset.sum_eq_zero fun A _ => ?_
    obtain ⟨i, hi⟩ := Multiset.exists_mem_of_ne_zero (hμ0 A)
    have hz : ((μ A).map (0 : Fin r → K)).prod = 0 :=
      Multiset.prod_eq_zero_iff.mpr (Multiset.mem_map_of_mem _ hi)
    rw [eval_mul, eval_multiset_prod_X, hz, mul_zero]
  -- and each has total degree at most `s`
  have hdeg1 : ∀ νl, (f νl).totalDegree ≤ s := by
    intro νl
    rw [hfa]
    refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun A _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_multiset_prod_X_le (μ A)).trans (hμs A)
  have hsum : (∑ νl : Fin t × Fin d, (f νl).totalDegree) < Fintype.card (Fin r) := by
    refine lt_of_le_of_lt (Finset.sum_le_sum fun νl _ => hdeg1 νl) ?_
    have hcard : (∑ _νl : Fin t × Fin d, s) = s * (t * d) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        smul_eq_mul]
      ring
    rw [hcard, Fintype.card_fin]
    exact hr
  obtain ⟨a, ha, hroot⟩ := exists_ne_zero_forall_eval_eq_zero h0 hsum
  refine ⟨a, ha, fun ν => ?_⟩
  refine (map_eq_zero_iff b.repr b.repr.injective).mp (Finsupp.ext fun l => ?_)
  have hν := hroot (ν, l)
  rw [hfa, eval_sum] at hν
  simp only [eval_mul, eval_C, eval_multiset_prod_X] at hν
  simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
  rw [← hν]
  exact Finset.sum_congr rfl fun A _ => mul_comm _ _

end Shrink

/-! ### Combining copies of a module -/

section SumSmul

variable {F A M : Type*} [DivisionRing F] [Semiring A] [AddCommMonoid M] [Module F M] [Module A M]
  [SMulCommClass F A M]

/-- Combining `r` copies of a module along a vector of scalars commuting with the operators. -/
def sumSmul {r : ℕ} (a : Fin r → F) : (Fin r → M) →ₗ[A] M where
  toFun x := ∑ i, a i • x i
  map_add' x y := by simp [smul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_comm]

@[simp]
theorem sumSmul_apply {r : ℕ} (a : Fin r → F) (x : Fin r → M) :
    sumSmul (A := A) a x = ∑ i, a i • x i := rfl

/-- **A nonzero vector of scalars combines `r` copies of a module onto it.** -/
theorem sumSmul_surjective {r : ℕ} {a : Fin r → F} (ha : a ≠ 0) :
    Function.Surjective (sumSmul (A := A) (M := M) a) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hcon
    exact ha (funext fun i => not_not.mp fun h => hcon ⟨i, h⟩)
  intro m
  refine ⟨Pi.single i ((a i)⁻¹ • m), ?_⟩
  rw [sumSmul_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, smul_smul, mul_inv_cancel₀ hi, one_smul]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

end SumSmul

end InverseGalois.Shafarevich
