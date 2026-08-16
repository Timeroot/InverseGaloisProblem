/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootRing
import InverseGalois.Rigidity.RET.Analytic.CoverRational
import InverseGalois.Rigidity.RET.Analytic.Identity

/-!
# A covering carrying a separating function is cut out by an equation

A function of moderate growth on a covering of a punctured plane satisfies a monic equation over
the polynomials of the base coordinate, after multiplication by the leading coefficient of that
equation.  If the function also takes distinct values at the points of each fibre, that equation
does more than hold: the pair consisting of the base coordinate and the function identifies the
covering with the root variety of the equation.

The comparison is a bijection for a counting reason.  The fibre of the covering over a point is an
orbit of the deck group, and the group acts freely because a nontrivial element fixing a point
would leave the function unchanged there; so the fibre carries exactly as many points as the group
has elements, and the function takes that many distinct values on it.  A monic polynomial of that
degree has at most that many roots, so the values of the function *are* all of the roots — the
specialization of the equation is separable, and every root of it is attained.  A continuous
bijection over the plane between two local homeomorphisms onto it is a homeomorphism.

Finitely many points of the base have to be discarded: the leading coefficient of the equation is a
polynomial in the base coordinate, and where it vanishes the multiplied function is identically
zero on a fibre.  Its roots are the only obstruction.

## Main results

* `Rigidity.RET.roots_spec_eq_of_separating` — the values of the coordinate on a fibre are all the
  roots of the specialized equation.
* `Rigidity.RET.separable_spec_of_separating` — the specialized equation is separable.
* `Rigidity.RET.exists_homeo_rootTotal_of_separating` — the covering is homeomorphic over the plane
  to the root variety of the equation.
* `Rigidity.RET.exists_algebraic_model` — a covering with a function of moderate growth separating
  the fibres over the complement of a finite set is, away from finitely many further points of the
  base, the root variety of a monic equation.
-/

open Polynomial Topology

noncomputable section

namespace Rigidity.RET

open Analytic

/-! ### A monic two-variable polynomial with prescribed lower coefficients -/

/-- The monic polynomial in the second variable with prescribed coefficients below the leading
one. -/
def monicPoly (b : ℕ → ℂ[X]) (n : ℕ) : Polynomial (Polynomial ℂ) :=
  X ^ n + ∑ k ∈ Finset.range n, C (b k) * X ^ k

theorem degree_sum_lt_monicPoly (b : ℕ → ℂ[X]) (n : ℕ) :
    (∑ k ∈ Finset.range n, C (b k) * X ^ k).degree < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
  intro k hk
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le k (b k))
    (by exact_mod_cast Finset.mem_range.mp hk)

theorem monicPoly_monic (b : ℕ → ℂ[X]) (n : ℕ) : (monicPoly b n).Monic :=
  monic_X_pow_add (degree_sum_lt_monicPoly b n)

theorem natDegree_monicPoly (b : ℕ → ℂ[X]) (n : ℕ) : (monicPoly b n).natDegree = n := by
  refine natDegree_eq_of_degree_eq_some ?_
  rw [monicPoly, degree_add_eq_left_of_degree_lt, degree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_lt_monicPoly b n

theorem eval_spec_monicPoly (b : ℕ → ℂ[X]) (n : ℕ) (z w : ℂ) :
    (spec (monicPoly b n) z).eval w = w ^ n + ∑ k ∈ Finset.range n, (b k).eval z * w ^ k := by
  simp only [monicPoly, spec, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, eval_add, eval_pow, eval_X,
    eval_finset_sum, eval_mul, eval_C, coe_evalRingHom]

/-! ### The fibres of a covering with a separating coordinate -/

section Model

variable {Y : Type*} {f W : Y → ℂ}
variable {H : Type*} [Group H] [Fintype H] [MulAction H Y] [IsOverBase H f]
variable {P : Polynomial (Polynomial ℂ)} {S' : Finset ℂ}

omit [Fintype H] in
/-- **A coordinate separating a fibre takes distinct values at the points of it.** -/
theorem injective_smul_of_separating
    (hsep : ∀ y : Y, f y ∉ (S' : Set ℂ) → ∀ c : H, c ≠ 1 → W (c • y) ≠ W y)
    {y₀ : Y} (hy₀ : f y₀ ∉ (S' : Set ℂ)) :
    Function.Injective fun a : H => W (a • y₀) := by
  intro a b hab
  by_contra hne
  have hc : a * b⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  have hfb : f (b • y₀) ∉ (S' : Set ℂ) := by rw [IsOverBase.smul_eq (f := f)]; exact hy₀
  refine hsep (b • y₀) hfb (a * b⁻¹) hc ?_
  have hkey : (a * b⁻¹) • (b • y₀) = a • y₀ := by rw [smul_smul, inv_mul_cancel_right]
  rw [hkey]
  exact hab

/-- **The values of a separating coordinate on a fibre are exactly the roots of the specialized
equation**: they are roots, they are as many as the degree, and a polynomial has no more roots than
its degree. -/
theorem roots_spec_eq_of_separating (hP : P.Monic) (hdeg : P.natDegree = Fintype.card H)
    (hroot : ∀ y : Y, (spec P (f y)).eval (W y) = 0)
    (hsep : ∀ y : Y, f y ∉ (S' : Set ℂ) → ∀ c : H, c ≠ 1 → W (c • y) ≠ W y)
    {y₀ : Y} (hy₀ : f y₀ ∉ (S' : Set ℂ)) :
    (spec P (f y₀)).roots = (Finset.univ : Finset H).val.map fun a => W (a • y₀) := by
  classical
  have hne : spec P (f y₀) ≠ 0 := (spec_monic hP _).ne_zero
  have hnodup : ((Finset.univ : Finset H).val.map fun a => W (a • y₀)).Nodup :=
    Finset.univ.nodup.map (injective_smul_of_separating (H := H) hsep hy₀)
  have hsub : ((Finset.univ : Finset H).val.map fun a => W (a • y₀)) ⊆
      (spec P (f y₀)).roots := by
    intro w hw
    rw [Multiset.mem_map] at hw
    obtain ⟨a, -, rfl⟩ := hw
    refine (mem_roots hne).2 ?_
    have hva := hroot (a • y₀)
    rw [IsOverBase.smul_eq (f := f)] at hva
    exact hva
  have hcard : Multiset.card (spec P (f y₀)).roots = Fintype.card H := by
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_spec hP, hdeg]
  exact (Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnodup).2 hsub)
    (by simp [hcard])).symm

/-- **The equation specializes to a separable polynomial over the base of a fibre the coordinate
separates.** -/
theorem separable_spec_of_separating (hP : P.Monic) (hdeg : P.natDegree = Fintype.card H)
    (hroot : ∀ y : Y, (spec P (f y)).eval (W y) = 0)
    (hsep : ∀ y : Y, f y ∉ (S' : Set ℂ) → ∀ c : H, c ≠ 1 → W (c • y) ≠ W y)
    {y₀ : Y} (hy₀ : f y₀ ∉ (S' : Set ℂ)) :
    (spec P (f y₀)).Separable := by
  have hne : spec P (f y₀) ≠ 0 := (spec_monic hP _).ne_zero
  refine (nodup_roots_iff_of_splits hne (IsAlgClosed.splits _)).1 ?_
  rw [roots_spec_eq_of_separating hP hdeg hroot hsep hy₀]
  exact Finset.univ.nodup.map (injective_smul_of_separating (H := H) hsep hy₀)

/-- **Every root of the specialized equation is a value of the coordinate on the fibre.** -/
theorem exists_smul_eq_of_root (hP : P.Monic) (hdeg : P.natDegree = Fintype.card H)
    (hroot : ∀ y : Y, (spec P (f y)).eval (W y) = 0)
    (hsep : ∀ y : Y, f y ∉ (S' : Set ℂ) → ∀ c : H, c ≠ 1 → W (c • y) ≠ W y)
    {y₀ : Y} (hy₀ : f y₀ ∉ (S' : Set ℂ)) {w : ℂ} (hw : (spec P (f y₀)).eval w = 0) :
    ∃ a : H, W (a • y₀) = w := by
  have hne : spec P (f y₀) ≠ 0 := (spec_monic hP _).ne_zero
  have hmem : w ∈ (spec P (f y₀)).roots := (mem_roots hne).2 hw
  rw [roots_spec_eq_of_separating hP hdeg hroot hsep hy₀, Multiset.mem_map] at hmem
  obtain ⟨a, -, ha⟩ := hmem
  exact ⟨a, ha⟩

/-! ### The comparison map to the root variety -/

/-- **The comparison map**: a point of the covering over the good part of the plane goes to its
base coordinate together with the value of the coordinate there, a point of the root variety. -/
def rootModel (P : Polynomial (Polynomial ℂ)) (S' : Finset ℂ)
    (hroot : ∀ y : Y, (spec P (f y)).eval (W y) = 0) :
    ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) → RootTotal P S' :=
  fun y => ⟨⟨(f (y : Y), W (y : Y)), hroot (y : Y)⟩, y.2⟩

@[simp]
theorem rootBase_rootModel (hroot : ∀ y : Y, (spec P (f y)).eval (W y) = 0)
    (y : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ))) : rootBase P S' (rootModel P S' hroot y) = f (y : Y) := rfl

@[simp]
theorem rootCoord_rootModel (hroot : ∀ y : Y, (spec P (f y)).eval (W y) = 0)
    (y : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ))) : rootCoord P S' (rootModel P S' hroot y) = W (y : Y) := rfl

theorem continuous_rootModel [TopologicalSpace Y] (hroot : ∀ y : Y, (spec P (f y)).eval (W y) = 0)
    (hfc : Continuous f) (hWc : Continuous W) : Continuous (rootModel P S' hroot) :=
  (((hfc.comp continuous_subtype_val).prodMk
    (hWc.comp continuous_subtype_val)).subtype_mk _).subtype_mk _

omit [Fintype H] [IsOverBase H f] in
/-- **The comparison map is injective**: two points of a fibre with the same coordinate differ by a
deck transformation the coordinate does not see, so by none. -/
theorem injective_rootModel (hroot : ∀ y : Y, (spec P (f y)).eval (W y) = 0)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ c : H, y' = c • y)
    (hsep : ∀ y : Y, f y ∉ (S' : Set ℂ) → ∀ c : H, c ≠ 1 → W (c • y) ≠ W y) :
    Function.Injective (rootModel (f := f) (W := W) P S' hroot) := by
  intro y y' h
  have h1 : f (y : Y) = f (y' : Y) := congrArg (rootBase P S') h
  have h2 : W (y : Y) = W (y' : Y) := congrArg (rootCoord P S') h
  obtain ⟨c, hc⟩ := htrans _ _ h1
  have hc1 : c = 1 := by
    by_contra hcne
    exact hsep (y : Y) y.2 c hcne (by rw [← hc]; exact h2.symm)
  exact Subtype.ext (by rw [hc, hc1, one_smul])

/-- **The comparison map is surjective**: the coordinate attains every root of the specialized
equation on the fibre. -/
theorem surjective_rootModel (hP : P.Monic) (hdeg : P.natDegree = Fintype.card H)
    (hroot : ∀ y : Y, (spec P (f y)).eval (W y) = 0)
    (hsep : ∀ y : Y, f y ∉ (S' : Set ℂ) → ∀ c : H, c ≠ 1 → W (c • y) ≠ W y)
    (hsurj : ∀ z ∉ (S' : Set ℂ), ∃ y : Y, f y = z) :
    Function.Surjective (rootModel (f := f) (W := W) P S' hroot) := by
  intro t
  obtain ⟨y₀, hy₀⟩ := hsurj (rootBase P S' t) t.2
  have hy₀' : f y₀ ∉ (S' : Set ℂ) := by rw [hy₀]; exact t.2
  have hw : (spec P (f y₀)).eval (rootCoord P S' t) = 0 := by
    rw [hy₀]; exact spec_eval_rootCoord t
  obtain ⟨a, ha⟩ := exists_smul_eq_of_root hP hdeg hroot hsep hy₀' hw
  have hfa : f (a • y₀) = rootBase P S' t := by rw [IsOverBase.smul_eq (f := f), hy₀]
  refine ⟨⟨a • y₀, by rw [Set.mem_preimage, hfa]; exact t.2⟩, ?_⟩
  refine eq_of_rootBase_eq_of_rootCoord_eq ?_ ?_
  · exact hfa
  · exact ha

/-- **A covering with a coordinate separating its fibres is the root variety of its equation.** -/
theorem exists_homeo_rootTotal_of_separating [TopologicalSpace Y] (hf : IsLocalHomeomorph f) (hWc : Continuous W)
    (hP : P.Monic) (hdeg : P.natDegree = Fintype.card H)
    (hroot : ∀ y : Y, (spec P (f y)).eval (W y) = 0)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ c : H, y' = c • y)
    (hsep : ∀ y : Y, f y ∉ (S' : Set ℂ) → ∀ c : H, c ≠ 1 → W (c • y) ≠ W y)
    (hsurj : ∀ z ∉ (S' : Set ℂ), ∃ y : Y, f y = z) :
    ∃ Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S',
      ∀ y, rootBase P S' (Φ y) = f (y : Y) := by
  have hsepz : ∀ z ∉ (S' : Set ℂ), (spec P z).Separable := by
    intro z hz
    obtain ⟨y₀, rfl⟩ := hsurj z hz
    exact separable_spec_of_separating (H := H) hP hdeg hroot hsep hz
  have hopen : IsOpen (f ⁻¹' ((S' : Set ℂ)ᶜ)) :=
    (S'.finite_toSet.isClosed.isOpen_compl).preimage hf.continuous
  have hf' : IsLocalHomeomorph fun y : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) => f (y : Y) :=
    hf.comp hopen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hcont : Continuous (rootModel (f := f) (W := W) P S' hroot) :=
    continuous_rootModel hroot hf.continuous hWc
  have hcomp : IsLocalHomeomorph
      (rootBase P S' ∘ rootModel (f := f) (W := W) P S' hroot) := hf'
  have hloc : IsLocalHomeomorph (rootModel (f := f) (W := W) P S' hroot) :=
    hcomp.of_comp (isLocalHomeomorph_rootBase hP hsepz) hcont
  have hbij : Function.Bijective (rootModel (f := f) (W := W) P S' hroot) :=
    ⟨injective_rootModel (H := H) hroot htrans hsep,
      surjective_rootModel (H := H) hP hdeg hroot hsep hsurj⟩
  exact ⟨hloc.toHomeomorphOfBijective hbij, fun y => rfl⟩

end Model

/-! ### Building the equation from a function of moderate growth -/

section Construct

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {S S₁ : Finset ℂ}
variable {H : Type*} [Group H] [Fintype H] [MulAction H Y] [ContinuousConstSMul H Y]
  [IsOverBase H f]

/-- **A covering of a punctured plane carrying a function of moderate growth that separates the
fibres over the complement of a finite set is the root variety of a monic equation, away from
finitely many further points of the base.**

The function satisfies a monic equation over the polynomials of the base coordinate once it is
multiplied by the leading coefficient of the equation it satisfies; the points to be discarded are
the roots of that leading coefficient, where the multiplied function is identically zero along a
fibre and separates nothing. -/
theorem exists_algebraic_model (hf : IsLocalHomeomorph f)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ c : H, y' = c • y)
    (hrange : Set.range f = ((S : Set ℂ))ᶜ) (hS₁ : S ⊆ S₁) {G : Y → ℂ} (hG : G ∈ coverRing hf S)
    (hsepG : ∀ y : Y, f y ∉ (S₁ : Set ℂ) → ∀ c : H, c ≠ 1 → G (c • y) ≠ G y) :
    ∃ (P : Polynomial (Polynomial ℂ)) (S' : Finset ℂ), S₁ ⊆ S' ∧ P.Monic ∧
      P.natDegree = Fintype.card H ∧ (∀ z ∉ (S' : Set ℂ), (spec P z).Separable) ∧
      ∃ Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S',
        ∀ y, rootBase P S' (Φ y) = f (y : Y) := by
  classical
  obtain ⟨A, R₀, m, hA, hinf⟩ := hG.2.infty
  obtain ⟨b, d, hd, heq⟩ := exists_integral_of_growth (H := H) hf
    (fun a y => IsOverBase.smul_eq (f := f) a y) htrans hG.1 S hrange hG.2.punct hA hinf
  refine ⟨monicPoly b (Fintype.card H), S₁ ∪ d.roots.toFinset, Finset.subset_union_left,
    monicPoly_monic _ _, natDegree_monicPoly _ _, ?_⟩
  set W : Y → ℂ := fun y => d.eval (f y) * G y with hW
  have hroot : ∀ y : Y, (spec (monicPoly b (Fintype.card H)) (f y)).eval (W y) = 0 := by
    intro y
    rw [eval_spec_monicPoly, hW]
    exact heq y
  have hdne : ∀ z ∉ ((S₁ ∪ d.roots.toFinset : Finset ℂ) : Set ℂ), d.eval z ≠ 0 := by
    intro z hz hzero
    refine hz ?_
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Multiset.mem_toFinset]
    exact Or.inr ((mem_roots hd.ne_zero).2 hzero)
  have hmem₁ : ∀ z ∉ ((S₁ ∪ d.roots.toFinset : Finset ℂ) : Set ℂ), z ∉ (S₁ : Set ℂ) := by
    intro z hz hmem
    refine hz ?_
    simp only [Finset.coe_union, Set.mem_union]
    exact Or.inl hmem
  have hsep : ∀ y : Y, f y ∉ ((S₁ ∪ d.roots.toFinset : Finset ℂ) : Set ℂ) →
      ∀ c : H, c ≠ 1 → W (c • y) ≠ W y := by
    intro y hy c hc
    simp only [hW, IsOverBase.smul_eq (f := f)]
    exact fun h => hsepG y (hmem₁ _ hy) c hc (mul_left_cancel₀ (hdne _ hy) h)
  have hsurj : ∀ z ∉ ((S₁ ∪ d.roots.toFinset : Finset ℂ) : Set ℂ), ∃ y : Y, f y = z := by
    intro z hz
    have hzS : z ∈ ((S : Set ℂ))ᶜ := fun hmem => hmem₁ z hz (hS₁ hmem)
    rw [← hrange] at hzS
    exact hzS
  have hWc : Continuous W := by
    rw [hW]
    exact (d.continuous.comp hf.continuous).mul (hG.1.continuous hf)
  have hsepz : ∀ z ∉ ((S₁ ∪ d.roots.toFinset : Finset ℂ) : Set ℂ),
      (spec (monicPoly b (Fintype.card H)) z).Separable := by
    intro z hz
    obtain ⟨y₀, rfl⟩ := hsurj z hz
    exact separable_spec_of_separating (H := H) (W := W) (monicPoly_monic _ _)
      (natDegree_monicPoly _ _) hroot hsep hz
  exact ⟨hsepz, exists_homeo_rootTotal_of_separating (H := H) hf hWc (monicPoly_monic _ _)
    (natDegree_monicPoly _ _) hroot htrans hsep hsurj⟩

end Construct

end Rigidity.RET

end
