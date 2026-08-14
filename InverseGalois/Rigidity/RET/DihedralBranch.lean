/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.LineSubst
import InverseGalois.Rigidity.RET.DihedralCover
import InverseGalois.Rigidity.RET.SeparableUnramified
import InverseGalois.Rigidity.RET.MoveInfinity

/-!
# The branch points of a dihedral cover

The dihedral group of order `2n` acts on the line `ℚ̄(u)` by `u ↦ ζ^i u` and `u ↦ ζ^i u^{-1}`, and
the invariant of the action is `w = u^n + u^{-n}`.  Reading `w` as the coordinate of a second copy
of the line presents `ℚ̄(u)` as a degree-`2n` cover of the line, and this file computes where that
cover is branched: the parameter satisfies `Y^{2n} - w·Y^n + 1 = 0`, an equation that stays
separable at every `w = t` with `t ≠ ±2`, so the affine branch points are exactly the two points
`t = 2` and `t = -2`.

Two branch points is sharp for `n ≥ 3`: a cover of the line with a single affine branch point has a
cyclic deck group (`Rigidity.RET.isAffineDeckGroup_one_iff`), and the dihedral group of order `2n`
is not cyclic once `n ≥ 3`.  This is the first non-abelian group whose branch-point count over the
line is pinned exactly.

## Main definitions

* `Rigidity.RET.dihSubst` — the substitution `T ↦ u^n + u^{-n}`.
* `Rigidity.RET.DihCover` — the dihedral cover of the line, and `Rigidity.RET.dihLineCover` its
  packaging as a cover.
* `Rigidity.RET.dihCoverAutHom` — the dihedral group, acting on the cover over the base.

## Main results

* `Rigidity.RET.separable_dihedralPoly` — the dihedral equation specializes separably away from
  `t = ±2`.
* `Rigidity.RET.finrank_dihCover` — the cover has degree `2n`, and
  `Rigidity.RET.dihDeckEquiv` identifies its deck group with the dihedral group.
* `Rigidity.RET.isAffineDeckGroup_dihedralGroup` — the dihedral group of order `2n` is the deck
  group of a cover of the line with at most two affine branch points.
* `Rigidity.RET.not_isAffineDeckGroup_one_dihedralGroup` — for `n ≥ 3`, one branch point is not
  enough, so the count is exact.
-/

open Polynomial GeomAKLB

noncomputable section

namespace Rigidity.RET

/-! ## The dihedral equation as a polynomial identity -/

/-- Specializing the coefficients of the dihedral equation specializes its invariant. -/
theorem dihedralPoly_map {A B : Type*} [CommRing A] [CommRing B] (g : A →+* B) (u : A) (n : ℕ) :
    (dihedralPoly u n).map g = dihedralPoly (g u) n := by
  simp [dihedralPoly, Polynomial.map_add, Polynomial.map_neg, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_one]

/-- **The dihedral equation is the product of two Kummer equations.**  A factorization `t = a + b`
with `a·b = 1` of the invariant splits `Y^{2n} - t·Y^n + 1` into `(Y^n - a)(Y^n - b)`. -/
theorem dihedralPoly_eq_mul {A : Type*} [CommRing A] {t a b : A} (hsum : a + b = t)
    (hprod : a * b = 1) (n : ℕ) :
    dihedralPoly t n = (X ^ n - C a) * (X ^ n - C b) := by
  have hC : (C a : A[X]) * C b = 1 := by rw [← map_mul, hprod, map_one]
  subst hsum
  simp only [dihedralPoly, two_mul, pow_add, map_add]
  linear_combination -hC

/-- Two Kummer equations with distinct constants are coprime: their difference is a unit. -/
theorem isCoprime_X_pow_sub_C {F : Type*} [Field F] {a b : F} (hab : a ≠ b) (n : ℕ) :
    IsCoprime (X ^ n - C a : F[X]) (X ^ n - C b) := by
  have h : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hu : (C (a - b)⁻¹ : F[X]) * (C a - C b) = 1 := by
    rw [← map_sub, ← map_mul, inv_mul_cancel₀ h, map_one]
  exact ⟨-C (a - b)⁻¹, C (a - b)⁻¹, by linear_combination hu⟩

/-- **The dihedral equation stays separable away from the two points `t = ±2`.**

Over an algebraically closed field the invariant `t` factors as `a + b` with `a·b = 1`, and the two
factors are distinct exactly when `t² ≠ 4`; the equation then splits into two coprime Kummer
equations, each separable in characteristic zero. -/
theorem separable_dihedralPoly {n : ℕ} (hn : 0 < n) {t : k} (ht : t ≠ 2) (ht' : t ≠ -2) :
    (dihedralPoly t n).Separable := by
  have hne4 : t ^ 2 - 4 ≠ 0 := by
    intro h
    have hfac : (t - 2) * (t + 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact ht (sub_eq_zero.mp h1)
    · exact ht' (eq_neg_of_add_eq_zero_left h1)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (t ^ 2 - 4) (n := 2) two_pos
  have hs0 : s ≠ 0 := by
    intro h
    apply hne4
    rw [← hs, h]
    ring
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  have hsum : (t + s) / 2 + (t - s) / 2 = t := by field_simp; ring
  have hprod : ((t + s) / 2) * ((t - s) / 2) = 1 := by
    field_simp
    linear_combination -hs
  have hane : ((t + s) / 2 : k) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact zero_ne_one hprod
  have hbne : ((t - s) / 2 : k) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact zero_ne_one hprod
  have hab : ((t + s) / 2 : k) ≠ (t - s) / 2 := by
    intro h
    field_simp at h
    have h' : (2 : k) * s = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h2' | h2'
    · exact h2 h2'
    · exact hs0 h2'
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [dihedralPoly_eq_mul hsum hprod]
  exact (Polynomial.separable_X_pow_sub_C _ hncast hane).mul
    (Polynomial.separable_X_pow_sub_C _ hncast hbne) (isCoprime_X_pow_sub_C hab n)

/-! ## The dihedral cover -/

/-- The order of the dihedral group is positive. -/
theorem dihPos (n : ℕ) [NeZero n] : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)

/-- **The dihedral substitution** `T ↦ u^n + u^{-n}` of the line into itself. -/
def dihSubst (n : ℕ) [NeZero n] : RatFunc k →ₐ[k] RatFunc k :=
  ratFuncSubst (dihedralInvariant k n) (transcendental_dihedralInvariant n (dihPos n))

@[simp] theorem dihSubst_X (n : ℕ) [NeZero n] :
    dihSubst n (RatFunc.X : RatFunc k) = dihedralInvariant k n :=
  ratFuncSubst_X _ _

/-- **The dihedral cover of the line**: the line `ℚ̄(u)`, seen as an extension of the line through
the invariant `u^n + u^{-n}` of the dihedral action. -/
abbrev DihCover (n : ℕ) [NeZero n] : Type := LineSubst (dihSubst n)

/-- **The parameter `u` of the dihedral cover.** -/
abbrev dihParam (n : ℕ) [NeZero n] : DihCover n := LineSubst.param (dihSubst n)

/-- **The parameter of the dihedral cover satisfies the degree-`2n` dihedral equation.** -/
theorem aeval_param_dihedralPoly (n : ℕ) [NeZero n] :
    Polynomial.aeval (dihParam n) (dihedralPoly (RatFunc.X : RatFunc k) n) = 0 := by
  have hXn : (RatFunc.X : RatFunc k) ^ n ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  apply LineSubst.toLine_injective
  simp only [dihedralPoly, map_add, map_neg, map_mul, map_pow, map_one, Polynomial.aeval_X,
    Polynomial.aeval_C, LineSubst.toLine_add, LineSubst.toLine_neg, LineSubst.toLine_mul,
    LineSubst.toLine_pow, LineSubst.toLine_one, LineSubst.toLine_zero, LineSubst.toLine_param,
    LineSubst.toLine_algebraMap, dihSubst_X, dihedralInvariant, two_mul, pow_add]
  field_simp
  ring

/-! ## The dihedral action on the cover -/

section Aut

variable {n : ℕ} {ζ : k} [NeZero n] (hζ : IsPrimitiveRoot ζ n)

/-- A dihedral automorphism of the line fixes the invariant, hence every function of it. -/
theorem dihedralAut_dihSubst (g : DihedralGroup n) (x : RatFunc k) :
    (dihedralAut hζ g) (dihSubst n x) = dihSubst n x := by
  have hcomp : (dihedralAut hζ g).toAlgHom.comp (dihSubst n) = dihSubst n := by
    refine ratFunc_algHom_ext ?_
    rw [AlgHom.comp_apply, dihSubst_X]
    exact dihedralAut_dihedralInvariant hζ g
  exact congrArg (fun ψ : RatFunc k →ₐ[k] RatFunc k => ψ x) hcomp

/-- A dihedral automorphism of the line, read as an automorphism of the dihedral cover over the
base of the cover. -/
def dihCoverAut (g : DihedralGroup n) : DihCover n ≃ₐ[RatFunc k] DihCover n :=
  AlgEquiv.ofRingEquiv (R := RatFunc k) (f := (dihedralAut hζ g).toRingEquiv)
    (dihedralAut_dihSubst hζ g)

@[simp] theorem dihCoverAut_apply (g : DihedralGroup n) (x : DihCover n) :
    LineSubst.toLine _ (dihCoverAut hζ g x) = dihedralAut hζ g (LineSubst.toLine _ x) := rfl

/-- **The dihedral group acts on the dihedral cover over the base.** -/
def dihCoverAutHom : DihedralGroup n →* (DihCover n ≃ₐ[RatFunc k] DihCover n) where
  toFun := dihCoverAut hζ
  map_one' := by
    refine AlgEquiv.ext fun x => ?_
    show (dihedralAut hζ 1) (LineSubst.toLine _ x) = LineSubst.toLine _ x
    rw [map_one]
    rfl
  map_mul' a b := by
    refine AlgEquiv.ext fun x => ?_
    rw [AlgEquiv.mul_apply]
    show (dihedralAut hζ (a * b)) (LineSubst.toLine _ x)
      = dihedralAut hζ a (dihedralAut hζ b (LineSubst.toLine _ x))
    rw [map_mul, AlgEquiv.mul_apply]

@[simp] theorem dihCoverAutHom_apply (g : DihedralGroup n) (x : DihCover n) :
    LineSubst.toLine _ (dihCoverAutHom hζ g x) = dihedralAut hζ g (LineSubst.toLine _ x) := rfl

/-- The action is faithful: distinct dihedral elements move the parameter differently. -/
theorem dihCoverAutHom_injective : Function.Injective (dihCoverAutHom hζ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine dihedralAut_injective hζ (AlgEquiv.ext fun x => ?_)
  simpa using AlgEquiv.ext_iff.mp hg x

end Aut

/-! ## Degree and Galois property -/

section Degree

variable (n : ℕ) [NeZero n]

/-- The dihedral equation is monic. -/
theorem dihedralPoly_X_monic : (dihedralPoly (RatFunc.X : RatFunc k) n).Monic :=
  dihedralPoly_monic _ (dihPos n)

/-- **The dihedral cover is a finite extension of the line.** -/
instance dihCover_finiteDimensional : FiniteDimensional (RatFunc k) (DihCover n) :=
  LineSubst.finiteDimensional _ ⟨_, dihedralPoly_X_monic n, aeval_param_dihedralPoly n⟩

/-- **The dihedral cover has degree `2n` over the line**, and its automorphism group over the line
is the dihedral group of order `2n`.  The degree is at most `2n` because the parameter satisfies
the dihedral equation, and at least `2n` because the `2n` dihedral substitutions are already that
many automorphisms over the base. -/
theorem finrank_dihCover : Module.finrank (RatFunc k) (DihCover n) = 2 * n := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_algebraicClosure n (dihPos n)
  have hfr : Module.finrank (RatFunc k) (DihCover n) ≤ 2 * n :=
    le_trans (LineSubst.finrank_le_of_monic _ (dihedralPoly_X_monic n)
      (aeval_param_dihedralPoly n)) (dihedralPoly_natDegree_le _ n)
  have hge : 2 * n ≤ Fintype.card (DihCover n ≃ₐ[RatFunc k] DihCover n) := by
    have hcard := Fintype.card_le_of_injective _ (dihCoverAutHom_injective hζ)
    rwa [DihedralGroup.card] at hcard
  exact le_antisymm hfr (hge.trans AlgEquiv.card_le)

/-- The automorphism group of the dihedral cover over the line has order `2n`. -/
theorem card_aut_dihCover : Fintype.card (DihCover n ≃ₐ[RatFunc k] DihCover n) = 2 * n := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_algebraicClosure n (dihPos n)
  refine le_antisymm (AlgEquiv.card_le.trans (le_of_eq (finrank_dihCover n))) ?_
  have hcard := Fintype.card_le_of_injective _ (dihCoverAutHom_injective hζ)
  rwa [DihedralGroup.card] at hcard

/-- **The dihedral cover is a Galois extension of the line**: it has as many automorphisms over the
base as its degree. -/
instance dihCover_isGalois : IsGalois (RatFunc k) (DihCover n) :=
  IsGalois.of_card_aut_eq_finrank (RatFunc k) (DihCover n)
    (by rw [Nat.card_eq_fintype_card, card_aut_dihCover, finrank_dihCover])

/-- **The dihedral cover, packaged as a cover of the line.** -/
abbrev dihLineCover : LineCover := LineCover.of (DihCover n)

@[simp] theorem dihLineCover_M : (dihLineCover n).M = DihCover n := rfl

variable {n} {ζ : k}

/-- **The dihedral group exhausts the automorphisms of the dihedral cover.** -/
theorem dihCoverAutHom_bijective (hζ : IsPrimitiveRoot ζ n) :
    Function.Bijective (dihCoverAutHom hζ) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨dihCoverAutHom_injective hζ, by rw [DihedralGroup.card, card_aut_dihCover]⟩

/-- **The deck group of the dihedral cover is the dihedral group of order `2n`.** -/
def dihDeckEquiv (hζ : IsPrimitiveRoot ζ n) : DihedralGroup n ≃* (dihLineCover n).deck :=
  MulEquiv.ofBijective (dihCoverAutHom hζ) (dihCoverAutHom_bijective hζ)

@[simp] theorem dihDeckEquiv_apply (hζ : IsPrimitiveRoot ζ n) (g : DihedralGroup n)
    (x : DihCover n) :
    LineSubst.toLine (dihSubst n) (dihDeckEquiv hζ g x)
      = dihedralAut hζ g (LineSubst.toLine (dihSubst n) x) := rfl

end Degree

/-! ## The branch points -/

/-- The parameter of the dihedral cover satisfies the dihedral equation over the coordinate ring of
the base. -/
theorem aeval_param_dihedralPolyX (n : ℕ) [NeZero n] :
    (Polynomial.aeval (dihParam n)) (dihedralPoly (Polynomial.X : Polynomial k) n) = 0 := by
  rw [← Polynomial.aeval_map_algebraMap (RatFunc k), dihedralPoly_map, RatFunc.algebraMap_X]
  exact aeval_param_dihedralPoly n

/-- **The dihedral group of order `2n` is the deck group of a cover of the line with at most two
affine branch points.**

The cover is the line itself, mapping to the line by the invariant `u^n + u^{-n}` of the dihedral
action; the degree is `2n` because the parameter satisfies the dihedral equation and the `2n`
dihedral automorphisms are already that many automorphisms over the base; and the equation
specializes separably away from `t = ±2`. -/
theorem isUnramifiedOutside_dihLineCover (n : ℕ) [NeZero n] :
    (dihLineCover n).IsUnramifiedOutside ({2, -2} : Set k) := by
  have hgen : IntermediateField.adjoin (RatFunc k) {dihParam n} = ⊤ :=
    LineSubst.adjoin_param_eq_top _
  have hmonicP : (dihedralPoly (Polynomial.X : Polynomial k) n).Monic :=
    dihedralPoly_monic _ (dihPos n)
  have hrootP := aeval_param_dihedralPolyX n
  have hsep : ∀ t ∉ ({2, -2} : Set k),
      ((dihedralPoly (Polynomial.X : Polynomial k) n).map (evalRingHom t)).Separable := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    rw [dihedralPoly_map]
    simpa using separable_dihedralPoly (dihPos n) ht.1 ht.2
  exact LineCover.isUnramifiedOutside_of_separable (dihLineCover n) hgen hmonicP hrootP hsep

/-- The branch locus of the dihedral cover is contained in the two points `t = ±2`. -/
theorem branchLocus_dihLineCover_subset (n : ℕ) [NeZero n] :
    (dihLineCover n).branchLocus ⊆ ({2, -2} : Set k) :=
  ((dihLineCover n).isUnramifiedOutside_iff_branchLocus_subset _).mp
    (isUnramifiedOutside_dihLineCover n)

theorem isAffineDeckGroup_dihedralGroup (n : ℕ) [NeZero n] :
    IsAffineDeckGroup 2 (DihedralGroup n) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_algebraicClosure n (dihPos n)
  refine ⟨dihLineCover n, ⟨(dihDeckEquiv hζ).symm⟩, ?_⟩
  refine le_trans (Set.ncard_le_ncard (branchLocus_dihLineCover_subset n) (Set.toFinite _)) ?_
  exact le_trans (Set.ncard_insert_le _ _) (by simp)

/-- **Two affine branch points are needed**: past the degenerate case `n = 1` the dihedral group of
order `2n` is not cyclic, and a cover of the line with a single affine branch point has a cyclic
deck group.  So `Rigidity.RET.isAffineDeckGroup_dihedralGroup` counts exactly. -/
theorem not_isAffineDeckGroup_one_dihedralGroup {n : ℕ} [NeZero n] (hn : n ≠ 1) :
    ¬ IsAffineDeckGroup 1 (DihedralGroup n) := fun h =>
  DihedralGroup.not_isCyclic hn (isAffineDeckGroup_one_iff.mp h)

end Rigidity.RET
