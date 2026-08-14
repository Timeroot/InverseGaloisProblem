/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.EquationCover
import InverseGalois.Hilbert.Analytic.SerreBaseCover

/-!
# The branch locus of a linear cover, and the equation `Xⁿ⁻¹(X - c) = T`

A **linear cover** is the cover of the line presented by an equation `g₀(X) = T` in which the
parameter enters linearly: the splitting cover of `linearCoverC g₀ = g₀(X) - T` over `ℚ̄(T)`.  Its
fibre over a point `t` of the line is the fibre `g₀⁻¹(t)`, so it is unramified at every `t` whose
fibre consists of `deg g₀` distinct points — the branch locus of the cover consists of critical
values of `g₀`, and nothing else.

Applied to the polynomial

`Xⁿ⁻¹(X - c)`,

whose derivative is `Xⁿ⁻²(nX - (n-1)c)`, this gives a cover of the line of degree `n` with **two**
branch points on the affine line, whatever `n` is: the only critical points are `0` and
`(n-1)c/n`, so the only critical values are `0` and `Xⁿ⁻¹(X-c)` evaluated there.  For
`c = n/(n-1)` this polynomial is `serreBaseP n`, the base cover shared by the two Serre
alternating families, whose geometric monodromy group is the full symmetric group.

## Main results

* `Rigidity.RET.linearCover` — the splitting cover of `g₀(X) = T` over `ℚ̄(T)`, and
  `Rigidity.RET.linearCover_isUnramifiedOutside` — it is unramified outside any set of parameters
  containing every `t` with `g₀ - t` inseparable.
* `Rigidity.RET.cuspPoly` — the polynomial `Xⁿ⁻¹(X - c)`, with
  `Rigidity.RET.separable_cuspPoly_sub`: every fibre outside the two critical values is separable.
* `Rigidity.RET.cuspCover_branchLocus_ncard_le` — the cover it presents has at most two branch
  points on the affine line, and `Rigidity.RET.isAffineDeckGroup_cuspCover` records this for the
  deck group.
* `Rigidity.RET.serreBaseCover` — the same for Serre's base cover `serreBaseP n`.
-/

open Polynomial SerreBaseCover

noncomputable section

namespace Rigidity.RET

open GeomAKLB

variable {n : ℕ} {c : k}

/-! ### A coprimality criterion over an algebraically closed field -/

/-- **Two polynomials over an algebraically closed field with no common root are coprime.**  A
non-unit greatest common divisor has positive degree, hence a root, and that root is a root of
both. -/
theorem isCoprime_of_no_common_root {K : Type*} [Field K] [IsAlgClosed K] {p q : Polynomial K}
    (h : ∀ x : K, p.IsRoot x → ¬ q.IsRoot x) : IsCoprime p q := by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff]
  by_contra hu
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (EuclideanDomain.gcd p q)
    fun hd => hu (Polynomial.isUnit_iff_degree_eq_zero.mpr hd)
  exact h x (hx.dvd (EuclideanDomain.gcd_dvd_left p q))
    (hx.dvd (EuclideanDomain.gcd_dvd_right p q))

/-! ### The cover presented by an equation with a linear parameter -/

/-- **Specializing the parameter of a linear cover to `t` gives the fibre polynomial
`g₀ - t`.** -/
theorem linearCoverC_map_evalRingHom (g₀ : Polynomial k) (t : k) :
    (linearCoverC g₀).map (evalRingHom t) = g₀ - C t := by
  have hC : (evalRingHom t).comp (C : k →+* Polynomial k) = RingHom.id k :=
    RingHom.ext fun a => by simp
  rw [linearCoverC, Polynomial.map_sub, Polynomial.map_map, hC, Polynomial.map_id, map_C]
  simp

/-- **The generic fibre of a linear cover is separable**: the equation is irreducible over `ℚ̄(T)`,
the parameter entering linearly, and the base field has characteristic zero. -/
theorem genericPoly_linearCoverC_separable (g₀ : Polynomial k) (hg : g₀.Monic)
    (hd : 1 ≤ g₀.natDegree) : (genericPoly (linearCoverC g₀)).Separable :=
  ((Monic.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc k) (linearCoverC_monic g₀ hg hd)).mp (linearCoverC_irreducible g₀)).separable

/-- **The degeneracy locus of a linear cover is contained in any set of parameters outside of
which the fibre polynomial is separable.** -/
theorem degeneracy_linearCoverC_subset (g₀ : Polynomial k) (hg : g₀.Monic) (hd : 1 ≤ g₀.natDegree)
    {S : Set k} (hS : ∀ t : k, t ∉ S → (g₀ - C t).Separable) :
    {t : k | (degeneracy (linearCoverC g₀)).eval t = 0} ⊆ S := by
  intro t ht
  by_contra hmem
  refine (separable_specialize_iff (linearCoverC g₀) (linearCoverC_monic g₀ hg hd)
    (by rw [linearCoverC_natDegree g₀ hd]; omega) t).mp ?_ ht
  rw [linearCoverC_map_evalRingHom]
  exact hS t hmem

/-- The **linear cover** attached to a monic polynomial `g₀` of positive degree: the splitting
cover of the equation `g₀(X) = T` over `ℚ̄(T)`. -/
@[reducible] def linearCover (g₀ : Polynomial k) (hg : g₀.Monic) (hd : 1 ≤ g₀.natDegree) :
    LineCover :=
  eqCover (linearCoverC g₀) (genericPoly_linearCoverC_separable g₀ hg hd)

/-- **A linear cover is unramified wherever its fibre polynomial stays separable.** -/
theorem linearCover_isUnramifiedOutside (g₀ : Polynomial k) (hg : g₀.Monic)
    (hd : 1 ≤ g₀.natDegree) {S : Set k} (hS : ∀ t : k, t ∉ S → (g₀ - C t).Separable) :
    (linearCover g₀ hg hd).IsUnramifiedOutside S := by
  haveI := eqCover_isSplittingField (linearCoverC g₀) (genericPoly_linearCoverC_separable g₀ hg hd)
  exact ((linearCover g₀ hg hd).isUnramifiedOutside_degeneracy_of_isSplittingField
    (linearCoverC g₀) (linearCoverC_monic g₀ hg hd)
    (by rw [linearCoverC_natDegree g₀ hd]; omega)).mono
      (degeneracy_linearCoverC_subset g₀ hg hd hS)

/-! ### The polynomial `Xⁿ⁻¹(X - c)` -/

/-- The polynomial `Xⁿ⁻¹(X - c)`: a map of the line to itself of degree `n` with a single point of
multiplicity `n - 1` in one fibre and a single double point in one other fibre. -/
def cuspPoly (n : ℕ) (c : k) : Polynomial k := X ^ (n - 1) * (X - C c)

/-- The nonzero critical point `(n-1)c/n` of `cuspPoly n c`. -/
def cuspCritPt (n : ℕ) (c : k) : k := ((n : k) - 1) * c / (n : k)

/-- The critical value of `cuspPoly n c` at its nonzero critical point. -/
def cuspCritVal (n : ℕ) (c : k) : k := (cuspPoly n c).eval (cuspCritPt n c)

theorem cuspPoly_monic (n : ℕ) (c : k) : (cuspPoly n c).Monic :=
  (monic_X_pow _).mul (monic_X_sub_C _)

theorem cuspPoly_natDegree (hn : 1 ≤ n) (c : k) : (cuspPoly n c).natDegree = n := by
  rw [cuspPoly, (monic_X_pow (R := k) (n - 1)).natDegree_mul (monic_X_sub_C _), natDegree_X_pow,
    natDegree_X_sub_C]
  omega

/-- **The derivative of `Xⁿ⁻¹(X - c)` is `Xⁿ⁻²(nX - (n-1)c)`**: the shape that makes the critical
points visible. -/
theorem derivative_cuspPoly (hn : 2 ≤ n) (c : k) :
    derivative (cuspPoly n c) = X ^ (n - 2) * (C (n : k) * X - C (((n : k) - 1) * c)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [cuspPoly, Nat.add_sub_cancel, derivative_mul, derivative_X_pow, derivative_sub,
    derivative_X, derivative_C, show m + 2 - 1 = m + 1 from rfl]
  simp only [C_mul, C_sub, C_1, C_eq_natCast]
  push_cast
  ring

/-- **The critical points of `Xⁿ⁻¹(X - c)` are `0` and `(n-1)c/n`.** -/
theorem eq_of_isRoot_derivative_cuspPoly (hn : 2 ≤ n) {c x : k}
    (hx : (derivative (cuspPoly n c)).IsRoot x) : x = 0 ∨ x = cuspCritPt n c := by
  have hn0 : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [derivative_cuspPoly hn] at hx
  simp only [IsRoot, eval_mul, eval_pow, eval_X, eval_sub, eval_C, mul_eq_zero] at hx
  rcases hx with h | h
  · exact Or.inl (pow_eq_zero_iff'.mp h).1
  · refine Or.inr ?_
    rw [cuspCritPt, eq_div_iff hn0]
    linear_combination h

/-- The value of `Xⁿ⁻¹(X - c)` at the critical point `0`. -/
theorem eval_cuspPoly_zero (hn : 2 ≤ n) (c : k) : (cuspPoly n c).eval (0 : k) = 0 := by
  simp [cuspPoly, zero_pow (show n - 1 ≠ 0 by omega)]

/-- **Every fibre of `Xⁿ⁻¹(X - c)` outside the two critical values is separable.**  A repeated root
of `Pₙ - t` is a common root of `Pₙ - t` and of the derivative of `Pₙ`, so it is a critical point,
and then `t` is the value of `Pₙ` there. -/
theorem separable_cuspPoly_sub (hn : 2 ≤ n) {c t : k} (ht0 : t ≠ 0)
    (htc : t ≠ cuspCritVal n c) : (cuspPoly n c - C t).Separable := by
  rw [separable_def, derivative_sub, derivative_C, sub_zero]
  refine isCoprime_of_no_common_root fun x hx hdx => ?_
  have hev : (cuspPoly n c).eval x = t := by
    have h := hx
    simp only [IsRoot, eval_sub, eval_C, sub_eq_zero] at h
    exact h
  rcases eq_of_isRoot_derivative_cuspPoly hn hdx with rfl | rfl
  · exact ht0 (by rw [← hev, eval_cuspPoly_zero hn])
  · exact htc hev.symm

/-! ### The cover with two affine branch points -/

/-- The **cover of the line presented by `Xⁿ⁻¹(X - c) = T`**: an `n`-sheeted cover with two branch
points on the affine line. -/
@[reducible] def cuspCover (n : ℕ) (c : k) (hn : 2 ≤ n) : LineCover :=
  linearCover (cuspPoly n c) (cuspPoly_monic n c) (by rw [cuspPoly_natDegree (by omega)]; omega)

/-- **The cover presented by `Xⁿ⁻¹(X - c) = T` is unramified outside the two critical values.** -/
theorem cuspCover_isUnramifiedOutside (hn : 2 ≤ n) (c : k) :
    (cuspCover n c hn).IsUnramifiedOutside {0, cuspCritVal n c} :=
  linearCover_isUnramifiedOutside _ _ _ fun t ht => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    exact separable_cuspPoly_sub hn ht.1 ht.2

/-- **The cover presented by `Xⁿ⁻¹(X - c) = T` has at most two branch points on the affine
line.** -/
theorem cuspCover_branchLocus_ncard_le (hn : 2 ≤ n) (c : k) :
    (cuspCover n c hn).branchLocus.ncard ≤ 2 := by
  have hsub : (cuspCover n c hn).branchLocus ⊆ ({0, cuspCritVal n c} : Set k) :=
    ((cuspCover n c hn).isUnramifiedOutside_iff_branchLocus_subset _).mp
      (cuspCover_isUnramifiedOutside hn c)
  refine le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) ?_
  exact le_trans (Set.ncard_insert_le _ _) (by simp)

/-- **The deck group of the cover presented by `Xⁿ⁻¹(X - c) = T` is a group with at most two affine
branch points**, for every `n` and every `c`. -/
theorem isAffineDeckGroup_cuspCover (hn : 2 ≤ n) (c : k) :
    IsAffineDeckGroup 2 (cuspCover n c hn).deck :=
  (isAffineDeckGroup_deck _).mono (cuspCover_branchLocus_ncard_le hn c)

/-! ### Serre's base cover -/

/-- Serre's base polynomial is the polynomial `Xⁿ⁻¹(X - c)` for `c = n/(n-1)`. -/
theorem serreBaseP_eq_cuspPoly (n : ℕ) (hn : 2 ≤ n) :
    serreBaseP n = cuspPoly n ((n : k) / ((n : k) - 1)) :=
  serreBaseP_factor n hn

/-- The **cover of the line presented by Serre's base equation** `serreBaseP n = T`. -/
@[reducible] def serreBaseCover (n : ℕ) (hn : 2 ≤ n) : LineCover :=
  linearCover (serreBaseP n) (serreBaseP_monic n hn) (by rw [serreBaseP_natDegree n hn]; omega)

/-- **Serre's base cover is unramified outside two points of the affine line.** -/
theorem serreBaseCover_isUnramifiedOutside (n : ℕ) (hn : 2 ≤ n) :
    (serreBaseCover n hn).IsUnramifiedOutside
      {0, cuspCritVal n ((n : k) / ((n : k) - 1))} :=
  linearCover_isUnramifiedOutside _ _ _ fun t ht => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    rw [serreBaseP_eq_cuspPoly n hn]
    exact separable_cuspPoly_sub hn ht.1 ht.2

/-- **Serre's base cover has at most two branch points on the affine line.** -/
theorem serreBaseCover_branchLocus_ncard_le (n : ℕ) (hn : 2 ≤ n) :
    (serreBaseCover n hn).branchLocus.ncard ≤ 2 := by
  have hsub : (serreBaseCover n hn).branchLocus ⊆
      ({0, cuspCritVal n ((n : k) / ((n : k) - 1))} : Set k) :=
    ((serreBaseCover n hn).isUnramifiedOutside_iff_branchLocus_subset _).mp
      (serreBaseCover_isUnramifiedOutside n hn)
  refine le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) ?_
  exact le_trans (Set.ncard_insert_le _ _) (by simp)

/-- **The deck group of Serre's base cover is a group with at most two affine branch points.** -/
theorem isAffineDeckGroup_serreBaseCover (n : ℕ) (hn : 2 ≤ n) :
    IsAffineDeckGroup 2 (serreBaseCover n hn).deck :=
  (isAffineDeckGroup_deck _).mono (serreBaseCover_branchLocus_ncard_le n hn)

end Rigidity.RET

end
