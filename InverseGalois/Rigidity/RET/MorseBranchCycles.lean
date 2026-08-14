/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.MorseSymmetric
import InverseGalois.Rigidity.RET.RamificationBound
import InverseGalois.Rigidity.RET.Degeneracy

/-!
# Simple branching: the cover `Xⁿ - nX = T` and its transposition branch cycles

The cover of the line presented by an equation `g₀(X) = T` can degenerate only over a *critical
value* of `g₀`, a value taken by `g₀` at a root of its derivative: elsewhere the fibre `g₀ - t` has
only simple roots, and a place with separable fibre carries no inertia.  There are at most
`deg g₀ - 1` critical values, since they are the values of `g₀` at the roots of `g₀'`.

When `g₀` is a Morse polynomial — every fibre has at most one double point, and that point is a
nondegenerate critical point — the local monodromy over each of those values is as small as it can
be while being nontrivial: an inertia element is either trivial or a transposition of the roots of
the equation, of order two, generating the inertia group there.  Combined with the computation of
the deck group of a Morse cover this gives, for every `n ≥ 2`, a cover of the line with symmetric
deck group `Sₙ` branched over at most `n - 1` points of the affine line, all of whose branch cycles
are transpositions.  The polynomial `Xⁿ - nX` is such a `g₀`.

## Main definitions

* `Rigidity.RET.critValues` — the values a polynomial takes at the roots of its derivative.
* `Rigidity.RET.morseCover` — the cover of the line presented by `Xⁿ - nX = T`.

## Main results

* `Rigidity.RET.isUnramifiedOutside_critValues` — the cover `g₀(X) = T` is unramified outside the
  critical values of `g₀`.
* `Rigidity.RET.ncard_critValues_le` — a polynomial of degree `n` has at most `n - 1` critical
  values.
* `Rigidity.RET.isSwap_of_isInertiaAt_of_isMorse` — every nontrivial branch cycle of the cover
  presented by a Morse polynomial is a transposition of the roots of the equation.
* `Rigidity.RET.exists_symmetric_cover_simple_branching` — for every `n ≥ 2` there is a cover of
  the line with deck group `Sₙ`, branched over at most `n - 1` points of the affine line, whose
  nontrivial inertia elements all have order two.
-/

open Polynomial SerreBaseCover

noncomputable section

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

-- the deck group commutes with the coordinate ring of the base on the integral model, so it acts
-- on the roots of an equation living there
attribute [local instance] Rigidity.RET.instSMulCommDeck

/-! ### Critical values -/

/-- The **critical values** of a polynomial: the values it takes at the roots of its derivative. -/
def critValues (g₀ : Polynomial k) : Set k := (fun a => g₀.eval a) '' {a | (derivative g₀).IsRoot a}

theorem mem_critValues {g₀ : Polynomial k} {a : k} (ha : (derivative g₀).IsRoot a) :
    g₀.eval a ∈ critValues g₀ := ⟨a, ha, rfl⟩

/-- A polynomial of positive degree is not constant, so subtracting a constant leaves it nonzero. -/
theorem sub_C_ne_zero_of_natDegree_pos {g₀ : Polynomial k} (hd : 1 ≤ g₀.natDegree) (t : k) :
    g₀ - C t ≠ 0 := by
  intro h
  have hgt : g₀ = C t := sub_eq_zero.mp h
  rw [hgt, natDegree_C] at hd
  omega

/-- **Away from the critical values the fibre is separable**: every root of `g₀ - t` is simple. -/
theorem rootMultiplicity_le_one_of_not_mem_critValues {g₀ : Polynomial k} (hd : 1 ≤ g₀.natDegree)
    {t : k} (ht : t ∉ critValues g₀) (y : k) : (g₀ - C t).rootMultiplicity y ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨hroot, hder⟩ :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot (sub_C_ne_zero_of_natDegree_pos hd t)).mp hlt
  rw [derivative_sub, derivative_C, sub_zero] at hder
  refine ht ?_
  have hev : g₀.eval y = t := by
    have h := hroot
    rw [IsRoot, eval_sub, eval_C, sub_eq_zero] at h
    exact h
  rw [← hev]
  exact mem_critValues hder

/-- The derivative of a polynomial of positive degree is nonzero. -/
theorem derivative_ne_zero_of_natDegree_pos {g₀ : Polynomial k} (hd : 1 ≤ g₀.natDegree) :
    derivative g₀ ≠ 0 := by
  intro h
  have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h
  omega

/-- The critical values of a polynomial of positive degree form a finite set. -/
theorem finite_critValues {g₀ : Polynomial k} (hd : 1 ≤ g₀.natDegree) : (critValues g₀).Finite :=
  (Polynomial.finite_setOf_isRoot (derivative_ne_zero_of_natDegree_pos hd)).image _

/-- **A polynomial of degree `n` has at most `n - 1` critical values.** -/
theorem ncard_critValues_le {g₀ : Polynomial k} (hd : 1 ≤ g₀.natDegree) :
    (critValues g₀).ncard ≤ g₀.natDegree - 1 := by
  have hne : derivative g₀ ≠ 0 := derivative_ne_zero_of_natDegree_pos hd
  have hfin : {a : k | (derivative g₀).IsRoot a}.Finite := Polynomial.finite_setOf_isRoot hne
  have hle : {a : k | (derivative g₀).IsRoot a}.ncard ≤ g₀.natDegree - 1 := by
    exact (ncard_setOf_eval_eq_zero_le hne).trans (Polynomial.natDegree_derivative_le g₀)
  show ((fun a => g₀.eval a) '' {a : k | (derivative g₀).IsRoot a}).ncard ≤ g₀.natDegree - 1
  exact (Set.ncard_image_le hfin).trans hle

/-! ### The branch locus of an equation cover -/

variable (g₀ : Polynomial k) (hg : g₀.Monic) (hd : 1 ≤ g₀.natDegree)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The cover `g₀(X) = T` is unramified outside the critical values of `g₀`.**  Over any other
point the fibre of the equation is separable, and a place with separable fibre carries no
inertia. -/
theorem isUnramifiedOutside_critValues :
    (linearCover g₀ hg hd).IsUnramifiedOutside (critValues g₀) := by
  haveI := eqCover_isSplittingField (linearCoverC g₀) (genericPoly_linearCoverC_separable g₀ hg hd)
  intro t ht σ hσ
  obtain ⟨Q, hmax, hover, hmem⟩ := hσ
  haveI := hmax
  haveI := hover
  refine eq_one_of_separable_fibre (linearCover g₀ hg hd) (linearCoverC g₀)
    (linearCoverC_monic g₀ hg hd) t Q (fun y => ?_) hmem
  rw [linearCoverC_map_evalRingHom g₀ t]
  exact rootMultiplicity_le_one_of_not_mem_critValues hd ht y

/-! ### Morse covers have transposition branch cycles -/

/-- **A nontrivial inertia element of a Morse cover generates the inertia group there and has order
two.** -/
theorem isInertiaGenAt_and_orderOf_of_isMorse (h : IsMorse g₀) (t : k)
    {σ : (linearCover g₀ hg hd).deck} (hσ : (linearCover g₀ hg hd).IsInertiaAt t σ) (hne : σ ≠ 1) :
    (linearCover g₀ hg hd).IsInertiaGenAt t σ ∧ orderOf σ = 2 := by
  obtain ⟨a, hone, htwo⟩ := h t
  exact isInertiaGenAt_and_orderOf_linearCover g₀ hg hd t a hone htwo hσ hne

/-- **Every nontrivial branch cycle of a Morse cover is a transposition of the roots of the
equation.** -/
theorem isSwap_of_isInertiaAt_of_isMorse
    [DecidableEq ((linearCoverC g₀).rootSet (Bring (linearCover g₀ hg hd).M))]
    (h : IsMorse g₀) (t : k) {σ : (linearCover g₀ hg hd).deck}
    (hσ : (linearCover g₀ hg hd).IsInertiaAt t σ) (hne : σ ≠ 1) :
    (MulAction.toPermHom (linearCover g₀ hg hd).deck
      ((linearCoverC g₀).rootSet (Bring (linearCover g₀ hg hd).M)) σ).IsSwap := by
  obtain ⟨a, hone, htwo⟩ := h t
  exact isSwap_of_isInertiaAt_linearCover g₀ hg hd t a hone htwo hσ hne

/-! ### The cover `Xⁿ - nX = T` -/

variable {n : ℕ}

theorem morsePoly_natDegree_pos (hn : 2 ≤ n) : 1 ≤ (morsePoly n : Polynomial k).natDegree := by
  rw [morsePoly_natDegree hn]
  omega

/-- **The cover of the line presented by `Xⁿ - nX = T`.** -/
def morseCover (n : ℕ) (hn : 2 ≤ n) : LineCover :=
  linearCover (morsePoly n) (morsePoly_monic hn) (morsePoly_natDegree_pos hn)

/-- The deck group of the cover `Xⁿ - nX = T` is the symmetric group on `n` letters. -/
theorem nonempty_deck_morseCover_mulEquiv_perm (hn : 2 ≤ n) :
    Nonempty ((morseCover n hn).deck ≃* Equiv.Perm (Fin n)) :=
  nonempty_deck_morseCover hn (morsePoly_natDegree_pos hn)

/-- The cover `Xⁿ - nX = T` is unramified outside the critical values of `Xⁿ - nX`. -/
theorem isUnramifiedOutside_critValues_morseCover (hn : 2 ≤ n) :
    (morseCover n hn).IsUnramifiedOutside (critValues (morsePoly n)) :=
  isUnramifiedOutside_critValues (morsePoly n) (morsePoly_monic hn) (morsePoly_natDegree_pos hn)

/-- The polynomial `Xⁿ - nX` has at most `n - 1` critical values. -/
theorem ncard_critValues_morsePoly_le (hn : 2 ≤ n) :
    (critValues (morsePoly n : Polynomial k)).ncard ≤ n - 1 := by
  have h := ncard_critValues_le (g₀ := (morsePoly n : Polynomial k)) (morsePoly_natDegree_pos hn)
  rwa [morsePoly_natDegree hn] at h

/-- **A nontrivial inertia element of the cover `Xⁿ - nX = T` generates the inertia group at its
point and has order two.** -/
theorem isInertiaGenAt_and_orderOf_morseCover (hn : 2 ≤ n) (t : k)
    {σ : (morseCover n hn).deck} (hσ : (morseCover n hn).IsInertiaAt t σ) (hne : σ ≠ 1) :
    (morseCover n hn).IsInertiaGenAt t σ ∧ orderOf σ = 2 :=
  isInertiaGenAt_and_orderOf_of_isMorse (morsePoly n) (morsePoly_monic hn)
    (morsePoly_natDegree_pos hn) (isMorse_morsePoly hn) t hσ hne

/-- **Symmetric groups occur with simple branching.**

For every `n ≥ 2` there is a cover of the line with deck group the symmetric group on `n` letters,
branched over at most `n - 1` points of the affine line, every nontrivial inertia element of which
generates its inertia group and has order two. -/
theorem exists_symmetric_cover_simple_branching (n : ℕ) (hn : 2 ≤ n) :
    ∃ (L : LineCover) (_ : L.deck ≃* Equiv.Perm (Fin n)) (S : Set k),
      S.ncard ≤ n - 1 ∧ L.IsUnramifiedOutside S ∧
      ∀ (t : k) (σ : L.deck), L.IsInertiaAt t σ → σ ≠ 1 →
        L.IsInertiaGenAt t σ ∧ orderOf σ = 2 :=
  ⟨morseCover n hn, (nonempty_deck_morseCover_mulEquiv_perm hn).some, critValues (morsePoly n),
    ncard_critValues_morsePoly_le hn, isUnramifiedOutside_critValues_morseCover hn,
    fun t _ hσ hne => isInertiaGenAt_and_orderOf_morseCover hn t hσ hne⟩

end Rigidity.RET

end
