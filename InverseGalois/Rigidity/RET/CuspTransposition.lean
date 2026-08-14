/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.MorseInertia
import InverseGalois.Rigidity.RET.SymmetricBranch

/-!
# The branch cycles of `Xⁿ⁻¹(X - c) = T` at its finite critical value

The cover of the line presented by an equation `g₀(X) = T` degenerates over a point `t` exactly
where the fibre `g₀ - t` acquires a multiple root, and the multiplicity pattern of that fibre is
what the local monodromy sees: if the fibre over `t` has a single double point and simple points
elsewhere, the general Morse computation of `RET.MorseInertia` says that every inertia element
there is an involution, and a nontrivial one generates the inertia group and exchanges exactly two
roots of the equation.

For `g₀ = Xⁿ⁻¹(X - c)` with `c ≠ 0` the fibre over the critical value `cuspCritVal n c` of the
nonzero critical point is of exactly that shape: the critical point `(n-1)c/n` is a double point of
its fibre because the second derivative of `g₀` does not vanish there, and it is the only
degeneration in that fibre because the other critical point `0` sits in the *other* critical fibre.
So the cover has an honest transposition as its branch cycle over `cuspCritVal n c`, whatever the
degree.

Serre's base polynomial is of this shape, and its cover has symmetric deck group.  For `n ≥ 3` the
symmetric group is not cyclic, so neither of the two candidate branch points can be dispensed with:
the branch locus of Serre's base cover on the affine line is *exactly* `{0, cuspCritVal}`, and over
the second of those two points the local monodromy is a transposition.

## Main results

* `Rigidity.RET.not_isCyclic_perm` — the symmetric group on `n ≥ 3` letters is not cyclic.
* `Rigidity.RET.isInertiaGenAt_and_orderOf_linearCover` — a nontrivial inertia element of the cover
  `g₀(X) = T` over a point whose fibre has a single double point generates the inertia group there
  and has order two, and `Rigidity.RET.isSwap_of_isInertiaAt_linearCover` — it exchanges two roots
  of the equation.
* `Rigidity.RET.isInertiaGenAt_and_orderOf_cuspCover` — the same for the cover `Xⁿ⁻¹(X - c) = T`
  over `cuspCritVal n c`.
* `Rigidity.RET.branchLocus_serreBaseCover` — the branch locus of Serre's base cover on the affine
  line consists of exactly two points, for every `n ≥ 3`.
* `Rigidity.RET.exists_isInertiaGenAt_serreBaseCover` — Serre's base cover has a transposition as a
  distinguished branch cycle over its finite critical value.
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

variable {n : ℕ} {c : k}

/-! ### The symmetric group is not cyclic -/

/-- **The symmetric group on at least three letters is not cyclic.**  A cyclic group is abelian,
and two transpositions sharing exactly one letter do not commute. -/
theorem not_isCyclic_perm (hn : 3 ≤ n) : ¬ IsCyclic (Equiv.Perm (Fin n)) := by
  intro h
  letI : CommGroup (Equiv.Perm (Fin n)) := IsCyclic.commGroup
  obtain ⟨a, b, c, hab, hac, hbc⟩ : ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff]⟩
  have h1 : (Equiv.swap a b * Equiv.swap b c) a = b := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]
  have h2 : (Equiv.swap b c * Equiv.swap a b) a = c := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_left]
  rw [mul_comm, h2] at h1
  exact hbc h1.symm

/-! ### The fibre of `Xⁿ⁻¹(X - c)` over its nonzero critical value -/

theorem cast_ne_zero_of_two_le (hn : 2 ≤ n) : (n : k) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by omega)

theorem cast_sub_one_ne_zero (hn : 2 ≤ n) : (n : k) - 1 ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have : n = 1 := by exact_mod_cast h
  omega

/-- **The nonzero critical point of `Xⁿ⁻¹(X - c)` really is nonzero**, as soon as `c` is. -/
theorem cuspCritPt_ne_zero (hn : 2 ≤ n) (hc : c ≠ 0) : cuspCritPt n c ≠ 0 :=
  div_ne_zero (mul_ne_zero (cast_sub_one_ne_zero hn) hc) (cast_ne_zero_of_two_le hn)

/-- The critical point of `Xⁿ⁻¹(X - c)` is not a root of the polynomial: it is not `0`, and it is
not `c` either. -/
theorem cuspCritPt_sub_ne_zero (hn : 2 ≤ n) (hc : c ≠ 0) : cuspCritPt n c - c ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  rw [cuspCritPt, div_eq_iff (cast_ne_zero_of_two_le hn)] at h
  exact hc (by linear_combination -h)

/-- **The two critical values of `Xⁿ⁻¹(X - c)` are distinct**: the critical value at the nonzero
critical point is nonzero, while the one at `0` is `0`. -/
theorem cuspCritVal_ne_zero (hn : 2 ≤ n) (hc : c ≠ 0) : cuspCritVal n c ≠ 0 := by
  rw [cuspCritVal, cuspPoly]
  simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_C]
  exact mul_ne_zero (pow_ne_zero _ (cuspCritPt_ne_zero hn hc)) (cuspCritPt_sub_ne_zero hn hc)

/-- **The second derivative of `Xⁿ⁻¹(X - c)` at its nonzero critical point.**  The derivative is
`Xⁿ⁻²(nX - (n-1)c)`, whose second factor vanishes at the critical point, so only the derivative of
that factor survives. -/
theorem eval_derivative_two_cuspPoly (hn : 2 ≤ n) (c : k) :
    (derivative (derivative (cuspPoly n c))).eval (cuspCritPt n c)
      = cuspCritPt n c ^ (n - 2) * (n : k) := by
  have hn0 : (n : k) ≠ 0 := cast_ne_zero_of_two_le hn
  have hcrit : (n : k) * cuspCritPt n c - ((n : k) - 1) * c = 0 := by
    rw [cuspCritPt]
    field_simp
    ring
  rw [derivative_cuspPoly hn, derivative_mul, derivative_X_pow]
  simp only [derivative_sub, derivative_mul, derivative_C, derivative_X, zero_mul, mul_one,
    zero_add, sub_zero, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub]
  linear_combination ((n - 2 : ℕ) : k) * cuspCritPt n c ^ (n - 2 - 1) * hcrit

/-- **The critical point of `Xⁿ⁻¹(X - c)` is a nondegenerate critical point**, so it is a double
point of its own fibre. -/
theorem not_isRoot_derivative_two_cuspPoly (hn : 2 ≤ n) (hc : c ≠ 0) :
    ¬ (derivative (derivative (cuspPoly n c))).IsRoot (cuspCritPt n c) := by
  rw [IsRoot, eval_derivative_two_cuspPoly hn]
  exact mul_ne_zero (pow_ne_zero _ (cuspCritPt_ne_zero hn hc)) (cast_ne_zero_of_two_le hn)

/-- **The fibre of `Xⁿ⁻¹(X - c)` over its nonzero critical value degenerates only at the critical
point.**  A repeated point of that fibre is a critical point, and the other critical point `0` has
critical value `0`, which is not the value in question. -/
theorem eq_cuspCritPt_of_isRoot (hn : 2 ≤ n) (hc : c ≠ 0) {x : k}
    (hx : (cuspPoly n c - C (cuspCritVal n c)).IsRoot x)
    (hx' : (derivative (cuspPoly n c)).IsRoot x) : x = cuspCritPt n c := by
  have hev : (cuspPoly n c).eval x = cuspCritVal n c := by
    have h := hx
    simp only [IsRoot, eval_sub, eval_C, sub_eq_zero] at h
    exact h
  rcases eq_of_isRoot_derivative_cuspPoly hn hx' with rfl | rfl
  · exact absurd (hev.symm.trans (eval_cuspPoly_zero hn c)) (cuspCritVal_ne_zero hn hc)
  · rfl

/-! ### Transposition branch cycles of a linear cover -/

section LinearCover

variable (g₀ : Polynomial k) (hg : g₀.Monic) (hd : 1 ≤ g₀.natDegree) (t a : k)

/-- The Morse condition at a place of the cover `g₀(X) = T` over a point whose fibre has a single
double point. -/
private theorem morse_linearCover
    (hone : ∀ x : k, (g₀ - C t).IsRoot x → (derivative g₀).IsRoot x → x = a)
    (htwo : ¬ (derivative (derivative g₀)).IsRoot a)
    (Q : Ideal (Bring (linearCover g₀ hg hd).M)) [Q.IsMaximal] [Q.LiesOver (placeP t)] :
    ((linearCoverC g₀).rootSet (Bring (linearCover g₀ hg hd).M)).ncard
      ≤ ((linearCoverC g₀).rootSet (Bring (linearCover g₀ hg hd).M ⧸ Q)).ncard + 1 := by
  have hfib : (linearCoverC g₀).map (evalRingHom t) = g₀ - C t := linearCoverC_map_evalRingHom g₀ t
  have hder : derivative (g₀ - C t) = derivative g₀ := by
    rw [derivative_sub, derivative_C, sub_zero]
  refine ncard_rootSet_le_of_fibre (linearCover g₀ hg hd) (linearCoverC g₀)
    (linearCoverC_monic g₀ hg hd) t Q a ?_ ?_
  · intro x hx hx'
    rw [hfib] at hx hx'
    rw [hder] at hx'
    exact hone x hx hx'
  · rw [hfib, hder]
    exact htwo

/-- **A nontrivial inertia element of the cover `g₀(X) = T` over a point whose fibre has a single
double point generates the inertia group there, and has order two.**  The fibre of the equation
over such a point has only one collision of residues, so an inertia element can only exchange two
roots — and the geometric inertia groups are cyclic. -/
theorem isInertiaGenAt_and_orderOf_linearCover
    (hone : ∀ x : k, (g₀ - C t).IsRoot x → (derivative g₀).IsRoot x → x = a)
    (htwo : ¬ (derivative (derivative g₀)).IsRoot a)
    {σ : (linearCover g₀ hg hd).deck} (hσ : (linearCover g₀ hg hd).IsInertiaAt t σ) (hne : σ ≠ 1) :
    (linearCover g₀ hg hd).IsInertiaGenAt t σ ∧ orderOf σ = 2 := by
  haveI := eqCover_isSplittingField (linearCoverC g₀) (genericPoly_linearCoverC_separable g₀ hg hd)
  obtain ⟨Q, hmax, hover, hmem⟩ := hσ
  haveI := hmax
  haveI := hover
  obtain ⟨hgen, hord⟩ := isInertiaGen_and_orderOf (linearCover g₀ hg hd) (linearCoverC g₀)
    (linearCoverC_monic g₀ hg hd) t Q (morse_linearCover g₀ hg hd t a hone htwo Q) hmem hne
  exact ⟨⟨Q, hmax, hover, hgen⟩, hord⟩

/-- **The branch cycle of the cover `g₀(X) = T` over a point whose fibre has a single double point
is a transposition of the roots of the equation.** -/
theorem isSwap_of_isInertiaAt_linearCover
    [DecidableEq ((linearCoverC g₀).rootSet (Bring (linearCover g₀ hg hd).M))]
    (hone : ∀ x : k, (g₀ - C t).IsRoot x → (derivative g₀).IsRoot x → x = a)
    (htwo : ¬ (derivative (derivative g₀)).IsRoot a)
    {σ : (linearCover g₀ hg hd).deck} (hσ : (linearCover g₀ hg hd).IsInertiaAt t σ) (hne : σ ≠ 1) :
    (MulAction.toPermHom (linearCover g₀ hg hd).deck
      ((linearCoverC g₀).rootSet (Bring (linearCover g₀ hg hd).M)) σ).IsSwap := by
  haveI := eqCover_isSplittingField (linearCoverC g₀) (genericPoly_linearCoverC_separable g₀ hg hd)
  obtain ⟨Q, hmax, hover, hmem⟩ := hσ
  haveI := hmax
  haveI := hover
  exact isSwap_of_mem_geomInertia (linearCover g₀ hg hd) (linearCoverC g₀)
    (linearCoverC_monic g₀ hg hd) t Q (morse_linearCover g₀ hg hd t a hone htwo Q) hmem hne

end LinearCover

/-! ### The cover `Xⁿ⁻¹(X - c) = T` -/

/-- **A nontrivial inertia element of the cover `Xⁿ⁻¹(X - c) = T` over its nonzero critical value
generates the inertia group there and has order two.** -/
theorem isInertiaGenAt_and_orderOf_cuspCover (hn : 2 ≤ n) (hc : c ≠ 0)
    {σ : (cuspCover n c hn).deck}
    (hσ : (cuspCover n c hn).IsInertiaAt (cuspCritVal n c) σ) (hne : σ ≠ 1) :
    (cuspCover n c hn).IsInertiaGenAt (cuspCritVal n c) σ ∧ orderOf σ = 2 :=
  isInertiaGenAt_and_orderOf_linearCover (cuspPoly n c) _ _ _ (cuspCritPt n c)
    (fun _ hx hx' => eq_cuspCritPt_of_isRoot hn hc hx hx')
    (not_isRoot_derivative_two_cuspPoly hn hc) hσ hne

/-! ### Serre's base cover -/

/-- The finite critical value of Serre's base polynomial. -/
@[reducible] def serreBaseCritVal (n : ℕ) : k := cuspCritVal n ((n : k) / ((n : k) - 1))

theorem serreBaseC_ne_zero (hn : 2 ≤ n) : ((n : k) / ((n : k) - 1)) ≠ 0 :=
  div_ne_zero (cast_ne_zero_of_two_le hn) (cast_sub_one_ne_zero hn)

/-- **A nontrivial inertia element of Serre's base cover over its finite critical value generates
the inertia group there and has order two.** -/
theorem isInertiaGenAt_and_orderOf_serreBaseCover (hn : 2 ≤ n)
    {σ : (serreBaseCover n hn).deck}
    (hσ : (serreBaseCover n hn).IsInertiaAt (serreBaseCritVal n) σ) (hne : σ ≠ 1) :
    (serreBaseCover n hn).IsInertiaGenAt (serreBaseCritVal n) σ ∧ orderOf σ = 2 := by
  have hc : ((n : k) / ((n : k) - 1)) ≠ 0 := serreBaseC_ne_zero hn
  refine isInertiaGenAt_and_orderOf_linearCover (serreBaseP n) _ _ _
    (cuspCritPt n ((n : k) / ((n : k) - 1))) ?_ ?_ hσ hne
  · intro x hx hx'
    rw [serreBaseP_eq_cuspPoly n hn] at hx hx'
    exact eq_cuspCritPt_of_isRoot hn hc hx hx'
  · rw [serreBaseP_eq_cuspPoly n hn]
    exact not_isRoot_derivative_two_cuspPoly hn hc

/-- Serre's base cover would be cyclic if it had at most one affine branch point, and for `n ≥ 3`
it is not. -/
theorem not_ncard_branchLocus_le_one_serreBaseCover (hn : 3 ≤ n) :
    ¬ (serreBaseCover n (by omega : 2 ≤ n)).branchLocus.ncard ≤ 1 := fun hle =>
  not_isCyclic_perm hn (isAffineDeckGroup_one_iff.mp
    (((isAffineDeckGroup_deck _).mono hle).congr (nonempty_deck_serreBaseCover n hn).some))

/-- **Both critical values of Serre's base polynomial are genuine branch points**, for `n ≥ 3`:
the branch locus of Serre's base cover on the affine line is exactly the pair of critical values.
Either of them alone would make the deck group cyclic, and the symmetric group is not. -/
theorem branchLocus_serreBaseCover (hn : 3 ≤ n) :
    (serreBaseCover n (by omega : 2 ≤ n)).branchLocus = {0, serreBaseCritVal n} := by
  have hsub : (serreBaseCover n (by omega : 2 ≤ n)).branchLocus ⊆ {0, serreBaseCritVal n} :=
    ((serreBaseCover n _).isUnramifiedOutside_iff_branchLocus_subset _).mp
      (serreBaseCover_isUnramifiedOutside n (by omega))
  refine subset_antisymm hsub ?_
  have hone : ∀ u : k,
      (serreBaseCover n (by omega : 2 ≤ n)).branchLocus ⊆ {u} →
        ¬ (serreBaseCover n (by omega : 2 ≤ n)).branchLocus.ncard ≤ 1 → False := by
    intro u hu hcon
    exact hcon (le_trans (Set.ncard_le_ncard hu (Set.finite_singleton u))
      (le_of_eq (Set.ncard_singleton u)))
  rintro x (rfl | rfl)
  · by_contra hx
    refine hone (serreBaseCritVal n) (fun y hy => ?_) (not_ncard_branchLocus_le_one_serreBaseCover hn)
    rcases hsub hy with h | h
    · exact absurd (h ▸ hy) hx
    · exact h
  · by_contra hx
    refine hone 0 (fun y hy => ?_) (not_ncard_branchLocus_le_one_serreBaseCover hn)
    rcases hsub hy with h | h
    · exact h
    · exact absurd (h ▸ hy) hx

/-- **Serre's base cover has a transposition as a distinguished branch cycle over its finite
critical value.**

The cover of the line presented by `serreBaseP n = T` has symmetric deck group; for `n ≥ 3` its
finite critical value is a genuine branch point, and the fibre there has a single double point, so
the inertia group at every place over it is generated by an involution. -/
theorem exists_isInertiaGenAt_serreBaseCover (hn : 3 ≤ n) :
    ∃ σ : (serreBaseCover n (by omega : 2 ≤ n)).deck, σ ≠ 1 ∧
      (serreBaseCover n (by omega : 2 ≤ n)).IsInertiaGenAt (serreBaseCritVal n) σ ∧
        orderOf σ = 2 := by
  have hmem : serreBaseCritVal n ∈ (serreBaseCover n (by omega : 2 ≤ n)).branchLocus := by
    rw [branchLocus_serreBaseCover hn]
    exact Set.mem_insert_of_mem _ rfl
  obtain ⟨σ, hne, hσ⟩ := hmem
  exact ⟨σ, hne, isInertiaGenAt_and_orderOf_serreBaseCover (by omega) hσ hne⟩

end Rigidity.RET

end
