/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootCover
import InverseGalois.Rigidity.RET.Degeneracy

/-!
# Fibres and separable locus of the root variety of a complex family

The root variety of a monic family of equations over the complex line projects to the line as a
covering map over any set of parameters where the specialized equation is separable.  This file
supplies the two pieces of bookkeeping that turn that statement into a genuine covering space of
known degree.

First, the fibre over a parameter is the set of roots of the specialized equation.  Over the
complex numbers a monic separable equation of degree `n` has exactly `n` roots, so every fibre
over the separable locus has exactly `P.natDegree` points, and every fibre at all is nonempty as
soon as the degree is positive.

Second, the separable locus is cofinite.  This is the degeneracy polynomial of the family: the
resultant of the equation with its derivative in the fibre variable is a polynomial in the
parameter which vanishes exactly where the specialized equation degenerates, and it is nonzero as
soon as the generic equation is separable.  That criterion was developed over an arbitrary field
of characteristic zero, and the specialization `spec` of the analytic side is literally the
specialization it speaks about, so it applies verbatim over `ℂ`.

Together these say: outside a finite set of parameters the root variety is a covering space of the
punctured line of degree `P.natDegree`.

## Main results

* `Rigidity.RET.Analytic.fiberEquivRoots` — the fibre over a parameter is the set of roots of the
  specialized equation.
* `Rigidity.RET.Analytic.card_fiber` — over a separable parameter the fibre has exactly
  `P.natDegree` points.
* `Rigidity.RET.Analytic.finite_compl_sepLocus` — the separable locus is cofinite.
* `Rigidity.RET.Analytic.isCoveringMap_restrict` — the restriction of the root projection to the
  preimage of a separable set is a covering map.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Analytic

/-! ### The fibre over a parameter -/

/-- **The fibre of the root projection over a parameter is the set of roots of the specialized
equation.** -/
def fiberEquivRoots (P : Polynomial (Polynomial ℂ)) (z : ℂ) :
    (rootProj P ⁻¹' {z}) ≃ {w : ℂ // (spec P z).eval w = 0} where
  toFun q := ⟨((q : rootVariety P) : ℂ × ℂ).2, by
    have hx : ((q : rootVariety P) : ℂ × ℂ).1 = z := q.2
    have h := (q : rootVariety P).2
    rwa [mem_rootVariety, hx] at h⟩
  invFun w := ⟨⟨(z, (w : ℂ)), w.2⟩, rfl⟩
  left_inv q := by
    have hx : ((q : rootVariety P) : ℂ × ℂ).1 = z := q.2
    exact Subtype.ext (Subtype.ext (Prod.ext hx.symm rfl))
  right_inv _ := rfl

/-- **Over a parameter where the specialized equation is separable the fibre has exactly as many
points as the degree of the family.**  The specialized equation is monic of the same degree, and
over the complex numbers a separable equation has as many roots as its degree. -/
theorem card_fiber {P : Polynomial (Polynomial ℂ)} (hP : P.Monic) {z : ℂ}
    (hz : (spec P z).Separable) : Nat.card (rootProj P ⁻¹' {z}) = P.natDegree := by
  have hne : spec P z ≠ 0 := (spec_monic hP z).ne_zero
  rw [Nat.card_congr (fiberEquivRoots P z)]
  have hcard : Nat.card {w : ℂ // (spec P z).eval w = 0} = (spec P z).roots.toFinset.card :=
    Nat.subtype_card _ fun w => by
      simp [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot]
  rw [hcard, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hz),
    ← (IsAlgClosed.splits (spec P z)).natDegree_eq_card_roots, natDegree_spec hP z]

/-- **Every fibre of the root projection is nonempty** once the family has positive degree: the
specialized equation is monic of that degree, and the complex numbers are algebraically closed. -/
theorem fiber_nonempty {P : Polynomial (Polynomial ℂ)} (hP : P.Monic) (hdeg : 0 < P.natDegree)
    (z : ℂ) : (rootProj P ⁻¹' {z}).Nonempty := by
  have hdz : 0 < (spec P z).degree :=
    natDegree_pos_iff_degree_pos.mp (by rw [natDegree_spec hP z]; exact hdeg)
  obtain ⟨w, hw⟩ := Complex.exists_root hdz
  exact ⟨⟨(z, w), hw⟩, rfl⟩

/-- **The root projection is surjective** once the family has positive degree. -/
theorem surjective_rootProj {P : Polynomial (Polynomial ℂ)} (hP : P.Monic)
    (hdeg : 0 < P.natDegree) : Function.Surjective (rootProj P) := by
  intro z
  obtain ⟨q, hq⟩ := fiber_nonempty hP hdeg z
  exact ⟨q, hq⟩

/-! ### The separable locus -/

/-- The **separable locus** of a family: the parameters where the specialized equation has no
repeated root. -/
def sepLocus (P : Polynomial (Polynomial ℂ)) : Set ℂ := {z : ℂ | (spec P z).Separable}

theorem mem_sepLocus {P : Polynomial (Polynomial ℂ)} {z : ℂ} :
    z ∈ sepLocus P ↔ (spec P z).Separable := Iff.rfl

/-- **The separable locus of a generically separable family is cofinite.**  Its complement is
contained in the zero set of the degeneracy polynomial of the family, which is a nonzero
polynomial precisely because the generic equation is separable. -/
theorem finite_compl_sepLocus (P : Polynomial (Polynomial ℂ)) (hP : P.Monic)
    (hdeg : 0 < P.natDegree)
    (hsep : (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))).Separable) :
    (sepLocus P)ᶜ.Finite :=
  finite_setOf_not_separable P hP hdeg hsep

/-- **The separable locus is open**: it is the complement of a finite set of complex numbers. -/
theorem isOpen_sepLocus (P : Polynomial (Polynomial ℂ)) (hP : P.Monic) (hdeg : 0 < P.natDegree)
    (hsep : (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))).Separable) : IsOpen (sepLocus P) := by
  rw [← compl_compl (sepLocus P)]
  exact ((finite_compl_sepLocus P hP hdeg hsep).isClosed).isOpen_compl

/-! ### The covering map over a separable set -/

/-- **The root projection restricted to the preimage of a set of separable parameters is a covering
map onto that set.** -/
theorem isCoveringMap_restrict {P : Polynomial (Polynomial ℂ)} (hP : P.Monic) {U : Set ℂ}
    (hsep : ∀ z ∈ U, (spec P z).Separable) :
    IsCoveringMap (U.restrictPreimage (rootProj P)) :=
  (isCoveringMapOn_rootProj hP hsep).isCoveringMap_restrictPreimage

/-- **The root projection is a covering map over the separable locus.** -/
theorem isCoveringMapOn_sepLocus {P : Polynomial (Polynomial ℂ)} (hP : P.Monic) :
    IsCoveringMapOn (rootProj P) (sepLocus P) :=
  isCoveringMapOn_rootProj hP fun _ hz => hz

/-- **Outside a finite set of parameters the root variety of a generically separable monic family
is a covering space of the line of degree the degree of the family.**  This is the analytic content
of the branch-cycle description of a cover: a finite set of parameters carries all the
degeneration, and away from it the family is an honest covering space of known degree. -/
theorem exists_finite_branch_covering (P : Polynomial (Polynomial ℂ)) (hP : P.Monic)
    (hdeg : 0 < P.natDegree)
    (hsep : (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))).Separable) :
    ∃ S : Set ℂ, S.Finite ∧ IsCoveringMapOn (rootProj P) Sᶜ ∧
      ∀ z ∈ Sᶜ, Nat.card (rootProj P ⁻¹' {z}) = P.natDegree := by
  refine ⟨(sepLocus P)ᶜ, finite_compl_sepLocus P hP hdeg hsep, ?_, ?_⟩
  · rw [compl_compl]
    exact isCoveringMapOn_sepLocus hP
  · intro z hz
    rw [compl_compl] at hz
    exact card_fiber hP hz

end Rigidity.RET.Analytic

end
