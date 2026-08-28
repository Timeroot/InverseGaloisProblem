/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.NormSurjective
import InverseGalois.CFT.Units.FirstInequality

/-!
# A cyclic extension all of whose fixed idele classes are norms is trivial

The first inequality bounds the order of the zeroth Tate group of the idele class group of a cyclic
extension below by the degree.  Read the other way round it is a triviality criterion: if every
idele class fixed by the Galois group is a norm then that Tate group has a single element, so the
degree is at most one and the extension is trivial.

This is the form in which the first inequality rules out extensions: an extension which is split at
enough places has all of its fixed classes among the norms, and therefore does not exist.
Contrapositively, a nontrivial cyclic extension always has a fixed idele class that is not a norm.

## Main results

* `InverseGalois.CFT.card_le_one_of_forall_normHom_ideleClassAut`: **a cyclic extension whose fixed
  idele classes are all norms has degree at most one.**
* `InverseGalois.CFT.subsingleton_gal_of_forall_normHom_ideleClassAut`: the same, read as the
  triviality of the Galois group.
* `InverseGalois.CFT.exists_fixed_not_normHom_ideleClassAut`: **a nontrivial cyclic extension has a
  fixed idele class that is not a norm.**

## Tags

number field, idele class group, first inequality, norm, Tate cohomology
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section Cyclic

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (σ : Gal(K/k)) {n : ℕ} (hn : Nat.card Gal(K/k) = n) [NeZero n]
  (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ)

include hn hgen

/-- **A cyclic extension of number fields all of whose fixed idele classes are norms has degree at
most one.**  The hypothesis says that the zeroth Tate group of the idele class group has a single
element, and the first inequality bounds the degree by its order. -/
theorem card_le_one_of_forall_normHom_ideleClassAut
    (h : ∀ x : ↥(idele K) ⧸ (ideleDiag K).range, ideleClassAut (k := k) σ x = x →
      ∃ y, normHom (ideleClassAut (k := k) σ) n y = x) : n ≤ 1 := by
  haveI : Subsingleton (tateH0 (ideleClassAut (k := k) σ) n) := subsingleton_tateH0_iff.mpr h
  have hle := first_inequality σ hn hgen
  rwa [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩] at hle

/-- **A cyclic extension of number fields all of whose fixed idele classes are norms is
trivial.** -/
theorem subsingleton_gal_of_forall_normHom_ideleClassAut
    (h : ∀ x : ↥(idele K) ⧸ (ideleDiag K).range, ideleClassAut (k := k) σ x = x →
      ∃ y, normHom (ideleClassAut (k := k) σ) n y = x) : Subsingleton Gal(K/k) := by
  refine Finite.card_le_one_iff_subsingleton.mp ?_
  rw [hn]
  exact card_le_one_of_forall_normHom_ideleClassAut σ hn hgen h

/-- **A nontrivial cyclic extension of number fields has an idele class which is fixed by the
Galois group and is not a norm.** -/
theorem exists_fixed_not_normHom_ideleClassAut (h1 : 1 < n) :
    ∃ x : ↥(idele K) ⧸ (ideleDiag K).range, ideleClassAut (k := k) σ x = x ∧
      ∀ y, normHom (ideleClassAut (k := k) σ) n y ≠ x := by
  by_contra hc
  push_neg at hc
  exact absurd (card_le_one_of_forall_normHom_ideleClassAut σ hn hgen hc) (by omega)

end Cyclic

end InverseGalois.CFT
