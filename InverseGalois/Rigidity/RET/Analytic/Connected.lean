/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Clopen

/-!
# An irreducible family has a connected root cover

The analytic counterpart of irreducibility is connectedness.  If the root variety of a monic family
of equations split into two parts over the complement of the degeneracy set, each part open and
closed, then each part would select a piece of every fibre; the selection is cut out by a monic
algebraic factor of the family, and both that factor and its complementary factor would have
positive degree.  So an irreducible family has a connected root cover.

The hypothesis is stated on the family itself; for a monic family it is the same as irreducibility
over the field of rational functions, because a monic polynomial is primitive.

## Main results

* `Rigidity.RET.Analytic.isPreconnected_puncturedVariety` — the part of the root variety over the
  complement of the degeneracy set of an irreducible family is connected.
* `Rigidity.RET.Analytic.isConnected_puncturedVariety` — the same, with nonemptiness.
* `Rigidity.RET.Analytic.irreducible_of_irreducible_map_ratFunc` — irreducibility over the field of
  rational functions transfers to the family itself.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Analytic

variable {P : Polynomial (Polynomial ℂ)} {S : Set ℂ}

theorem selectedRoots_subset (W : Set (rootVariety P)) (z : ℂ) :
    selectedRoots P W z ⊆ (spec P z).roots.toFinset := by
  classical
  intro a ha
  rw [selectedRoots, Finset.mem_filter] at ha
  exact ha.1

/-- **The root cover of an irreducible family is connected.**  A part of it that is open and closed
is cut out by a monic factor, and a proper nonempty part would make that factor and its
complementary factor both nontrivial. -/
theorem isPreconnected_puncturedVariety (hP : P.Monic) (hdeg : 0 < P.natDegree)
    (hirr : Irreducible P) (hS : S.Finite) (hsep : ∀ z ∉ S, (spec P z).Separable) :
    IsPreconnected (puncturedVariety P S) := by
  intro u v hu hv hcover hnu hnv
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hSc : IsOpen (Sᶜ : Set ℂ) := hS.isClosed.isOpen_compl
  have hEopen : IsOpen (puncturedVariety P S) := isOpen_puncturedVariety hSc
  have hWopen : IsOpen (puncturedVariety P S ∩ u) := hEopen.inter hu
  have hdiff : puncturedVariety P S \ (puncturedVariety P S ∩ u) = puncturedVariety P S ∩ v := by
    ext x
    constructor
    · rintro ⟨hxE, hxW⟩
      have hxu : x ∉ u := fun h => hxW ⟨hxE, h⟩
      rcases hcover hxE with h | h
      · exact absurd h hxu
      · exact ⟨hxE, h⟩
    · rintro ⟨hxE, hxv⟩
      refine ⟨hxE, ?_⟩
      rintro ⟨-, hxu⟩
      exact Set.eq_empty_iff_forall_notMem.1 hempty x ⟨hxE, hxu, hxv⟩
  have hWcoopen : IsOpen (puncturedVariety P S \ (puncturedVariety P S ∩ u)) := by
    rw [hdiff]
    exact hEopen.inter hv
  obtain ⟨Q, m, hQmonic, hQdeg, hQdvd, hcard, -⟩ :=
    exists_monic_factor_of_clopen hP hdeg hS hsep hWopen hWcoopen
  -- the selected part is nonempty over the parameter of a point of the first piece
  obtain ⟨q, hqE, hqu⟩ := hnu
  have hqS : ((q : ℂ × ℂ)).1 ∉ S := hqE
  have hmpos : 0 < m := by
    rw [← hcard _ hqS]
    refine Finset.card_pos.2 ⟨((q : ℂ × ℂ)).2, ?_⟩
    rw [mem_selectedRoots hP]
    exact ⟨q.2, hqE, hqu⟩
  -- and it misses a point of the second piece
  obtain ⟨q', hq'E, hq'v⟩ := hnv
  have hq'S : ((q' : ℂ × ℂ)).1 ∉ S := hq'E
  have hq'W : q' ∉ puncturedVariety P S ∩ u := fun h =>
    Set.eq_empty_iff_forall_notMem.1 hempty q' ⟨hq'E, h.2, hq'v⟩
  have hmlt : m < P.natDegree := by
    rw [← hcard _ hq'S, ← card_rootFinset hP (hsep _ hq'S)]
    refine Finset.card_lt_card
      ((Finset.ssubset_iff_of_subset (selectedRoots_subset _ _)).2 ⟨((q' : ℂ × ℂ)).2, ?_, ?_⟩)
    · rw [mem_rootFinset hP]
      exact q'.2
    · rw [mem_selectedRoots hP]
      rintro ⟨h, hmem⟩
      exact hq'W hmem
  -- both factors are nontrivial, contradicting irreducibility
  obtain ⟨R, hR⟩ := hQdvd
  have hRmonic : R.Monic := hQmonic.of_mul_monic_left (by rw [← hR]; exact hP)
  have hdegsum : P.natDegree = m + R.natDegree := by
    rw [hR, hQmonic.natDegree_mul' hRmonic.ne_zero, hQdeg]
  rcases hirr.isUnit_or_isUnit hR with h | h
  · rw [hQmonic.eq_one_of_isUnit h, Polynomial.natDegree_one] at hQdeg
    omega
  · rw [hRmonic.eq_one_of_isUnit h, Polynomial.natDegree_one] at hdegsum
    omega

theorem nonempty_puncturedVariety (hP : P.Monic) (hdeg : 0 < P.natDegree) (hS : S.Finite) :
    (puncturedVariety P S).Nonempty := by
  obtain ⟨z, hz⟩ := hS.infinite_compl.nonempty
  obtain ⟨q, hq⟩ := fiber_nonempty hP hdeg z
  exact ⟨q, by rw [mem_puncturedVariety, show ((q : ℂ × ℂ)).1 = z from hq]; exact hz⟩

/-- **The root cover of an irreducible family is connected.** -/
theorem isConnected_puncturedVariety (hP : P.Monic) (hdeg : 0 < P.natDegree)
    (hirr : Irreducible P) (hS : S.Finite) (hsep : ∀ z ∉ S, (spec P z).Separable) :
    IsConnected (puncturedVariety P S) :=
  ⟨nonempty_puncturedVariety hP hdeg hS, isPreconnected_puncturedVariety hP hdeg hirr hS hsep⟩

/-- **Irreducibility over the field of rational functions transfers to a monic family**, because a
monic polynomial is primitive. -/
theorem irreducible_of_irreducible_map_ratFunc (hP : P.Monic)
    (h : Irreducible (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)))) : Irreducible P :=
  (hP.isPrimitive.irreducible_iff_irreducible_map_fraction_map).2 h

end Rigidity.RET.Analytic

end
