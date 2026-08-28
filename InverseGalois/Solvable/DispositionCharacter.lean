/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.DispositionShrink
import InverseGalois.Solvable.PCentralCharacter
import InverseGalois.Solvable.PCentralTower

/-!
# The coordinate character of a collapsed disposition group

The collapse of the free object of rank `d * r` onto the free object of rank `d` selects the copies
of the generating system marked by a vector of bits.  Read through the coordinate characters of the
two free objects, it becomes a completely explicit linear map: the `i`-th coordinate of the collapse
of an element is the sum of its coordinates at the pairs `(i, j)` with the `j`-th copy selected.

That description is what the arithmetic side of the shrinking process consumes.  A square root of a
product of primes whose sign character is the `(i, j)`-th coordinate is moved by an automorphism
exactly as that coordinate says, so the product of the selected square roots of a row is fixed by
the kernel of the collapse and therefore lives in the shrunken field, where its sign character is
the `i`-th coordinate.

The two remaining compatibilities are of the same nature: the coordinate character does not see the
`p`-class, and the collapse commutes with the projection of the tower.

## Main definitions

* `InverseGalois.FreePClass.mergeChar`: the linear map summing the coordinates of a row over the
  selected copies.

## Main results

* `InverseGalois.FreePClass.coordClass_comp_proj`: the coordinate character is compatible with the
  projection of the tower of free objects.
* `InverseGalois.FreePClass.coordClass_comp_collapse`: **read through the coordinate characters,
  the collapse sums the coordinates of each row over the selected copies.**
* `InverseGalois.FreePClass.proj_comp_collapse`: the collapse commutes with the projection of the
  tower.
* `InverseGalois.FreePClass.collapse_surjective`: the collapse is onto as soon as one copy is
  selected.

## Tags

`p`-group, free object, coordinate character, collapse, Shafarevich, disposition group
-/

namespace InverseGalois

namespace FreePClass

open Multiplicative

/-! ### The coordinate character along the tower -/

/-- **The coordinate character is compatible with the projection of the tower of free objects.**
Both sides send the `i`-th distinguished generator to the `i`-th standard basis vector. -/
theorem coordClass_comp_proj (p d : ℕ) [NeZero p] {c : ℕ} (hc : 1 ≤ c) :
    (coordClass p d hc).comp (proj p d c) = coordClass p d (hc.trans (Nat.le_succ c)) :=
  eq_coordClass _ fun i => by rw [MonoidHom.comp_apply, proj_gen, coordClass_gen]

/-! ### The collapse, read through the coordinate characters -/

variable {n d r : ℕ}

/-- The linear map summing the coordinates of each row over the copies selected by a vector of
bits. -/
noncomputable def mergeChar (d : ℕ) (a : Fin r → ZMod 2) :
    Multiplicative (Fin (d * r) → ZMod 2) →* Multiplicative (Fin d → ZMod 2) :=
  MonoidHom.mk' (fun f => ofAdd fun i =>
      ∑ j ∈ Finset.univ.filter fun j => a j = 1, toAdd f (finProdFinEquiv (i, j)))
    fun _ _ => congrArg ofAdd (funext fun _ => Finset.sum_add_distrib)

theorem toAdd_mergeChar (d : ℕ) (a : Fin r → ZMod 2) (f : Multiplicative (Fin (d * r) → ZMod 2))
    (i : Fin d) : toAdd (mergeChar d a f) i =
      ∑ j ∈ Finset.univ.filter fun j => a j = 1, toAdd f (finProdFinEquiv (i, j)) :=
  rfl

/-- The merging map sends the standard basis vector of a pair to the standard basis vector of its
row when the copy is selected, and to zero otherwise. -/
theorem mergeChar_single (d : ℕ) (a : Fin r → ZMod 2) (q : Fin d × Fin r) (i : Fin d) :
    toAdd (mergeChar d a (ofAdd (Pi.single (finProdFinEquiv q) (1 : ZMod 2)))) i
      = if a q.2 = 1 then (Pi.single q.1 (1 : ZMod 2) : Fin d → ZMod 2) i else 0 := by
  rw [toAdd_mergeChar]
  have hsum : ∀ j : Fin r,
      toAdd (ofAdd (Pi.single (finProdFinEquiv q) (1 : ZMod 2) : Fin (d * r) → ZMod 2))
        (finProdFinEquiv (i, j))
      = if j = q.2 then (Pi.single q.1 (1 : ZMod 2) : Fin d → ZMod 2) i else 0 := by
    intro j
    show (Pi.single (finProdFinEquiv q) (1 : ZMod 2) : Fin (d * r) → ZMod 2)
      (finProdFinEquiv (i, j)) = _
    simp only [Pi.single_apply, finProdFinEquiv.apply_eq_iff_eq, Prod.ext_iff]
    by_cases h1 : i = q.1 <;> by_cases h2 : j = q.2 <;> simp [h1, h2]
  simp only [hsum, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Read through the coordinate characters, the collapse sums the coordinates of each row over
the selected copies.**  Both sides are homomorphisms, and the distinguished generators indexed by
pairs generate. -/
theorem coordClass_comp_collapse (a : Fin r → ZMod 2) :
    (coordClass 2 d (Nat.succ_pos n)).comp (collapse (n := n) (d := d) a)
      = (mergeChar d a).comp (coordClass 2 (d * r) (Nat.succ_pos n)) := by
  refine MonoidHom.eq_of_eqOn_dense (closure_range_genPair n d r) ?_
  rintro _ ⟨q, rfl⟩
  show coordClass 2 d (Nat.succ_pos n) (collapse a (genPair n d r q))
    = mergeChar d a (coordClass 2 (d * r) (Nat.succ_pos n) (genPair n d r q))
  rw [collapse_genPair, genPair, coordClass_gen]
  refine Multiplicative.toAdd.injective (funext fun i => ?_)
  rw [mergeChar_single]
  by_cases hj : a q.2 = 1
  · rw [if_pos hj, if_pos hj, coordClass_gen]
    rfl
  · rw [if_neg hj, if_neg hj, map_one]
    rfl

/-! ### The collapse along the tower -/

/-- **The collapse commutes with the projection of the tower of free objects.** -/
theorem proj_comp_collapse (m d r : ℕ) (a : Fin r → ZMod 2) :
    (proj 2 d (m + 1)).comp (collapse (n := m + 1) (d := d) a)
      = (collapse (n := m) (d := d) a).comp (proj 2 (d * r) (m + 1)) := by
  refine MonoidHom.eq_of_eqOn_dense (closure_range_genPair (m + 1) d r) ?_
  rintro _ ⟨q, rfl⟩
  show proj 2 d (m + 1) (collapse a (genPair (m + 1) d r q))
    = collapse a (proj 2 (d * r) (m + 1) (genPair (m + 1) d r q))
  rw [collapse_genPair, genPair, proj_gen]
  show _ = collapse a (genPair m d r q)
  rw [collapse_genPair]
  by_cases hj : a q.2 = 1
  · rw [if_pos hj, if_pos hj, proj_gen]
  · rw [if_neg hj, if_neg hj, map_one]

/-- **The collapse is onto as soon as one copy is selected.**  Every distinguished generator of the
target is the image of the corresponding generator of the selected copy. -/
theorem collapse_surjective {a : Fin r → ZMod 2} {j : Fin r} (hj : a j = 1) :
    Function.Surjective (collapse (n := n) (d := d) a) := by
  have hrange : ⊤ ≤ (collapse (n := n) (d := d) a).range := by
    rw [← closure_range_gen 2 d (n + 1)]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨genPair n d r (i, j), by rw [collapse_genPair, if_pos hj]⟩
  exact fun y => hrange (Subgroup.mem_top y)

end FreePClass

end InverseGalois
