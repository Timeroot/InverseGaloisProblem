/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.PCentralFree
import InverseGalois.Solvable.PCentralShrink

/-!
# Shrinking a disposition `2`-group

The free object of rank `d * r` and `2`-class `n + 1` has its generators indexed by pairs: `r`
copies of a system of `d` generators.  A vector `a` of `r` bits selects some of the copies, and the
collapse `collapse a` sends the `i`-th generator of the `j`-th copy to the `i`-th generator of the
free object of rank `d` when the `j`-th copy is selected, and to the identity otherwise.  Whatever
`a` is, the collapse is surjective as soon as one copy is selected, so the free object of rank `d`
is a quotient of the free object of rank `d * r` in `2 ^ r - 1` different ways.

Shafarevich's shrinking process chooses among them.  Given an array of `d * r` elements of the last
nonzero term of the lower `2`-central series of the large free object — in the arithmetic
application, the obstruction attached to the `j`-th copy of the `i`-th block of ramified primes —
there is a choice of `a` for which each of the `d` rows, restricted to the selected copies, is
collapsed to the identity, provided only that `r` is large enough.  The bound on `r` depends on
nothing but `d` and `n`.

## Main definitions

* `InverseGalois.FreePClass.genPair`: the generators of the free object of rank `d * r`, indexed by
  pairs.
* `InverseGalois.FreePClass.collapse`: the homomorphism onto the free object of rank `d` selecting
  the copies marked by a vector of bits.

## Main results

* `InverseGalois.FreePClass.exists_ne_zero_forall_prod_eq_one`: **an array of elements of the last
  term of the lower `2`-central series is annihilated, row by row, by the collapse along a suitable
  nonzero vector of bits**, provided the number of copies exceeds an explicit bound.
* `InverseGalois.FreePClass.exists_rankMultiplier`: the same statement with the bound existentially
  quantified, the form the arithmetic induction consumes.

## Tags

`p`-group, lower central series, Chevalley–Warning, Shafarevich, disposition group
-/

namespace InverseGalois

namespace FreePClass

variable {n d r : ℕ}

/-- The generators of the free object of rank `d * r` and `2`-class `n + 1`, indexed by pairs: the
`i`-th generator of the `j`-th copy of a system of `d` generators. -/
def genPair (n d r : ℕ) (q : Fin d × Fin r) : FreePClass 2 (d * r) (n + 1) :=
  gen 2 (d * r) (n + 1) (finProdFinEquiv q)

theorem closure_range_genPair (n d r : ℕ) :
    Subgroup.closure (Set.range (genPair n d r)) = ⊤ := by
  have hrange : Set.range (genPair n d r) = Set.range (gen 2 (d * r) (n + 1)) :=
    finProdFinEquiv.surjective.range_comp (gen 2 (d * r) (n + 1))
  rw [hrange, closure_range_gen]

/-- The collapse of the free object of rank `d * r` onto the free object of rank `d` selecting the
copies of the generating system marked by a vector of bits. -/
noncomputable def collapse (a : Fin r → ZMod 2) :
    FreePClass 2 (d * r) (n + 1) →* FreePClass 2 d (n + 1) :=
  lift (lowerPCentralSeries_eq_bot 2 d (n + 1)) fun k =>
    if a (finProdFinEquiv.symm k).2 = 1 then gen 2 d (n + 1) (finProdFinEquiv.symm k).1 else 1

@[simp] theorem collapse_genPair (a : Fin r → ZMod 2) (q : Fin d × Fin r) :
    collapse a (genPair n d r q) = if a q.2 = 1 then gen 2 d (n + 1) q.1 else 1 := by
  rw [genPair, collapse, lift_gen]
  simp

/-- **An array of elements of the last nonzero term of the lower `2`-central series of the free
object of rank `d * r` is annihilated, row by row, by the collapse along a suitable nonzero vector
of bits**, provided the number `r` of copies of the generating system is large enough. -/
theorem exists_ne_zero_forall_prod_eq_one
    (θ : Fin d → Fin r → FreePClass 2 (d * r) (n + 1))
    (hθ : ∀ i j, θ i j ∈ lowerPCentralSeries 2 (FreePClass 2 (d * r) (n + 1)) n)
    (hr : d * charCount (FreePClass 2 d (n + 1)) n * (n + 2) < r) :
    ∃ a : Fin r → ZMod 2, a ≠ 0 ∧ ∀ i : Fin d,
      (((List.finRange r).filter fun j => decide (a j = 1)).map
        fun j => collapse a (θ i j)).prod = 1 :=
  InverseGalois.exists_ne_zero_forall_prod_eq_one (lowerPCentralSeries_eq_bot 2 (d * r) (n + 1))
    (lowerPCentralSeries_eq_bot 2 d (n + 1)) (closure_range_genPair n d r)
    (y := gen 2 d (n + 1)) (π := collapse) collapse_genPair hθ hr

/-- **The number of copies of the generating system needed for the shrinking process** depends only
on the rank and the class. -/
theorem exists_rankMultiplier (n d : ℕ) :
    ∃ r : ℕ, 0 < r ∧ ∀ θ : Fin d → Fin r → FreePClass 2 (d * r) (n + 1),
      (∀ i j, θ i j ∈ lowerPCentralSeries 2 (FreePClass 2 (d * r) (n + 1)) n) →
      ∃ a : Fin r → ZMod 2, a ≠ 0 ∧ ∀ i : Fin d,
        (((List.finRange r).filter fun j => decide (a j = 1)).map
          fun j => collapse a (θ i j)).prod = 1 :=
  ⟨d * charCount (FreePClass 2 d (n + 1)) n * (n + 2) + 1, Nat.succ_pos _,
    fun θ hθ => exists_ne_zero_forall_prod_eq_one θ hθ (Nat.lt_succ_self _)⟩

end FreePClass

end InverseGalois
