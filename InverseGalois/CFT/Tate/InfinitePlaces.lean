/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Fibers

/-!
# The lattice of the infinite places of a Galois extension

The Galois group of an extension of number fields permutes the infinite places of the top field,
and two of them lie in the same orbit exactly when they restrict to the same place of the base.
The set of infinite places is therefore fibred over the infinite places of the base field with the
orbits as fibres, and for a cyclic Galois group the Herbrand quotient of the free lattice it spans
is the product over the places of the base of the order of the decomposition group of a place
above it.  That order is one or two: it is two exactly at the places that ramify, the real places
of the base having a complex place above them.

This is the contribution of the infinite places to the Herbrand quotient of the idele class group,
and it is also the shape of the unit lattice: the logarithmic embedding identifies the real
representation of the units with the trace-zero part of this permutation representation.

## Main definitions

* `InverseGalois.CFT.placeAbove`: a place of the extension above a given place of the base field.

## Main results

* `InverseGalois.CFT.comap_smul_infinitePlace`: the restriction of a place to the base field is
  invariant under the Galois group.
* `InverseGalois.CFT.herbrand_permLatticeAut_infinitePlace`: **the Herbrand quotient of the free
  lattice on the infinite places is the product of the orders of the decomposition groups.**
* `InverseGalois.CFT.herbrand_permLatticeAut_infinitePlace_ramified`: the same product written as a
  power of two, one factor for each ramified place of the base field.

## Tags

Tate cohomology, Herbrand quotient, infinite place, decomposition group, ramification
-/

namespace InverseGalois.CFT

open MulAction NumberField NumberField.InfinitePlace

variable (k K : Type*) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-! ### The places above a place of the base field -/

/-- **A place of the extension above a given place of the base field.** -/
noncomputable def placeAbove (v : InfinitePlace k) : InfinitePlace K :=
  (InfinitePlace.comap_surjective (k := k) (K := K) v).choose

omit [NumberField k] [NumberField K] in
theorem comap_placeAbove (v : InfinitePlace k) :
    (placeAbove k K v).comap (algebraMap k K) = v :=
  (InfinitePlace.comap_surjective (k := k) (K := K) v).choose_spec

variable {k K}

omit [NumberField k] [NumberField K] in
/-- **The restriction of a place to the base field is invariant under the Galois group.** -/
theorem comap_smul_infinitePlace (g : Gal(K/k)) (w : InfinitePlace K) :
    (g • w).comap (algebraMap k K) = w.comap (algebraMap k K) :=
  (InfinitePlace.mem_orbit_iff.mp ⟨g, rfl⟩).symm

omit [NumberField k] [NumberField K] in
/-- **The Galois group acts transitively on the places above a place of the base field.** -/
theorem exists_smul_placeAbove_eq (w : InfinitePlace K) :
    ∃ g : Gal(K/k), g • placeAbove k K (w.comap (algebraMap k K)) = w :=
  InfinitePlace.exists_smul_eq_of_comap_eq (comap_placeAbove k K _)

/-! ### The Herbrand quotient -/

/-- **The Herbrand quotient of the free lattice on the infinite places of a cyclic Galois extension
is the product of the orders of the decomposition groups** of a chosen place above each place of
the base field. -/
theorem herbrand_permLatticeAut_infinitePlace {σ : Gal(K/k)}
    (hσ : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ} (hn : Nat.card Gal(K/k) = n) :
    herbrand (permLatticeAut (toPerm σ : Equiv.Perm (InfinitePlace K))) n
      = ∏ v : InfinitePlace k, (Nat.card (stabilizer Gal(K/k) (placeAbove k K v)) : ℚ) := by
  haveI : Module.Finite k K := Module.Finite.of_restrictScalars_finite ℚ k K
  exact herbrand_permLatticeAut_toPerm_of_fibers comap_smul_infinitePlace (comap_placeAbove k K)
    exists_smul_placeAbove_eq hσ hn

open scoped Classical in
/-- **The Herbrand quotient of the free lattice on the infinite places is a power of two**, one
factor for each place of the base field that ramifies in the extension. -/
theorem herbrand_permLatticeAut_infinitePlace_ramified {σ : Gal(K/k)}
    (hσ : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ} (hn : Nat.card Gal(K/k) = n) :
    herbrand (permLatticeAut (toPerm σ : Equiv.Perm (InfinitePlace K))) n
      = ∏ v : InfinitePlace k, if (placeAbove k K v).IsUnramified k then (1 : ℚ) else 2 := by
  rw [herbrand_permLatticeAut_infinitePlace hσ hn]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [InfinitePlace.card_stabilizer]
  by_cases h : (placeAbove k K v).IsUnramified k <;> simp [h]

end InverseGalois.CFT
