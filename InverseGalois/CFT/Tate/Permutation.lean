/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Congr
import InverseGalois.CFT.Tate.Pi
import InverseGalois.CFT.Tate.Shapiro
import InverseGalois.CFT.Tate.Trivial

/-!
# The Herbrand quotient of a permutation lattice

A cyclic group acting on a finite set acts on the free abelian group it generates, and that lattice
splits as the product of the lattices of the orbits.  Each orbit is a cyclic shift of a set of
coordinates, so the lattice it generates is the module induced from the trivial module `ℤ` over the
stabiliser of a point.  Shapiro's lemma computes the Tate groups of an induced module, the
computation for a trivial action computes those of `ℤ`, and the product formula assembles the
answers: the Herbrand quotient of the whole lattice is the product over the orbits of the order of
the stabiliser.

The lattice is presented here in the form the two computations produce, indexed by the orbits and
with the orbit of length `d` carrying the coordinates `ZMod d`; a lattice met elsewhere is compared
to this model by an equivariant isomorphism, which does not change the Herbrand quotient.

## Main definitions

* `InverseGalois.CFT.permAut`: the cyclic shift of a family of blocks of coordinates.

## Main results

* `InverseGalois.CFT.permAut_pow_eq_one`: the shift has order dividing the common multiple of the
  block lengths.
* `InverseGalois.CFT.herbrand_permAut`: **the Herbrand quotient of a permutation lattice is the
  product over the orbits of the order of the stabiliser.**

## Tags

Tate cohomology, Herbrand quotient, permutation module, Shapiro's lemma
-/

namespace InverseGalois.CFT

variable {ι : Type*}

/-! ### The shift of a family of blocks -/

/-- **The permutation lattice of a family of orbits**, shifted cyclically inside each block. -/
def permAut (d : ι → ℕ) : (∀ i, ZMod (d i) → ℤ) ≃+ (∀ i, ZMod (d i) → ℤ) :=
  piAut fun i => indAut (1 : ℤ ≃+ ℤ) (d i)

/-- The shift moves each coordinate to the next one in its block. -/
theorem permAut_apply (d : ι → ℕ) (x : ∀ i, ZMod (d i) → ℤ) (i : ι) (j : ZMod (d i)) :
    permAut d x i j = x i (j + 1) := by
  show indTwist (1 : ℤ ≃+ ℤ) j (x i (j + 1)) = x i (j + 1)
  have h : indTwist (1 : ℤ ≃+ ℤ) j = 1 := by simp only [indTwist, ite_self]
  rw [h]
  rfl

/-- **The shift has order dividing the common multiple of the block lengths.** -/
theorem permAut_pow_eq_one {d m : ι → ℕ} [∀ i, NeZero (d i)] {n : ℕ}
    (hn : ∀ i, d i * m i = n) : (permAut d) ^ n = 1 :=
  piAut_pow_eq_one fun i => by
    rw [← hn i]
    exact indAut_pow_eq_one (1 : ℤ ≃+ ℤ) (one_pow (m i))

/-! ### The Herbrand quotient -/

/-- **The Herbrand quotient of a permutation lattice is the product over the orbits of the order of
the stabiliser.**  An orbit of length `d` inside a cyclic group of order `n = d * m` has a
stabiliser of order `m`, and it contributes exactly that factor. -/
theorem herbrand_permAut [Fintype ι] {d m : ι → ℕ} [∀ i, NeZero (d i)] {n : ℕ}
    (hn : ∀ i, d i * m i = n) (hm : ∀ i, m i ≠ 0) :
    herbrand (permAut d) n = ∏ i, (m i : ℚ) := by
  have hsplit : herbrand (permAut d) n = ∏ i, herbrand (indAut (1 : ℤ ≃+ ℤ) (d i)) n :=
    herbrand_piAut _ n
  rw [hsplit]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hn i, herbrand_indAut (1 : ℤ ≃+ ℤ) (m i) (one_pow (m i)), herbrand_int (m i) (hm i)]

end InverseGalois.CFT
