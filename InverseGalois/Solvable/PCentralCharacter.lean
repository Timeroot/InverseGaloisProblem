/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.PCentralCoord
import InverseGalois.Solvable.PCentralFrattini

/-!
# The coordinate character of a free object of positive `p`-class

A free object of rank `d` and `p`-class at least one has a canonical character with values in the
elementary abelian group of rank `d`: divide by the first term of the lower `p`-central series,
which returns the free object of `p`-class one, and read off the coordinates there.  The character
sends the `i`-th distinguished generator to the `i`-th standard basis vector, and that property
pins it down, because the distinguished generators generate.

Its kernel is exactly the first term of the lower `p`-central series, which for a finite `p`-group
sits inside the Frattini subgroup.  So a character of the free object matching the generators has
its kernel inside the Frattini subgroup, and is onto.  That is the form in which the character is
used: a family of square roots whose sign characters match the generators of the Galois group both
spans and separates, the second because the sign characters have small kernel.

## Main definitions

* `InverseGalois.FreePClass.coordClass`: the coordinate character of a free object of positive
  `p`-class.

## Main results

* `InverseGalois.FreePClass.ker_coordClass`: the kernel of the coordinate character is the first
  term of the lower `p`-central series.
* `InverseGalois.FreePClass.eq_coordClass`: **a character matching the distinguished generators is
  the coordinate character.**
* `InverseGalois.FreePClass.surjective_of_apply_gen`,
  `InverseGalois.FreePClass.ker_le_frattini_of_apply_gen`: **a character matching the distinguished
  generators is onto and has its kernel inside the Frattini subgroup.**

## Tags

free `p`-group, `p`-class, elementary abelian, Frattini subgroup, character
-/

namespace InverseGalois

namespace FreePClass

open Multiplicative

variable (p d : ℕ) [NeZero p] {c : ℕ}

/-! ### The coordinate character -/

/-- The coordinate character of the free object of rank `d` and `p`-class at least one: divide by
the first term of the lower `p`-central series and read off the coordinates of the resulting free
object of `p`-class one. -/
noncomputable def coordClass (hc : 1 ≤ c) : FreePClass p d c →* Multiplicative (Fin d → ZMod p) :=
  (coordEquiv p d).toMonoidHom.comp
    ((quotientEquiv p d hc).toMonoidHom.comp
      (QuotientGroup.mk' (lowerPCentralSeries p (FreePClass p d c) 1)))

@[simp] theorem coordClass_gen (hc : 1 ≤ c) (i : Fin d) :
    coordClass p d hc (gen p d c i) = ofAdd (Pi.single i 1) := by
  have hq : quotientEquiv p d hc
      (QuotientGroup.mk' (lowerPCentralSeries p (FreePClass p d c) 1) (gen p d c i))
      = gen p d 1 i := rfl
  show coord p d (quotientEquiv p d hc
      (QuotientGroup.mk' (lowerPCentralSeries p (FreePClass p d c) 1) (gen p d c i)))
      = ofAdd (Pi.single i 1)
  rw [hq, coord_gen]

theorem surjective_coordClass (hc : 1 ≤ c) : Function.Surjective (coordClass p d hc) :=
  (coordEquiv p d).surjective.comp
    ((quotientEquiv p d hc).surjective.comp (QuotientGroup.mk'_surjective _))

/-- **The kernel of the coordinate character is the first term of the lower `p`-central series.** -/
theorem ker_coordClass (hc : 1 ≤ c) :
    (coordClass p d hc).ker = lowerPCentralSeries p (FreePClass p d c) 1 := by
  ext x
  simp only [coordClass, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]

/-! ### Characters matching the generators -/

variable {p d}

/-- **A character of the free object matching the distinguished generators is the coordinate
character.**  Two homomorphisms agreeing on a generating set agree. -/
theorem eq_coordClass (hc : 1 ≤ c) {χ : FreePClass p d c →* Multiplicative (Fin d → ZMod p)}
    (hχ : ∀ i, χ (gen p d c i) = ofAdd (Pi.single i 1)) : χ = coordClass p d hc := by
  refine MonoidHom.eq_of_eqOn_dense (closure_range_gen p d c) ?_
  rintro _ ⟨i, rfl⟩
  rw [hχ i, coordClass_gen]

/-- **A character of the free object matching the distinguished generators is onto.** -/
theorem surjective_of_apply_gen (hc : 1 ≤ c)
    {χ : FreePClass p d c →* Multiplicative (Fin d → ZMod p)}
    (hχ : ∀ i, χ (gen p d c i) = ofAdd (Pi.single i 1)) : Function.Surjective χ := by
  rw [eq_coordClass hc hχ]
  exact surjective_coordClass p d hc

/-- **The kernel of a character of the free object matching the distinguished generators lies
inside the Frattini subgroup.**  The kernel is the first term of the lower `p`-central series, and
in a finite `p`-group every maximal subgroup contains it. -/
theorem ker_le_frattini_of_apply_gen [Fact p.Prime] (hc : 1 ≤ c)
    {χ : FreePClass p d c →* Multiplicative (Fin d → ZMod p)}
    (hχ : ∀ i, χ (gen p d c i) = ofAdd (Pi.single i 1)) :
    χ.ker ≤ frattini (FreePClass p d c) := by
  rw [eq_coordClass hc hχ, ker_coordClass]
  exact lowerPCentralSeries_one_le_frattini (isPGroup p d c)

end FreePClass

end InverseGalois
