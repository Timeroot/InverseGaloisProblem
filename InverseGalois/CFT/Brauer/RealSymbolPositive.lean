/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.RealSymbol

/-!
# The archimedean symbols of a unit positive at every real embedding

The symbol at an infinite place is trivial at a complex place, and at a real place it is trivial as
soon as its second argument is positive there.  So a unit which every real embedding of the field
sends to a positive number contributes nothing to the archimedean half of the product formula, no
matter what the first argument is.  The symbol of a pair of real units is symmetric, and at a
complex place there is nothing to say, so the symbol at an infinite place is symmetric and the two
arguments may be exchanged.

Positivity under every real embedding is stated as a condition on ring homomorphisms to the reals
rather than on places, and in that form it is visibly carried along the Galois group: composing a
real embedding with an automorphism is again a real embedding.

## Main results

* `InverseGalois.CFT.archSymbol_eq_one_of_forall_pos`: the symbol at an infinite place is trivial
  when its second argument is positive under every real embedding.
* `InverseGalois.CFT.prod_archSymbol_eq_one_of_forall_pos`: **the archimedean half of the product
  formula is trivial for a second argument positive under every real embedding.**
* `InverseGalois.CFT.archSymbol_comm`: the symbol at an infinite place is symmetric.
* `InverseGalois.CFT.prod_archSymbol_eq_one_of_forall_pos_left`: **the same for a first argument
  positive under every real embedding.**
* `InverseGalois.CFT.forall_pos_map`: **positivity under every real embedding is preserved by the
  Galois group.**

## Tags

real place, symbol, totally positive, product formula, class field theory
-/

namespace InverseGalois.CFT

open NumberField

section Positive

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
/-- The symbol at an infinite place is trivial when its second argument is positive under every
real embedding.  At a complex place the symbol is trivial outright, and at a real place the second
argument is a positive real. -/
theorem archSymbol_eq_one_of_forall_pos (u : InfinitePlace K) (a b : Kˣ)
    (hb : ∀ φ : K →+* ℝ, 0 < φ (b : K)) : archSymbol K u a b = 1 := by
  rcases u.isReal_or_isComplex with hu | hu
  · rw [archSymbol_of_isReal K hu]
    refine realSymbol_of_pos_right _ ?_
    rw [Units.coe_map]
    exact hb (InfinitePlace.embedding_of_isReal hu)
  · rw [archSymbol_of_isComplex K hu]

/-- **The archimedean half of the product formula is trivial for a second argument positive under
every real embedding.** -/
theorem prod_archSymbol_eq_one_of_forall_pos (a b : Kˣ) (hb : ∀ φ : K →+* ℝ, 0 < φ (b : K)) :
    ∏ u : InfinitePlace K, archSymbol K u a b = 1 :=
  Finset.prod_eq_one fun u _ => archSymbol_eq_one_of_forall_pos u a b hb

omit [NumberField K] in
/-- **The symbol at an infinite place is symmetric**: at a real place it is the symbol of a pair of
real units, which is symmetric, and at a complex place it is trivial either way round. -/
theorem archSymbol_comm (u : InfinitePlace K) (a b : Kˣ) :
    archSymbol K u a b = archSymbol K u b a := by
  rcases u.isReal_or_isComplex with hu | hu
  · rw [archSymbol_of_isReal K hu, archSymbol_of_isReal K hu, realSymbol_comm]
  · rw [archSymbol_of_isComplex K hu, archSymbol_of_isComplex K hu]

omit [NumberField K] in
/-- The symbol at an infinite place is trivial when its **first** argument is positive under every
real embedding, the symbol being symmetric. -/
theorem archSymbol_eq_one_of_forall_pos_left (u : InfinitePlace K) {a : Kˣ}
    (ha : ∀ φ : K →+* ℝ, 0 < φ (a : K)) (b : Kˣ) : archSymbol K u a b = 1 :=
  (archSymbol_comm u a b).trans (archSymbol_eq_one_of_forall_pos u b a ha)

/-- **The archimedean half of the product formula is trivial for a first argument positive under
every real embedding.** -/
theorem prod_archSymbol_eq_one_of_forall_pos_left {a : Kˣ}
    (ha : ∀ φ : K →+* ℝ, 0 < φ (a : K)) (b : Kˣ) :
    ∏ u : InfinitePlace K, archSymbol K u a b = 1 :=
  Finset.prod_eq_one fun u _ => archSymbol_eq_one_of_forall_pos_left u ha b

end Positive

section Galois

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- **Positivity under every real embedding is preserved by the Galois group**: a real embedding
composed with an automorphism is again a real embedding. -/
theorem forall_pos_map (σ : Gal(K/k)) {x : K} (hx : ∀ φ : K →+* ℝ, 0 < φ x) (φ : K →+* ℝ) :
    0 < φ (σ x) :=
  hx (φ.comp (σ : K →+* K))

end Galois

end InverseGalois.CFT
