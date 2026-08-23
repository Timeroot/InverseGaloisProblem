/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Congr
import InverseGalois.CFT.Tate.Pi
import InverseGalois.CFT.Tate.Prod

/-!
# A product of modules split by a predicate on the index

The group of ideles of a number field is a product over all of the places, of which only the finitely
many in a chosen finite set contribute to the Herbrand quotient: at every other place the factor is
the group of units of a valuation ring on which the decomposition group acts without cohomology.  To
read the Herbrand quotient off as a finite product one therefore has to split a product indexed by an
infinite set into the part named by a predicate and the rest, and discard the rest.

That is what is done here.  A predicate on the index set splits a product of modules into the product
over the indices satisfying it and the product over those that do not, compatibly with an
automorphism acting coordinatewise; when only finitely many indices satisfy the predicate and the
factors at the others have vanishing Tate groups, the Herbrand quotient of the whole product is the
finite product of the Herbrand quotients of the named factors.

## Main definitions

* `InverseGalois.CFT.piSplitEquiv`: **a predicate on the index set splits a product of modules into
  two products.**

## Main results

* `InverseGalois.CFT.piSplitEquiv_piAut`: the splitting is compatible with a coordinatewise
  automorphism.
* `InverseGalois.CFT.herbrand_piAut_split`: **the Herbrand quotient of a product of modules is the
  product over the finitely many named indices**, as soon as the factors at the other indices have
  vanishing Tate groups.

## Tags

Tate cohomology, Herbrand quotient, product, idele
-/

namespace InverseGalois.CFT

variable {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] (p : ι → Prop) [DecidablePred p]

/-! ### The splitting -/

/-- **A predicate on the index set splits a product of modules into two products**: the one over the
indices satisfying it and the one over those that do not. -/
def piSplitEquiv :
    (∀ i, M i) ≃+ ((∀ i : {i // p i}, M i) × (∀ i : {i // ¬ p i}, M i)) where
  toFun f := (fun i => f i, fun i => f i)
  invFun z i := if h : p i then z.1 ⟨i, h⟩ else z.2 ⟨i, h⟩
  left_inv f := by
    funext i
    by_cases h : p i <;> simp [h]
  right_inv z := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · exact dif_pos i.2
    · exact dif_neg i.2
  map_add' _ _ := rfl

@[simp]
theorem piSplitEquiv_apply (f : ∀ i, M i) :
    piSplitEquiv p f = (fun i : {i // p i} => f i, fun i : {i // ¬ p i} => f i) := rfl

/-- **The splitting is compatible with a coordinatewise automorphism.** -/
theorem piSplitEquiv_piAut (σ : ∀ i, M i ≃+ M i) (f : ∀ i, M i) :
    piSplitEquiv p (piAut σ f)
      = prodAut (piAut fun i : {i // p i} => σ i) (piAut fun i : {i // ¬ p i} => σ i)
          (piSplitEquiv (M := M) p f) := rfl

/-! ### The Herbrand quotient -/

variable (σ : ∀ i, M i ≃+ M i) (n : ℕ)

/-- **The Herbrand quotient of a product of modules is the product over the finitely many named
indices**, as soon as the factors at the other indices have vanishing Tate groups.  This is how the
places outside a finite set drop out of the Herbrand quotient of the group of ideles. -/
theorem herbrand_piAut_split [Fintype {i // p i}]
    (h0 : ∀ i : {i // ¬ p i}, Subsingleton (tateH0 (σ i) n))
    (hm1 : ∀ i : {i // ¬ p i}, Subsingleton (tateHm1 (σ i) n)) :
    herbrand (piAut σ) n = ∏ i : {i // p i}, herbrand (σ i) n := by
  rw [herbrand_congr (piSplitEquiv (M := M) p) (piSplitEquiv_piAut p σ) n, herbrand_prodAut,
    herbrand_piAut (fun i : {i // p i} => σ i) n,
    herbrand_piAut_eq_one (fun i : {i // ¬ p i} => σ i) n h0 hm1, mul_one]

end InverseGalois.CFT
