/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.LocalPowIdele

/-!
# The ideles that are local powers at the auxiliary places and units outside

The algebraic proof of the second inequality of class field theory needs, besides the finite set `S`
of places carrying the ideal classes and the ramification, a second finite set `T` of auxiliary
places disjoint from `S`.  The subgroup of the ideles it produces is unconstrained at the infinite
places and at the places of `S`, is an `n`-th power at the places of `T`, and is a unit of the
valuation ring everywhere else.

Each of the three conditions is there for a reason.  Nothing is asked at `S` because the extension
to be killed splits completely there, so every local element is a norm; at the places of `T` the
local degree divides `n`, so an `n`-th power is a norm; and outside the two sets the extension is
unramified, so a unit is a norm.  In the other direction the subgroup has to be large enough that
together with the principal ideles it is everything, and that is what the two sets are chosen for:
`S` lets an idele be corrected by a principal one into a unit outside `S`, and the surjectivity onto
the local unit quotients at `T` lets it be corrected further by an `S`-unit.

## Main definitions

* `InverseGalois.CFT.splitPowIdele`: **the ideles that are `n`-th powers at the auxiliary places and
  units of the valuation ring outside the two sets of places.**

## Tags

number field, idele, power, unit, place, second inequality
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

section SplitPowIdele

variable (k : Type*) [Field k] [NumberField k]

/-- **The ideles that are `n`-th powers at the auxiliary places and units of the valuation ring
outside the two sets of places.**  No condition is imposed at the infinite places, nor at the places
of the first set. -/
def splitPowIdele (S T : Set (HeightOneSpectrum (𝓞 k))) (n : ℕ) : AddSubgroup ↥(idele k) where
  carrier := {x | (∀ v ∈ T, (x : FullIdele k).2 v ∈ nsmulSubgroup _ n) ∧
    ∀ v : HeightOneSpectrum (𝓞 k), v ∉ S → v ∉ T → unitVal ((x : FullIdele k).2 v) = 0}
  add_mem' hx hy :=
    ⟨fun v hv => add_mem (hx.1 v hv) (hy.1 v hv), fun v hvS hvT => by
      show unitVal (_ + _) = 0
      rw [map_add, hx.2 v hvS hvT, hy.2 v hvS hvT, add_zero]⟩
  zero_mem' := ⟨fun _ _ => zero_mem _, fun _ _ _ => map_zero _⟩
  neg_mem' hx :=
    ⟨fun v hv => neg_mem (hx.1 v hv), fun v hvS hvT => by
      show unitVal (-_) = 0
      rw [map_neg, hx.2 v hvS hvT, neg_zero]⟩

variable {k}

theorem mem_splitPowIdele {S T : Set (HeightOneSpectrum (𝓞 k))} {n : ℕ} {x : ↥(idele k)} :
    x ∈ splitPowIdele k S T n ↔ (∀ v ∈ T, (x : FullIdele k).2 v ∈ nsmulSubgroup _ n) ∧
      ∀ v : HeightOneSpectrum (𝓞 k), v ∉ S → v ∉ T →
        unitVal ((x : FullIdele k).2 v) = 0 := Iff.rfl

end SplitPowIdele

end InverseGalois.CFT
