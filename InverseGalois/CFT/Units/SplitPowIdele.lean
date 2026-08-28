/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.LocalPowIdele
import InverseGalois.CFT.Units.SUnit

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

## Main results

* `InverseGalois.CFT.ideleDiag_range_sup_splitPowIdele_eq_top`: **the principal ideles together with
  those ideles are all the ideles.**

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

/-- **The principal ideles together with the ideles that are local `n`-th powers at the auxiliary
places and units outside the two sets of places are all the ideles.**  The first set carrying the
ideal classes lets one correct a given idele by a principal idele into one that is a unit of the
valuation ring outside that set; the `S`-units surjecting onto the local units modulo `n`-th powers
at the auxiliary places lets one correct it further, by a principal idele which changes nothing
outside the first set, into one that is an `n`-th power there. -/
theorem ideleDiag_range_sup_splitPowIdele_eq_top {S T : Set (HeightOneSpectrum (𝓞 k))}
    (hTS : ∀ v ∈ T, v ∉ S) {n : ℕ}
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 k) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 k) in Filter.cofinite, m v = 0) →
      ∃ a : kˣ, ∀ v ∉ S, ord k v (a : k) = m v)
    (hsurj : ∀ c : (v : HeightOneSpectrum (𝓞 k)) → (v.adicCompletion k)ˣ,
      (∀ v ∈ T, Valued.v ((c v : v.adicCompletion k)) = 1) →
      ∃ u : kˣ, u ∈ sUnits k S ∧ ∀ v ∈ T, ∃ z : (v.adicCompletion k)ˣ,
        adicUnitHom v u = c v * z ^ n) :
    (ideleDiag k).range ⊔ splitPowIdele k S T n = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨a, ha⟩ := hrepr (fun v => -unitVal ((x : FullIdele k).2 v)) (by
    filter_upwards [(mem_idele k).mp x.2] with v hv
    rw [hv, neg_zero])
  set y : ↥(idele k) := x - ideleDiag k (Additive.ofMul a) with hydef
  have hyval : ∀ v ∉ S, unitVal ((y : FullIdele k).2 v) = 0 := by
    intro v hv
    show unitVal ((x : FullIdele k).2 v - (fullDiag k (Additive.ofMul a)).2 v) = 0
    rw [map_sub, fullDiag_snd, unitVal_adicUnitHom]
    show unitVal ((x : FullIdele k).2 v) - -ord k v (a : k) = 0
    rw [ha v hv]
    ring
  obtain ⟨u, hu, hz⟩ := hsurj (fun v => Additive.toMul ((y : FullIdele k).2 v)) fun v hv =>
    mem_ker_unitVal.mp (AddMonoidHom.mem_ker.mpr (hyval v (hTS v hv)))
  refine AddSubgroup.mem_sup.mpr ⟨ideleDiag k (Additive.ofMul a) + ideleDiag k (Additive.ofMul u),
    ⟨Additive.ofMul a + Additive.ofMul u, map_add _ _ _⟩,
    y - ideleDiag k (Additive.ofMul u), ⟨fun v hv => ?_, fun v hvS hvT => ?_⟩, by
      rw [hydef]; abel⟩
  · obtain ⟨z, hzv⟩ := hz v hv
    refine ⟨Additive.ofMul z⁻¹, ?_⟩
    show Additive.ofMul (Additive.toMul ((y : FullIdele k).2 v))
        - Additive.ofMul (adicUnitHom v u) = n • Additive.ofMul z⁻¹
    rw [hzv, ofMul_mul, ofMul_pow, ofMul_inv]
    abel
  · show unitVal ((y : FullIdele k).2 v - (fullDiag k (Additive.ofMul u)).2 v) = 0
    rw [map_sub, fullDiag_snd, unitVal_adicUnitHom]
    show unitVal ((y : FullIdele k).2 v) - -ord k v (u : k) = 0
    rw [hyval v hvS, mem_sUnits.mp hu v hvS]
    ring

end SplitPowIdele

end InverseGalois.CFT
