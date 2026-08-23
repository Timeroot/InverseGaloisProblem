/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicAction
import InverseGalois.CFT.Local.UnitValuation
import InverseGalois.CFT.Tate.FamilyRing

/-!
# The Galois action on the family of completions at the finite places

A Galois automorphism of a number field carries the completion at a prime isomorphically onto the
completion at the image prime.  Doing this for every prime at once, and checking that the identity
acts trivially and that a product acts as the composite, presents the completions as a family of
rings carrying an action of the Galois group in the sense of
`InverseGalois.CFT.RingFamilyAction`; the group then acts on the sections of the family, and on the
sections of the family of unit groups.  These are the finite components of the group of ideles.

The compatibility of the transports is checked on the image of the field, which is dense in each
completion: an element of the field determines a section of the family, so both sides of each of
the two identities send it to the same value, and the identities extend to the completions by
continuity.

## Main definitions

* `InverseGalois.CFT.adicCoe`: the section of the family of completions determined by an element of
  the field.
* `InverseGalois.CFT.adicRingFamily`: **the Galois action on the family of completions at the
  finite places.**

## Main results

* `InverseGalois.CFT.adicCompletionGalEquiv_adicCoe`: the transport carries the section determined
  by an element of the field to the section determined by its image.
* `InverseGalois.CFT.transport_adicUnitsFamily`: **the transport of the unit group of a completion
  by an automorphism fixing the place is the action of the decomposition group.**

## Tags

class field theory, idele, completion, Galois action, family of rings
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section AdicFamily

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]

/-- **The section of the family of completions determined by an element of the field**: at each
prime, the image of the element in the completion there. -/
def adicCoe (y : K) (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K :=
  (((WithVal.equiv (v.valuation K)).symm y : WithVal (v.valuation K)) : v.adicCompletion K)

theorem ringCast_adicCoe {v w : HeightOneSpectrum (𝓞 K)} (h : v = w) (y : K) :
    ringCast (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K) h (adicCoe y v)
      = adicCoe y w :=
  ringCast_apply_section _ h (adicCoe y)

/-- **The transport carries the section determined by an element of the field to the section
determined by its image.** -/
@[simp]
theorem adicCompletionGalEquiv_adicCoe (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/k)) (y : K) :
    adicCompletionGalEquiv v σ (adicCoe y v) = adicCoe (σ y) (σ • v) := by
  rw [adicCoe, adicCompletionGalEquiv_coe]
  rfl

/-- **The Galois group acts on the family of completions of a number field at its finite
places.** -/
noncomputable def adicRingFamily :
    RingFamilyAction (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) Gal(K/k) where
  map σ v := adicCompletionGalEquiv v σ
  map_one v z := by
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (continuous_adicCompletionGalEquiv v 1)
        (continuous_ringCast _ (one_smul Gal(K/k) v).symm)) fun x => ?_
    show adicCompletionGalEquiv v 1 (adicCoe (WithVal.equiv (v.valuation K) x) v)
      = ringCast _ _ (adicCoe (WithVal.equiv (v.valuation K) x) v)
    rw [adicCompletionGalEquiv_adicCoe, ringCast_adicCoe]
    rfl
  map_mul σ τ v z := by
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (continuous_adicCompletionGalEquiv v (σ * τ))
        (((continuous_ringCast _ (mul_smul σ τ v).symm).comp
          (continuous_adicCompletionGalEquiv (τ • v) σ)).comp
          (continuous_adicCompletionGalEquiv v τ))) fun x => ?_
    show adicCompletionGalEquiv v (σ * τ) (adicCoe (WithVal.equiv (v.valuation K) x) v)
      = ringCast _ _ (adicCompletionGalEquiv (τ • v) σ
          (adicCompletionGalEquiv v τ (adicCoe (WithVal.equiv (v.valuation K) x) v)))
    rw [adicCompletionGalEquiv_adicCoe, adicCompletionGalEquiv_adicCoe,
      adicCompletionGalEquiv_adicCoe, ringCast_adicCoe]
    rfl

@[simp]
theorem adicRingFamily_map (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) :
    (adicRingFamily (k := k) (K := K)).map σ v = adicCompletionGalEquiv v σ := rfl

/-! ### The transport by an automorphism fixing the place -/

/-- **A Galois automorphism fixing a place transports the completion there by the action of the
decomposition group.** -/
theorem ringCast_adicCompletionGalEquiv (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/k))
    (hσ : σ • v = v) (z : v.adicCompletion K) :
    ringCast (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K) hσ
        (adicCompletionGalEquiv v σ z)
      = adicCompletionAut v σ hσ z := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq ((continuous_ringCast _ hσ).comp (continuous_adicCompletionGalEquiv v σ))
      (continuous_adicCompletionAut v σ hσ)) fun x => ?_
  show ringCast _ hσ (adicCompletionGalEquiv v σ (adicCoe (WithVal.equiv (v.valuation K) x) v))
    = adicCompletionAut v σ hσ (adicCoe (WithVal.equiv (v.valuation K) x) v)
  rw [adicCompletionGalEquiv_adicCoe, ringCast_adicCoe]
  simp only [adicCoe]
  rw [adicCompletionAut_coe]
  rfl

/-- **The transport of the unit group of a completion by a Galois automorphism fixing the place is
the action of the decomposition group.** -/
theorem transport_adicUnitsFamily (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/k)) (hσ : σ • v = v)
    (a : Additive (v.adicCompletion K)ˣ) :
    (adicRingFamily (k := k) (K := K)).unitsFamily.transport hσ a
      = smulUnitsAut (G := ↥(stabilizer Gal(K/k) v)) (R := v.adicCompletion K)
          ⟨σ, mem_stabilizer_iff.mpr hσ⟩ a := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [FamilyAction.transport_apply, famCast_units, coe_smulUnitsAut_apply,
    stabilizer_smul_adicCompletion_def]
  exact ringCast_adicCompletionGalEquiv v σ hσ _

end AdicFamily

end InverseGalois.CFT
