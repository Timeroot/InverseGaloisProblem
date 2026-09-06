/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleClassTorsionSubgroup
import InverseGalois.CFT.Units.NsmulTorsionRep

/-!
# The idele classes killed by a prime, read locally over a subgroup

The elements killed by a prime of the units, of the ideles and of the idele classes stay short exact
after tensoring with any coefficients, and they stay short exact when read on a subgroup of the
Galois group.  Over a subgroup the middle term is again a product of local groups, but the product
is indexed by the orbits of the subgroup on the places of the extension rather than by the places of
the base field, and the factor at an orbit is the complete cohomology of the stabiliser there with
coefficients in the roots of unity of a completion tensored with the restricted coefficients.

Reading the long exact sequence at its third term therefore presents the complete cohomology of a
subgroup with coefficients in the idele classes killed by a prime by purely local data: **a class
comes from a family of local classes exactly when the connecting map kills it**, and every class
comes from such a family as soon as the roots of unity of the field carry no complete cohomology one
degree higher over the subgroup.

This is the description the obstruction to the theorem of Tate and Nakayama asks for.  That
obstruction lands in the complete cohomology of the vectors of the idele classes killed by the
prime, tensored with the coefficients, and the vectors killed by a number inside the representation
attached to an action are the elements killed by that number for the action; so the same
presentation reads the target of the obstruction over a subgroup, which is where the criterion for
the everywhere locally trivial classes of the units has to be checked.

## Main definitions

* `InverseGalois.CFT.localTorsionResFamily`: the families of local classes indexed by the orbits of
  a subgroup on the places of the extension.
* `InverseGalois.CFT.ideleClassTorsionNsmulResEquiv`: the target of the obstruction to the theorem
  of Tate and Nakayama over a subgroup is the complete cohomology of the idele classes killed by the
  prime, tensored with the restricted coefficients.

## Main results

* `InverseGalois.CFT.ker_tateδ_tensor_ideleClassTorsionRes`: the classes of the idele classes killed
  by a prime, tensored with the coefficients and read on a subgroup, which the connecting map kills
  are exactly those coming from the ideles killed by the prime.
* `InverseGalois.CFT.exists_localTorsionRes_tateMap_eq`: **a class killed by the connecting map is
  the image of a family of local classes**, one for each orbit of the subgroup on the places of the
  extension.
* `InverseGalois.CFT.exists_localTorsionRes_tateMap_eq_of_isZero`: **every class is the image of
  such a family** as soon as the roots of unity of the field, tensored with the coefficients, carry
  no complete cohomology over the subgroup one degree higher.
* `InverseGalois.CFT.exists_localTorsionRes_tateMap_eq_nsmul`: **every class of the target of the
  obstruction to the theorem of Tate and Nakayama over a subgroup is the image of a family of local
  classes** under the same conditions.

## Tags

number field, idele class group, root of unity, decomposition group, Sylow subgroup, Tate
cohomology, tensor product
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

noncomputable section

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] [Finite Gal(K/k)]
  {p : ℕ} (hp : p.Prime) (W : Rep ℤ Gal(K/k)) (S : Subgroup Gal(K/k))

/-! ### The exactness over a subgroup -/

/-- The classes of the idele classes killed by a prime, tensored with the coefficients and read on a
subgroup of the Galois group, which the connecting map kills are exactly those coming from the
ideles killed by the prime. -/
theorem ker_tateδ_tensor_ideleClassTorsionRes (n : ℤ) :
    LinearMap.ker (tateδ (resSeq_tensorSeq_ideleClassTorsion_shortExact hp W S) n).hom
      = LinearMap.range (tateMap
        (resHom S (tensorHomLeft W (ideleToIdeleClassTorsion k K (p : ℤ)))) n).hom := by
  ext x
  simpa only [LinearMap.mem_ker, LinearMap.mem_range, Set.mem_range] using
    tateExact_map_δ (resSeq_tensorSeq_ideleClassTorsion_shortExact hp W S) n x

/-! ### The local data -/

section Local

variable (w₀ : ∀ ω : orbitRel.Quotient ↥S (InfinitePlace K), ω.orbit)
  (v₀ : ∀ ω : orbitRel.Quotient ↥S (HeightOneSpectrum (𝓞 K)), ω.orbit)

/-- **The families of local classes indexed by the orbits of a subgroup of the Galois group on the
places of the extension**: at an orbit, the complete cohomology of the stabiliser of a chosen place
there with coefficients in the roots of unity of the completion tensored with the restricted
coefficients. -/
abbrev localTorsionResFamily (n : ℤ) : Type :=
  (∀ ω : orbitRel.Quotient ↥S (InfinitePlace K),
      tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
        (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)).comp
          (stabilizerSubgroupHom S ((w₀ ω : ω.orbit) : InfinitePlace K))) (p : ℤ))
        (resObj (stabilizer ↥S ((w₀ ω : ω.orbit) : InfinitePlace K)) (resObj S W))) n) ×
    (∀ ω : orbitRel.Quotient ↥S (HeightOneSpectrum (𝓞 K)),
      tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)).comp
          (stabilizerSubgroupHom S ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))) (p : ℤ))
        (resObj (stabilizer ↥S ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))
          (resObj S W))) n)

variable {d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))

/-- **A class of the idele classes killed by a prime, tensored with coefficients of finite rank over
the field with that many elements and read on a subgroup of the Galois group, which the connecting
map kills is the image of a family of local classes.**  There is one member of the family for each
orbit of the subgroup on the places of the extension. -/
theorem exists_localTorsionRes_tateMap_eq (n : ℤ)
    (x : tateModule (resObj S (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W)) n)
    (hx : tateδ (resSeq_tensorSeq_ideleClassTorsion_shortExact hp W S) n x = 0) :
    ∃ y : localTorsionResFamily (p := p) W S w₀ v₀ n,
      tateMap (resHom S (tensorHomLeft W (ideleToIdeleClassTorsion k K (p : ℤ)))) n
        ((ideleTorsionTensorTateResEquiv S W e w₀ v₀ n).symm y) = x := by
  obtain ⟨z, hz⟩ := (tateExact_map_δ
    (resSeq_tensorSeq_ideleClassTorsion_shortExact hp W S) n x).1 hx
  refine ⟨ideleTorsionTensorTateResEquiv S W e w₀ v₀ n z, ?_⟩
  rw [AddEquiv.symm_apply_apply]
  exact hz

include hp in
/-- **Every class of the idele classes killed by a prime, tensored with coefficients of finite rank
over the field with that many elements and read on a subgroup of the Galois group, is the image of a
family of local classes** as soon as the roots of unity of the field, tensored with the
coefficients, carry no complete cohomology over the subgroup one degree higher. -/
theorem exists_localTorsionRes_tateMap_eq_of_isZero (n : ℤ)
    (h : Limits.IsZero (tateModule (resObj S
      (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W)) (n + 1)))
    (x : tateModule (resObj S (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W)) n) :
    ∃ y : localTorsionResFamily (p := p) W S w₀ v₀ n,
      tateMap (resHom S (tensorHomLeft W (ideleToIdeleClassTorsion k K (p : ℤ)))) n
        ((ideleTorsionTensorTateResEquiv S W e w₀ v₀ n).symm y) = x :=
  exists_localTorsionRes_tateMap_eq hp W S w₀ v₀ e n x (eq_zero_of_isZero h _)

end Local

/-! ### The target of the obstruction -/

/-- **The target of the obstruction to the theorem of Tate and Nakayama for the idele class group
over a subgroup of the Galois group is the complete cohomology of the idele classes killed by the
prime, tensored with the restricted coefficients**: the vectors killed by a number inside the
representation attached to an action are the elements killed by that number for the action. -/
def ideleClassTorsionNsmulResEquiv (n : ℤ) :
    ↥(tateModule (tensorObj (nsmulTorsion (resObj S (ideleClassRep k K)) p) (resObj S W)) n)
      ≃ₗ[ℤ] ↥(tateModule (resObj S
        (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W)) n) :=
  tateTensorNsmulTorsionRepEquiv ((ideleClassAutHom k K).comp S.subtype) p (resObj S W) n

section Local

variable (w₀ : ∀ ω : orbitRel.Quotient ↥S (InfinitePlace K), ω.orbit)
  (v₀ : ∀ ω : orbitRel.Quotient ↥S (HeightOneSpectrum (𝓞 K)), ω.orbit)
  {d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))

include hp in
/-- **Every class of the target of the obstruction to the theorem of Tate and Nakayama over a
subgroup of the Galois group is, read in the idele classes killed by the prime, the image of a
family of local classes** as soon as the roots of unity of the field, tensored with the
coefficients, carry no complete cohomology over the subgroup one degree higher. -/
theorem exists_localTorsionRes_tateMap_eq_nsmul (n : ℤ)
    (h : Limits.IsZero (tateModule (resObj S
      (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W)) (n + 1)))
    (x : tateModule (tensorObj (nsmulTorsion (resObj S (ideleClassRep k K)) p) (resObj S W)) n) :
    ∃ y : localTorsionResFamily (p := p) W S w₀ v₀ n,
      tateMap (resHom S (tensorHomLeft W (ideleToIdeleClassTorsion k K (p : ℤ)))) n
          ((ideleTorsionTensorTateResEquiv S W e w₀ v₀ n).symm y)
        = ideleClassTorsionNsmulResEquiv W S n x :=
  exists_localTorsionRes_tateMap_eq_of_isZero hp W S w₀ v₀ e n h _

end Local

end

end InverseGalois.CFT
