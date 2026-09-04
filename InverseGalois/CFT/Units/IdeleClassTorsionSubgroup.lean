/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.RestrictNatural
import InverseGalois.CFT.Units.IdeleTensorSha
import InverseGalois.CFT.Units.IdeleTorsionSubgroup

/-!
# The idele classes killed by a prime, read on a subgroup of the Galois group

The roots of unity of a number field, the elements of its ideles killed by a prime and the elements
of its idele classes killed by that prime form a short exact sequence of representations of the
Galois group, and tensoring with any coefficients keeps it exact.  A short exact sequence of
representations of a group stays short exact when read on a subgroup, because injectivity,
surjectivity and exactness in the middle are statements about the underlying modules and the
underlying modules do not change.  So the same three terms, tensored and read on a subgroup, still
give a long exact sequence of complete cohomology of that subgroup.

**Combined with the description of the middle term over a subgroup**, this makes the complete
cohomology of a subgroup with coefficients in the idele classes killed by a prime accessible from
purely local data: the middle term is the product over the orbits of the subgroup on the places of
the extension of the complete cohomology of the stabiliser there with coefficients in the roots of
unity of the completion, and the outer term is the roots of unity of the field.  In particular the
idele classes killed by the prime have no complete cohomology over the subgroup in a degree in which
no local factor has any and the roots of unity of the field have none one degree higher.

## Main results

* `InverseGalois.CFT.resSeq_tensorSeq_ideleClassTorsion_shortExact`: **the roots of unity, the
  ideles killed by a prime and the idele classes killed by that prime, tensored with any
  coefficients, stay short exact when read on a subgroup of the Galois group.**
* `InverseGalois.CFT.range_tateδ_tensor_ideleClassTorsionRes`: **the classes of the roots of unity
  tensored with the coefficients which die in the ideles are exactly the image of the connecting
  map** coming out of the idele classes killed by the prime, one degree lower, over the subgroup.
* `InverseGalois.CFT.isZero_tateModule_tensor_ideleClassTorsionRes`: the idele classes killed by the
  prime have no complete cohomology over the subgroup in a degree in which the ideles killed by the
  prime have none and the roots of unity of the field have none one degree higher.
* `InverseGalois.CFT.isZero_tateModule_tensor_ideleClassTorsionRes_of_local`: **the same, with the
  hypothesis on the ideles replaced by the vanishing of every local factor**, indexed by the orbits
  of the subgroup on the places of the extension.

## Tags

number field, idele class group, root of unity, subgroup, Sylow subgroup, Tate cohomology, short
exact sequence
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

noncomputable section

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] [Finite Gal(K/k)]
  {p : ℕ} (hp : p.Prime) (W : Rep ℤ Gal(K/k)) (S : Subgroup Gal(K/k))

/-! ### The sequence over a subgroup -/

omit [Finite Gal(K/k)] in
include hp in
/-- **The roots of unity of a number field, the elements of its ideles killed by a prime and the
elements of its idele classes killed by that prime, tensored with any coefficients, stay short exact
when read on a subgroup of the Galois group.**  Injectivity, surjectivity and exactness in the
middle are statements about the underlying modules, which a subgroup does not change. -/
theorem resSeq_tensorSeq_ideleClassTorsion_shortExact :
    (resSeq S (tensorSeq W (ideleClassTorsionShortComplex k K (p : ℤ)))).ShortExact :=
  resSeq_shortExact (tensorSeq_ideleClassTorsionShortComplex_shortExact hp W) S

include hp in
/-- The classes produced by the connecting map of the sequence of the elements killed by the prime,
read on a subgroup, die in the ideles. -/
theorem tateMap_tateδ_tensor_ideleClassTorsionRes_eq_zero (n : ℤ)
    (y : ↥(tateModule
      (resObj S (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W)) n)) :
    tateMap (resHom S (tensorHomLeft W (globalUnitsToIdeleTorsion k K (p : ℤ)))) (n + 1)
        (tateδ (resSeq_tensorSeq_ideleClassTorsion_shortExact hp W S) n y) = 0 :=
  (tateExact_δ_map (resSeq_tensorSeq_ideleClassTorsion_shortExact hp W S) n).apply_apply_eq_zero y

include hp in
/-- Every class of the roots of unity of the field tensored with the coefficients which dies in the
ideles comes, over a subgroup, from the complete cohomology of the idele classes killed by the
prime, tensored with the same coefficients, one degree lower. -/
theorem exists_tateδ_tensor_ideleClassTorsionRes_eq (n : ℤ)
    (x : ↥(tateModule (resObj S
      (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W)) (n + 1)))
    (hx : tateMap (resHom S (tensorHomLeft W (globalUnitsToIdeleTorsion k K (p : ℤ))))
      (n + 1) x = 0) :
    ∃ y : ↥(tateModule
      (resObj S (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W)) n),
      tateδ (resSeq_tensorSeq_ideleClassTorsion_shortExact hp W S) n y = x :=
  (tateExact_δ_map (resSeq_tensorSeq_ideleClassTorsion_shortExact hp W S) n x).1 hx

include hp in
/-- **The classes of the roots of unity of the field tensored with the coefficients which die in the
ideles are exactly the image of the connecting map**, over a subgroup of the Galois group, coming
out of the complete cohomology of the idele classes killed by the prime one degree lower. -/
theorem range_tateδ_tensor_ideleClassTorsionRes (n : ℤ) :
    LinearMap.range (tateδ (resSeq_tensorSeq_ideleClassTorsion_shortExact hp W S) n).hom
      = LinearMap.ker (tateMap
        (resHom S (tensorHomLeft W (globalUnitsToIdeleTorsion k K (p : ℤ)))) (n + 1)).hom := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  refine ⟨?_, exists_tateδ_tensor_ideleClassTorsionRes_eq hp W S n x⟩
  rintro ⟨y, rfl⟩
  exact tateMap_tateδ_tensor_ideleClassTorsionRes_eq_zero hp W S n y

include hp in
/-- **The idele classes killed by a prime, tensored with any coefficients, have no complete
cohomology over a subgroup in a degree in which the ideles killed by the prime have none and the
roots of unity of the field have none one degree higher.** -/
theorem isZero_tateModule_tensor_ideleClassTorsionRes (n : ℤ)
    (h₂ : Limits.IsZero
      (tateModule (resObj S (tensorObj (torsionRep (ideleAutHom k K) (p : ℤ)) W)) n))
    (h₁ : Limits.IsZero (tateModule (resObj S
      (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W)) (n + 1))) :
    Limits.IsZero
      (tateModule (resObj S (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W)) n) :=
  isZero_tateModule_X₃ (resSeq_tensorSeq_ideleClassTorsion_shortExact hp W S) n h₂ h₁

/-! ### The local form of the hypothesis -/

section Local

variable {d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))
  (w₀ : ∀ ω : orbitRel.Quotient ↥S (InfinitePlace K), ω.orbit)
  (v₀ : ∀ ω : orbitRel.Quotient ↥S (HeightOneSpectrum (𝓞 K)), ω.orbit)

include hp e in
/-- **The idele classes killed by a prime, tensored with coefficients of finite rank over the field
with that many elements, have no complete cohomology over a subgroup in a degree in which no local
factor has any and the roots of unity of the field have none one degree higher.**  The local factors
are indexed by the orbits of the subgroup on the places of the extension, and the factor at an orbit
is the complete cohomology of the stabiliser there with coefficients in the roots of unity of the
completion tensored with the restricted coefficients. -/
theorem isZero_tateModule_tensor_ideleClassTorsionRes_of_local (n : ℤ)
    (h₁ : ∀ ω : orbitRel.Quotient ↥S (InfinitePlace K), Limits.IsZero
      (tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
        (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)).comp
          (stabilizerSubgroupHom S ((w₀ ω : ω.orbit) : InfinitePlace K))) (p : ℤ))
        (resObj (stabilizer ↥S ((w₀ ω : ω.orbit) : InfinitePlace K)) (resObj S W))) n))
    (h₂ : ∀ ω : orbitRel.Quotient ↥S (HeightOneSpectrum (𝓞 K)), Limits.IsZero
      (tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)).comp
          (stabilizerSubgroupHom S ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))) (p : ℤ))
        (resObj (stabilizer ↥S ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))
          (resObj S W))) n))
    (h₃ : Limits.IsZero (tateModule (resObj S
      (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W)) (n + 1))) :
    Limits.IsZero
      (tateModule (resObj S (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W)) n) :=
  isZero_tateModule_tensor_ideleClassTorsionRes hp W S n
    (isZero_tateModule_tensor_ideleTorsionRes S W e w₀ v₀ n h₁ h₂) h₃

end Local

end

end InverseGalois.CFT
