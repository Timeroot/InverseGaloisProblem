/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleTensorTorsion
import InverseGalois.CFT.Units.IdeleTorsionTensor

/-!
# The idele classes killed by a prime, tensored with coefficients, read locally

The elements killed by a prime of the units, of the ideles and of the idele classes stay short exact
after tensoring with any coefficients, because the middle term is killed by the prime.  The long
exact sequence of complete cohomology therefore reads the middle group of the three, the one which
measures the failure of the theorem of Tate and Nakayama for coefficients with torsion, between two
groups that are known: the ideles killed by the prime are the roots of unity of every completion at
once, so their complete cohomology tensored with coefficients of finite rank over the prime field is
a product of local groups, one for each place of the base field; and the outer term on the other
side is the roots of unity of the field itself.

What comes out is the exactness statement in usable form: **a class of the idele classes killed by a
prime, tensored with the coefficients, comes from local data at the places exactly when the
connecting map kills it**, and in particular every such class comes from local data as soon as the
roots of unity of the field carry no complete cohomology one degree higher.  This is the shape the
error term of the theorem of Tate and Nakayama takes: a global group presented by local ones.

## Main results

* `InverseGalois.CFT.ker_tateδ_tensor_ideleClassTorsion`: the classes of the idele classes killed by
  a prime, tensored with the coefficients, which the connecting map kills are exactly those coming
  from the ideles killed by the prime.
* `InverseGalois.CFT.exists_localTorsion_tateMap_eq`: **a class killed by the connecting map is the
  image of a family of local classes**, one for each place of the base field, each read in the
  decomposition group of a place above it with coefficients in the roots of unity of the completion
  tensored with the restricted coefficients.
* `InverseGalois.CFT.exists_localTorsion_tateMap_eq_of_isZero`: **every class is the image of such a
  family** as soon as the roots of unity of the field, tensored with the coefficients, carry no
  complete cohomology one degree higher.

## Tags

number field, idele class group, root of unity, decomposition group, Tate cohomology, tensor product
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

noncomputable section

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] [Finite Gal(K/k)]
  (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))
  (w₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), ω.orbit)
  (v₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), ω.orbit)

/-! ### The exactness -/

/-- The classes of the idele classes killed by a prime, tensored with the coefficients, which the
connecting map kills are exactly those coming from the ideles killed by the prime. -/
theorem ker_tateδ_tensor_ideleClassTorsion (n : ℤ) :
    LinearMap.ker (tateδ (tensorSeq_ideleClassTorsionShortComplex_shortExact
        (Fact.out : p.Prime) W) n).hom
      = LinearMap.range
        (tateMap (tensorHomLeft W (ideleToIdeleClassTorsion k K (p : ℤ))) n).hom := by
  ext x
  simpa only [LinearMap.mem_ker, LinearMap.mem_range, Set.mem_range] using
    tateExact_map_δ (tensorSeq_ideleClassTorsionShortComplex_shortExact
      (Fact.out : p.Prime) W) n x

/-! ### The local data -/

include e in
/-- **A class of the idele classes killed by a prime, tensored with coefficients of finite rank over
the field with that many elements, which the connecting map kills is the image of a family of local
classes.**  There is one member of the family for each place of the base field, read in the
decomposition group of a place above it with coefficients in the roots of unity of the completion
there tensored with the restricted coefficients. -/
theorem exists_localTorsion_tateMap_eq (n : ℤ)
    (x : tateModule (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W) n)
    (hx : tateδ (tensorSeq_ideleClassTorsionShortComplex_shortExact (Fact.out : p.Prime) W) n x
      = 0) :
    ∃ y : (∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
          tateModule (tensorObj (torsionRep (smulUnitsAut
            (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
            (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)) (p : ℤ))
            (resObj (stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)) W)) n) ×
        (∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
          tateModule (tensorObj (torsionRep (smulUnitsAut
            (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
            (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (p : ℤ))
            (resObj (stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) W)) n),
      tateMap (tensorHomLeft W (ideleToIdeleClassTorsion k K (p : ℤ))) n
        ((ideleTorsionTensorTateEquiv W e w₀ v₀ n).symm y) = x := by
  obtain ⟨z, hz⟩ := (tateExact_map_δ (tensorSeq_ideleClassTorsionShortComplex_shortExact
    (Fact.out : p.Prime) W) n x).1 hx
  refine ⟨ideleTorsionTensorTateEquiv W e w₀ v₀ n z, ?_⟩
  rw [AddEquiv.symm_apply_apply]
  exact hz

include e in
/-- **Every class of the idele classes killed by a prime, tensored with coefficients of finite rank
over the field with that many elements, is the image of a family of local classes** as soon as the
roots of unity of the field, tensored with the coefficients, carry no complete cohomology one degree
higher.  The error term of the theorem of Tate and Nakayama is then a global group presented
entirely by local ones. -/
theorem exists_localTorsion_tateMap_eq_of_isZero (n : ℤ)
    (h : Limits.IsZero (tateModule
      (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W) (n + 1)))
    (x : tateModule (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W) n) :
    ∃ y : (∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
          tateModule (tensorObj (torsionRep (smulUnitsAut
            (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
            (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)) (p : ℤ))
            (resObj (stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)) W)) n) ×
        (∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
          tateModule (tensorObj (torsionRep (smulUnitsAut
            (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
            (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (p : ℤ))
            (resObj (stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) W)) n),
      tateMap (tensorHomLeft W (ideleToIdeleClassTorsion k K (p : ℤ))) n
        ((ideleTorsionTensorTateEquiv W e w₀ v₀ n).symm y) = x :=
  exists_localTorsion_tateMap_eq W e w₀ v₀ n x (eq_zero_of_isZero h _)

end

end InverseGalois.CFT
