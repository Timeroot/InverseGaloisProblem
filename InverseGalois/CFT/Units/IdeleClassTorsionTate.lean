/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TorsionFree
import InverseGalois.CFT.Units.IdeleClassTorsionSES
import InverseGalois.CFT.Units.IdeleTorsion

/-!
# The complete cohomology of the idele classes killed by a prime

The elements killed by a prime of the units, of the ideles and of the idele classes form a short
exact sequence, so their complete cohomologies fit into a long exact sequence.  Two of its three
terms are known: the middle one is, in every degree, the product over the places of the base field
of the complete cohomology of a decomposition group with coefficients in the roots of unity of a
completion, and the outer one on the left is the complete cohomology of the roots of unity of the
field itself.

The consequences are the two halves of the same statement.  Read forwards, the idele classes killed
by the prime have no complete cohomology in a degree in which no local factor has any and the roots
of unity have none one degree higher.  Read backwards, the connecting map has as its image exactly
the classes of the roots of unity of the field which die in the ideles, that is, the everywhere
locally trivial ones; so those classes are a quotient of the complete cohomology of the idele
classes killed by the prime, one degree lower.

## Main results

* `InverseGalois.CFT.range_tateδ_ideleClassTorsion`: **the everywhere locally trivial classes of the
  roots of unity of the field are exactly the image of the connecting map** from the complete
  cohomology of the idele classes killed by the prime, one degree lower.
* `InverseGalois.CFT.isZero_tateModule_ideleClassTorsion`: the idele classes killed by the prime
  have no complete cohomology in a degree in which the ideles killed by it have none and the units
  killed by it have none one degree higher.
* `InverseGalois.CFT.isZero_tateModule_ideleClassTorsion_of_local`: **the same, with the middle term
  replaced by the local factors** at the places of the base field.

## Tags

number field, idele class group, root of unity, Tate cohomology, long exact sequence
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

noncomputable section

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] [Finite Gal(K/k)]
  {p : ℕ} (hp : p.Prime)

/-! ### The connecting map -/

include hp

/-- The classes produced by the connecting map die in the ideles. -/
theorem tateMap_tateδ_ideleClassTorsion_eq_zero (n : ℤ)
    (y : ↥(tateModule (torsionRep (ideleClassAutHom k K) (p : ℤ)) n)) :
    tateMap (globalUnitsToIdeleTorsion k K (p : ℤ)) (n + 1)
        (tateδ (ideleClassTorsionShortComplex_shortExact k K hp) n y) = 0 :=
  (tateExact_δ_map (ideleClassTorsionShortComplex_shortExact k K hp) n).apply_apply_eq_zero y

/-- Every class of the roots of unity of the field which dies in the ideles comes from the complete
cohomology of the idele classes killed by the prime, one degree lower. -/
theorem exists_tateδ_ideleClassTorsion_eq (n : ℤ)
    (x : ↥(tateModule (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) (n + 1)))
    (hx : tateMap (globalUnitsToIdeleTorsion k K (p : ℤ)) (n + 1) x = 0) :
    ∃ y : ↥(tateModule (torsionRep (ideleClassAutHom k K) (p : ℤ)) n),
      tateδ (ideleClassTorsionShortComplex_shortExact k K hp) n y = x :=
  (tateExact_δ_map (ideleClassTorsionShortComplex_shortExact k K hp) n x).1 hx

/-- **The everywhere locally trivial classes of the roots of unity of the field are exactly the
image of the connecting map** from the complete cohomology of the idele classes killed by the prime,
one degree lower.  The kernel on the right is the group of everywhere locally trivial classes,
because the complete cohomology of the elements of the ideles killed by the prime is the product
over the places of the base field of the complete cohomology of a decomposition group with
coefficients in the roots of unity of a completion. -/
theorem range_tateδ_ideleClassTorsion (n : ℤ) :
    LinearMap.range (tateδ (ideleClassTorsionShortComplex_shortExact k K hp) n).hom
      = LinearMap.ker (tateMap (globalUnitsToIdeleTorsion k K (p : ℤ)) (n + 1)).hom := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  refine ⟨?_, exists_tateδ_ideleClassTorsion_eq hp n x⟩
  rintro ⟨y, rfl⟩
  exact tateMap_tateδ_ideleClassTorsion_eq_zero hp n y

/-! ### Vanishing -/

/-- **The idele classes killed by a prime have no complete cohomology in a degree in which the
ideles killed by it have none and the units killed by it have none one degree higher.** -/
theorem isZero_tateModule_ideleClassTorsion (n : ℤ)
    (h₂ : Limits.IsZero (tateModule (torsionRep (ideleAutHom k K) (p : ℤ)) n))
    (h₁ : Limits.IsZero
      (tateModule (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) (n + 1))) :
    Limits.IsZero (tateModule (torsionRep (ideleClassAutHom k K) (p : ℤ)) n) :=
  isZero_tateModule_X₃ (ideleClassTorsionShortComplex_shortExact k K hp) n h₂ h₁

variable (w₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), ω.orbit)
  (v₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), ω.orbit)

/-- **The idele classes killed by a prime have no complete cohomology in a degree in which no local
factor has any and the units killed by the prime have none one degree higher.**  The local factors
are the complete cohomologies of the decomposition groups with coefficients in the roots of unity of
the completions, one for each place of the base field. -/
theorem isZero_tateModule_ideleClassTorsion_of_local (n : ℤ)
    (h₁ : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
      Limits.IsZero (tateModule (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
        (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)) (p : ℤ)) n))
    (h₂ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      Limits.IsZero (tateModule (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (p : ℤ)) n))
    (h₀ : Limits.IsZero
      (tateModule (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) (n + 1))) :
    Limits.IsZero (tateModule (torsionRep (ideleClassAutHom k K) (p : ℤ)) n) :=
  isZero_tateModule_ideleClassTorsion hp n
    (isZero_tateModule_ideleTorsion w₀ v₀ (Int.natCast_ne_zero.2 hp.ne_zero) n h₁ h₂) h₀

end

end InverseGalois.CFT
