/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleTorsionTensor
import InverseGalois.CFT.Units.IdeleTorusShaTorsion

/-!
# The locally trivial classes with coefficients killed by a prime, place by place

The everywhere locally trivial classes of the units of a Galois extension of number fields, tensored
with coefficients killed by a prime, are the image of the complete cohomology of the coefficients
three degrees lower as soon as one obstruction group vanishes, and that obstruction group is read on
the elements of the ideles killed by the prime and on the roots of unity of the field.  The elements
of the ideles killed by the prime are the roots of unity of every completion at once, so the
obstruction splits into one condition per place of the base field, each involving only the
decomposition group of a place above it.

Most places cost nothing.  The local module is killed by the prime and the local complete cohomology
is killed by the order of the decomposition group, so a place whose decomposition group has order
prime to the prime contributes nothing at all.  At an archimedean place the decomposition group has
order one or two, so **for an odd prime the archimedean places drop out of the criterion entirely**
and what is left is a condition at the finite places together with one on the roots of unity of the
field.

## Main results

* `InverseGalois.CFT.isZero_tateModule_tensor_adicTorsion_of_coprime`,
  `InverseGalois.CFT.isZero_tateModule_tensor_infiniteTorsion_of_coprime`: **a place whose
  decomposition group has order prime to the prime contributes nothing.**
* `InverseGalois.CFT.isZero_tateModule_tensor_infiniteTorsion_of_odd`: **for an odd prime an
  archimedean place contributes nothing**, its decomposition group having order one or two.
* `InverseGalois.CFT.range_shaTorusPTorsionMap_of_isZero_local`: **the everywhere locally trivial
  classes of the units tensored with coefficients of finite rank over the field with a prime number
  of elements are exactly the image of the complete cohomology of the coefficients three degrees
  lower**, as soon as no local factor and no class of the roots of unity of the field obstructs.
* `InverseGalois.CFT.range_shaTorusPTorsionMap_of_isZero_adic`,
  `InverseGalois.CFT.range_shaTorusPTorsionMap_one_of_isZero_adic`: the same for an odd prime, with
  the archimedean places already discharged.

## Tags

number field, idele, decomposition group, Tate cohomology, Tate-Shafarevich group, tensor product
-/

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

noncomputable section

/-! ### The places that cost nothing -/

section CoprimeFinite

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] [Finite Gal(K/k)]
  (W : Rep ℤ Gal(K/k)) {p : ℕ}

/-- **A finite place whose decomposition group has order prime to the prime contributes nothing.**
The roots of unity of the completion there are killed by the prime, while the complete cohomology of
the decomposition group is killed by its order. -/
theorem isZero_tateModule_tensor_adicTorsion_of_coprime (v : HeightOneSpectrum (𝓞 K))
    (hcop : Nat.Coprime p (Nat.card ↥(stabilizer Gal(K/k) v))) (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj (torsionRep (smulUnitsAut
      (G := ↥(stabilizer Gal(K/k) v)) (R := v.adicCompletion K)) (p : ℤ))
      (resObj (stabilizer Gal(K/k) v) W)) n) :=
  isZero_tateModule_tensorObj_of_coprime' _ _ (fun a => nsmul_eq_zero_torsionBy a) hcop n

end CoprimeFinite

section CoprimeArchimedean

variable {k K : Type} [Field k] [Field K] [Algebra k K] [Finite Gal(K/k)]
  (W : Rep ℤ Gal(K/k)) {p : ℕ}

/-- **An archimedean place whose decomposition group has order prime to the prime contributes
nothing.** -/
theorem isZero_tateModule_tensor_infiniteTorsion_of_coprime (w : InfinitePlace K)
    (hcop : Nat.Coprime p (Nat.card ↥(stabilizer Gal(K/k) w))) (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj (torsionRep (smulUnitsAut
      (G := ↥(stabilizer Gal(K/k) w)) (R := w.Completion)) (p : ℤ))
      (resObj (stabilizer Gal(K/k) w) W)) n) :=
  isZero_tateModule_tensorObj_of_coprime' _ _ (fun a => nsmul_eq_zero_torsionBy a) hcop n

/-- **For an odd prime an archimedean place contributes nothing**, because the decomposition group
of an archimedean place has order one or two. -/
theorem isZero_tateModule_tensor_infiniteTorsion_of_odd (hodd : Odd p) (w : InfinitePlace K)
    (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj (torsionRep (smulUnitsAut
      (G := ↥(stabilizer Gal(K/k) w)) (R := w.Completion)) (p : ℤ))
      (resObj (stabilizer Gal(K/k) w) W)) n) := by
  refine isZero_tateModule_tensor_infiniteTorsion_of_coprime W w ?_ n
  rcases InfinitePlace.nat_card_stabilizer_eq_one_or_two k w with h | h
  · rw [h]
    exact Nat.coprime_one_right p
  · rw [h]
    exact Nat.coprime_two_right.2 hodd

end CoprimeArchimedean

/-! ### The criterion, place by place -/

section Sha

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {p d : ℕ} [Fact p.Prime] (W : Rep ℤ Gal(K/k)) (e : ↥W.V ≃+ (Fin d → ZMod p))
  (w₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), ω.orbit)
  (v₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), ω.orbit)

include e in
/-- **The everywhere locally trivial classes of the units tensored with coefficients of finite rank
over the field with a prime number of elements are exactly the image of the complete cohomology of
the coefficients three degrees lower**, as soon as no place of the base field obstructs and the
roots of unity of the field do not either.  The condition at a place involves only the decomposition
group of a place above it acting on the roots of unity of the completion there, tensored with the
restricted coefficients. -/
theorem range_shaTorusPTorsionMap_of_isZero_local (n : ℤ)
    (h₁ : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), Limits.IsZero
      (tateModule (tensorObj (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
        (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)) (p : ℤ))
        (resObj (stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)) W))
        (n + 1 + 1 + 1 + 1)))
    (h₂ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), Limits.IsZero
      (tateModule (tensorObj (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (p : ℤ))
        (resObj (stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) W))
        (n + 1 + 1 + 1 + 1)))
    (h₀ : Limits.IsZero
      (tateModule (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W)
        (n + 1 + 1 + 1 + 1 + 1))) :
    LinearMap.range (shaTorusPTorsionMap k K W (nsmul_eq_zero_of_equivPi e) n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom :=
  range_shaTorusPTorsionMap_of_isZero_idele k K W (nsmul_eq_zero_of_equivPi e) n
    (isZero_tateModule_tensor_ideleTorsion W e w₀ v₀ (n + 1 + 1 + 1 + 1) h₁ h₂) h₀

include e in
/-- **For an odd prime the archimedean places drop out of the criterion**: the everywhere locally
trivial classes of the units tensored with coefficients of finite rank over the field with that many
elements are exactly the image of the complete cohomology of the coefficients three degrees lower as
soon as no finite place obstructs and the roots of unity of the field do not either. -/
theorem range_shaTorusPTorsionMap_of_isZero_adic (hodd : Odd p) (n : ℤ)
    (h₂ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), Limits.IsZero
      (tateModule (tensorObj (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (p : ℤ))
        (resObj (stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) W))
        (n + 1 + 1 + 1 + 1)))
    (h₀ : Limits.IsZero
      (tateModule (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W)
        (n + 1 + 1 + 1 + 1 + 1))) :
    LinearMap.range (shaTorusPTorsionMap k K W (nsmul_eq_zero_of_equivPi e) n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom :=
  range_shaTorusPTorsionMap_of_isZero_local k K W e
    (fun ω => ⟨_, ω.nonempty_orbit.choose_spec⟩) v₀ n
    (fun _ => isZero_tateModule_tensor_infiniteTorsion_of_odd W hodd _ _) h₂ h₀

include e in
/-- **The everywhere locally trivial classes of the first cohomology of the units tensored with
coefficients of finite rank over the field with an odd prime number of elements are exactly the
image of the complete cohomology of the coefficients in degree `-2`**, as soon as no finite place
obstructs and the roots of unity of the field do not either.  For a finite group that degree is a
finite object, so the group of everywhere locally trivial classes is finite. -/
theorem range_shaTorusPTorsionMap_one_of_isZero_adic (hodd : Odd p)
    (h₂ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), Limits.IsZero
      (tateModule (tensorObj (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (p : ℤ))
        (resObj (stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) W)) 2))
    (h₀ : Limits.IsZero
      (tateModule (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W) 3)) :
    LinearMap.range (shaTorusPTorsionMap k K W (nsmul_eq_zero_of_equivPi e) (-2))
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) 1).hom :=
  range_shaTorusPTorsionMap_of_isZero_adic k K W e v₀ hodd (-2) h₂ h₀

end Sha

end

end InverseGalois.CFT
