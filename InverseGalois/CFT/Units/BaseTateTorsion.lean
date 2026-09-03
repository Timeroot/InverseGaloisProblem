/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TensorTorsionError
import InverseGalois.CFT.Units.BaseTate
import InverseGalois.CFT.Units.IdeleTensorSha
import InverseGalois.CFT.Units.NsmulTorsionRep

/-!
# Tate and Nakayama for the idele class group, with coefficients killed by a prime

The theorem of Tate and Nakayama computes the complete cohomology of a representation tensored with
the idele class group from that of the representation alone, and the proof of it in the development
asks the representation to be flat over the integers.  The coefficients that occur in an embedding
problem are killed by a prime and are as far from flat as they can be, so what is needed is the
same statement with the flatness replaced by a hypothesis one can check.

What replaces it is the complete cohomology of the idele classes killed by the prime, tensored with
the coefficients, in the two degrees just above the one in question.  Those two groups sit on
either side of the comparison in a four term exact sequence, so nothing at all has to be assumed;
and when they vanish the comparison is an isomorphism again.  They are local: the idele classes
killed by the prime sit between the roots of unity of the field and the roots of unity of the
completions, so the two groups reduce to the ideles and the units, and the ideles are a product
over the places.

## Main definitions

* `InverseGalois.CFT.baseTateNakayamaPTorsionMap`: the comparison itself, with no hypothesis.
* `InverseGalois.CFT.baseTateNakayamaPTorsionLeft`,
  `InverseGalois.CFT.baseTateNakayamaPTorsionRight`: the maps entering and leaving it.
* `InverseGalois.CFT.baseTateNakayamaPTorsionEquiv`: **the theorem of Tate and Nakayama for the
  idele class group of a Galois extension of number fields, for coefficients killed by a prime.**
* `InverseGalois.CFT.baseTateNakayamaPTorsionEquivOfIdele`: the same, with the hypothesis pushed
  down to the ideles and the units.

## Main results

* `InverseGalois.CFT.exact_baseTateNakayamaPTorsionLeft`,
  `InverseGalois.CFT.exact_baseTateNakayamaPTorsionRight`: **the comparison of Tate and Nakayama
  for the idele class group, for coefficients killed by a prime, sits in a four term exact sequence
  whose two ends are the idele classes killed by the prime, tensored with the same coefficients.**

## Tags

number field, idele class group, fundamental class, Tate-Nakayama, torsion, embedding problem
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open CategoryTheory NumberField

namespace InverseGalois.CFT

noncomputable section

open Tate

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {p : ℕ} [Fact p.Prime] (W : Rep ℤ Gal(K/k)) (hW : ∀ w : ↥W.V, p • w = 0)

/-- The idele class group of a Galois extension of number fields, with its fundamental class,
satisfies the classical hypotheses of Tate's theorem on every Sylow subgroup for every prime. -/
theorem isTateClassTwo_baseFundamentalClass_sylow (q : ℕ) (_ : q.Prime) (P : Sylow q Gal(K/k)) :
    IsTateClassTwo (P : Subgroup Gal(K/k)) (ideleClassRep k K) (baseFundamentalClass k K) :=
  isTateClassTwo_baseFundamentalClass k K (P : Subgroup Gal(K/k))

include hW

/-- **The comparison of Tate and Nakayama for the idele class group of a Galois extension of number
fields**, with no hypothesis on the coefficients beyond being killed by a prime. -/
def baseTateNakayamaPTorsionMap (n : ℤ) :
    ↥(tateModule W n) →ₗ[ℤ] ↥(tateModule (tensorObj (ideleClassRep k K) W) (n + 1 + 1)) :=
  tateNakayamaTwoMap (ideleClassRep k K) (baseFundamentalClass k K) W n

/-- **The map entering the comparison**: the idele classes killed by the prime, tensored with the
coefficients, three degrees above the lower of the two degrees. -/
def baseTateNakayamaPTorsionLeft (n : ℤ) :
    ↥(tateModule (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W) (n + 1 + 1 + 1))
      →ₗ[ℤ] ↥(tateModule W n) :=
  tateNakayamaPTorsionErrorLeft (ideleClassRep k K) (baseFundamentalClass k K) W hW
      (isTateClassTwo_baseFundamentalClass_sylow k K) n ∘ₗ
    (tateTensorNsmulTorsionRepEquiv (ideleClassAutHom k K) p W (n + 1 + 1 + 1)).symm.toLinearMap

/-- **The map leaving the comparison**: the idele classes killed by the prime, tensored with the
coefficients, four degrees above the lower of the two degrees. -/
def baseTateNakayamaPTorsionRight (n : ℤ) :
    ↥(tateModule (tensorObj (ideleClassRep k K) W) (n + 1 + 1)) →ₗ[ℤ]
      ↥(tateModule (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W)
        (n + 1 + 1 + 1 + 1)) :=
  (tateTensorNsmulTorsionRepEquiv (ideleClassAutHom k K) p W
        (n + 1 + 1 + 1 + 1)).toLinearMap ∘ₗ
    tateNakayamaPTorsionErrorRight (ideleClassRep k K) (baseFundamentalClass k K) W hW
      (isTateClassTwo_baseFundamentalClass_sylow k K) n

/-- **The comparison of Tate and Nakayama for the idele class group is exact at the coefficients**:
what it kills comes from the idele classes killed by the prime, tensored with the coefficients,
three degrees above. -/
theorem exact_baseTateNakayamaPTorsionLeft (n : ℤ) :
    Function.Exact (baseTateNakayamaPTorsionLeft k K W hW n)
      (baseTateNakayamaPTorsionMap k K W n) := by
  refine LinearMap.exact_iff.2 ?_
  rw [show baseTateNakayamaPTorsionMap k K W n
      = tateNakayamaTwoMap (ideleClassRep k K) (baseFundamentalClass k K) W n from rfl,
    ← range_tateNakayamaPTorsionErrorLeft (ideleClassRep k K) (baseFundamentalClass k K) W hW
      (isTateClassTwo_baseFundamentalClass_sylow k K) n]
  show _ = LinearMap.range (_ ∘ₗ
    (tateTensorNsmulTorsionRepEquiv (ideleClassAutHom k K) p W (n + 1 + 1 + 1)).symm.toLinearMap)
  rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

/-- **The comparison of Tate and Nakayama for the idele class group is exact at the tensor
product**: what dies in the idele classes killed by the prime, tensored with the coefficients, four
degrees above, comes from the coefficients. -/
theorem exact_baseTateNakayamaPTorsionRight (n : ℤ) :
    Function.Exact (baseTateNakayamaPTorsionMap k K W n)
      (baseTateNakayamaPTorsionRight k K W hW n) := by
  refine LinearMap.exact_iff.2 ?_
  rw [show baseTateNakayamaPTorsionMap k K W n
      = tateNakayamaTwoMap (ideleClassRep k K) (baseFundamentalClass k K) W n from rfl,
    ← ker_tateNakayamaPTorsionErrorRight (ideleClassRep k K) (baseFundamentalClass k K) W hW
      (isTateClassTwo_baseFundamentalClass_sylow k K) n]
  show LinearMap.ker ((tateTensorNsmulTorsionRepEquiv (ideleClassAutHom k K) p W
      (n + 1 + 1 + 1 + 1)).toLinearMap ∘ₗ _) = _
  exact LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot_of_injective
      (tateTensorNsmulTorsionRepEquiv (ideleClassAutHom k K) p W (n + 1 + 1 + 1 + 1)).injective)

/-- **The theorem of Tate and Nakayama for the idele class group of a Galois extension of number
fields, for coefficients killed by a prime**: the complete cohomology of a representation killed by
a prime in a degree is the complete cohomology of its tensor product with the idele class group two
degrees higher, as soon as the idele classes killed by the prime, tensored with the same
coefficients, have no complete cohomology in the two degrees just above. -/
def baseTateNakayamaPTorsionEquiv (n : ℤ)
    (h : Limits.IsZero
      (tateModule (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W) (n + 1 + 1 + 1)))
    (h' : Limits.IsZero
      (tateModule (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W) (n + 1 + 1 + 1 + 1))) :
    ↥(tateModule W n) ≃ₗ[ℤ] ↥(tateModule (tensorObj (ideleClassRep k K) W) (n + 1 + 1)) :=
  tateNakayamaTwoEquivOfPTorsion (ideleClassRep k K) (baseFundamentalClass k K) W hW
    (fun _ _ P => isTateClassTwo_baseFundamentalClass k K (P : Subgroup Gal(K/k))) n
    (isZero_tateModule_tensorObj_nsmulTorsion_repOfAddAut (ideleClassAutHom k K) p W
      (n + 1 + 1 + 1) h)
    (isZero_tateModule_tensorObj_nsmulTorsion_repOfAddAut (ideleClassAutHom k K) p W
      (n + 1 + 1 + 1 + 1) h')

/-- **The theorem of Tate and Nakayama for the idele class group of a Galois extension of number
fields, for coefficients killed by a prime, with the hypothesis read on the ideles and on the
units**: the ideles killed by the prime are a product over the places of the roots of unity of the
completions, so the two hypotheses on them are local ones. -/
def baseTateNakayamaPTorsionEquivOfIdele (n : ℤ)
    (h₂ : Limits.IsZero
      (tateModule (tensorObj (torsionRep (ideleAutHom k K) (p : ℤ)) W) (n + 1 + 1 + 1)))
    (h₁ : Limits.IsZero
      (tateModule (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W)
        (n + 1 + 1 + 1 + 1)))
    (h₂' : Limits.IsZero
      (tateModule (tensorObj (torsionRep (ideleAutHom k K) (p : ℤ)) W) (n + 1 + 1 + 1 + 1)))
    (h₁' : Limits.IsZero
      (tateModule (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W)
        (n + 1 + 1 + 1 + 1 + 1))) :
    ↥(tateModule W n) ≃ₗ[ℤ] ↥(tateModule (tensorObj (ideleClassRep k K) W) (n + 1 + 1)) :=
  baseTateNakayamaPTorsionEquiv k K W hW n
    (isZero_tateModule_tensor_ideleClassTorsion (Fact.out : p.Prime) W (n + 1 + 1 + 1) h₂ h₁)
    (isZero_tateModule_tensor_ideleClassTorsion (Fact.out : p.Prime) W (n + 1 + 1 + 1 + 1) h₂' h₁')

end

end InverseGalois.CFT
