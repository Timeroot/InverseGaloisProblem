/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.BaseTateTorsion
import InverseGalois.CFT.Units.IdeleTensorSha

/-!
# The locally trivial classes with coefficients killed by a prime, and their source

The units of a Galois extension of number fields sit inside the ideles with the idele classes as
quotient, and that sequence stays exact after tensoring with coefficients killed by a prime.  The
long exact sequence then reads the everywhere locally trivial classes of the units tensored with the
coefficients, in a degree, as the image of the complete cohomology of the idele classes tensored
with them one degree lower.  The comparison of Tate and Nakayama maps the complete cohomology of the
coefficients themselves, two degrees lower again, into that group.  Composing the two produces
locally trivial classes out of the complete cohomology of the coefficients three degrees lower,
exactly as for a lattice.

For coefficients killed by a prime the comparison is no longer bijective, and what it misses is
measured by the idele classes killed by the prime.  The image of the composite is therefore not all
of the locally trivial classes but precisely the classes coming from those idele classes on which
the obstruction vanishes; and when that obstruction group has no complete cohomology in the relevant
degree, **the everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower.**
That is the finiteness which makes the group accessible: the complete cohomology of a finite group
in a fixed degree with coefficients killed by a prime is a finite object, while the cohomology of
the units is not.

## Main definitions

* `InverseGalois.CFT.shaTorusPTorsionMap`: the map from the complete cohomology of coefficients
  killed by a prime to the complete cohomology of the units tensored with them, three degrees
  higher.

## Main results

* `InverseGalois.CFT.tateMap_shaTorusPTorsionMap_eq_zero`: **the classes it produces are everywhere
  locally trivial.**
* `InverseGalois.CFT.range_shaTorusPTorsionMap`: **its image is exactly the classes produced by the
  idele classes on which the obstruction of Tate and Nakayama vanishes**, with no hypothesis at all.
* `InverseGalois.CFT.range_shaTorusPTorsionMap_of_isZero`,
  `InverseGalois.CFT.range_shaTorusPTorsionMap_of_isZero_idele`: **the everywhere locally trivial
  classes of the units tensored with coefficients killed by a prime are exactly the image of the
  complete cohomology of the coefficients three degrees lower**, as soon as the obstruction group
  vanishes; and the obstruction read on the ideles and on the units.
* `InverseGalois.CFT.range_shaTorusPTorsionMap_one`: the same in the first cohomology.

## Tags

number field, idele class group, Tate cohomology, Tate-Nakayama, Tate-Shafarevich group, torsion
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open CategoryTheory

namespace InverseGalois.CFT

noncomputable section

open Tate

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {p : ℕ} [Fact p.Prime] (W : Rep ℤ Gal(K/k)) (hW : ∀ w : ↥W.V, p • w = 0)

/-- **The map from the complete cohomology of coefficients killed by a prime to the complete
cohomology of the units tensored with them, three degrees higher**: the comparison of Tate and
Nakayama for the idele class group, followed by the connecting map of the sequence of the idele
classes. -/
def shaTorusPTorsionMap (n : ℤ) :
    ↥(tateModule W n) →ₗ[ℤ] ↥(tateModule (tensorObj (globalUnitsRep k K) W) (n + 1 + 1 + 1)) :=
  (tateδ (tensorSeq_ideleClassShortComplex_shortExact_of_nsmul (Fact.out : p.Prime) W hW)
      (n + 1 + 1)).hom ∘ₗ
    baseTateNakayamaPTorsionMap k K W n

theorem shaTorusPTorsionMap_apply (n : ℤ) (y : ↥(tateModule W n)) :
    shaTorusPTorsionMap k K W hW n y =
      tateδ (tensorSeq_ideleClassShortComplex_shortExact_of_nsmul (Fact.out : p.Prime) W hW)
        (n + 1 + 1) (baseTateNakayamaPTorsionMap k K W n y) :=
  rfl

/-- **The classes produced by the map are everywhere locally trivial.**  They come from the
connecting map of the sequence of the idele classes, and the composite of that map with the map
induced by the inclusion of the units into the ideles is zero. -/
theorem tateMap_shaTorusPTorsionMap_eq_zero (n : ℤ) (y : ↥(tateModule W n)) :
    tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)
      (shaTorusPTorsionMap k K W hW n y) = 0 :=
  tateMap_tateδ_tensor_ideleClass_eq_zero (Fact.out : p.Prime) W hW (n + 1 + 1)
    (baseTateNakayamaPTorsionMap k K W n y)

/-- **The classes produced by the map are exactly those the connecting map produces out of the idele
classes on which the obstruction of Tate and Nakayama vanishes.**  Nothing is assumed: the image of
the comparison is the kernel of the obstruction, and the image of a composite is the image of the
first map carried along the second. -/
theorem range_shaTorusPTorsionMap (n : ℤ) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = Submodule.map
          (tateδ (tensorSeq_ideleClassShortComplex_shortExact_of_nsmul (Fact.out : p.Prime) W hW)
            (n + 1 + 1)).hom
          (LinearMap.ker (baseTateNakayamaPTorsionRight k K W hW n)) := by
  show LinearMap.range
    ((tateδ (tensorSeq_ideleClassShortComplex_shortExact_of_nsmul (Fact.out : p.Prime) W hW)
        (n + 1 + 1)).hom ∘ₗ baseTateNakayamaPTorsionMap k K W n) = _
  rw [LinearMap.range_comp,
    ← LinearMap.exact_iff.1 (exact_baseTateNakayamaPTorsionRight k K W hW n)]

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**, as
soon as the idele classes killed by the prime, tensored with the same coefficients, have no complete
cohomology four degrees higher.  The kernel on the right is the group of everywhere locally trivial
classes, because the cohomology of the ideles is the product over the places of the cohomology of
the completions. -/
theorem range_shaTorusPTorsionMap_of_isZero (n : ℤ)
    (h : Limits.IsZero
      (tateModule (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W) (n + 1 + 1 + 1 + 1))) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom := by
  have hker : LinearMap.ker (baseTateNakayamaPTorsionRight k K W hW n) = ⊤ :=
    Submodule.eq_top_iff'.2 fun _ => LinearMap.mem_ker.2 (eq_zero_of_isZero h _)
  rw [range_shaTorusPTorsionMap, hker, Submodule.map_top,
    range_tateδ_tensor_ideleClass (Fact.out : p.Prime) W hW (n + 1 + 1)]

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**,
with the obstruction read on the ideles and on the units.  The ideles killed by the prime are a
product over the places of the roots of unity of the completions, so the obstruction is a purely
local condition together with one on the roots of unity of the field. -/
theorem range_shaTorusPTorsionMap_of_isZero_idele (n : ℤ)
    (h₂ : Limits.IsZero
      (tateModule (tensorObj (torsionRep (ideleAutHom k K) (p : ℤ)) W) (n + 1 + 1 + 1 + 1)))
    (h₁ : Limits.IsZero
      (tateModule (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W)
        (n + 1 + 1 + 1 + 1 + 1))) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom :=
  range_shaTorusPTorsionMap_of_isZero k K W hW n
    (isZero_tateModule_tensor_ideleClassTorsion (Fact.out : p.Prime) W (n + 1 + 1 + 1 + 1) h₂ h₁)

/-- **The everywhere locally trivial classes of the first cohomology of the units tensored with
coefficients killed by a prime are exactly the image of the complete cohomology of the coefficients
in degree `-2`**, as soon as the obstruction vanishes.  For a finite group that degree is a finite
object, so the group of everywhere locally trivial classes is finite. -/
theorem range_shaTorusPTorsionMap_one
    (h : Limits.IsZero
      (tateModule (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W) 2)) :
    LinearMap.range (shaTorusPTorsionMap k K W hW (-2))
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) 1).hom :=
  range_shaTorusPTorsionMap_of_isZero k K W hW (-2) h

end

end InverseGalois.CFT
