/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.FreePresentation
import InverseGalois.CFT.TateCohomology.NakayamaCoeff
import InverseGalois.CFT.TateCohomology.NakayamaRestrict
import InverseGalois.CFT.TateCohomology.SylowSurjective
import InverseGalois.CFT.Units.IdeleTorusShaSharp

/-!
# The comparison of Tate and Nakayama for the idele class group, along a presentation

The theorem of Tate and Nakayama for the idele class group of a Galois extension of number fields
holds for coefficients flat over the integers, and there it is an isomorphism.  For coefficients
with torsion the comparison map still exists and is no longer onto, and the failure is exactly what
stands between the criterion of `InverseGalois.CFT.Units.IdeleTorusShaSharp` and a theorem.

The comparison is natural in the coefficients, so a presentation of the coefficients by a
representation flat over the integers already produces a large part of the image: every class the
presentation induces two degrees higher is a value of the comparison.  Since every representation
is a quotient of the free module on its elements, that part is always available.  What the criterion
then asks is only that the classes of the idele classes tensored with the coefficients be spanned by
those coming from the presentation together with those coming from the ideles.

The comparison also commutes with corestriction from a subgroup, and the coefficients are killed by
the prime, so corestriction from a Sylow subgroup for that prime is onto.  The spanning condition
may therefore be read on that subgroup alone, which is to say on the extension of the subfield it
fixes: **the criterion for the base field follows from the criterion for a subfield over which the
extension has degree a power of the prime.**

## Main results

* `InverseGalois.CFT.surjective_baseTateNakayamaTwoMap`: **the comparison of Tate and Nakayama for
  the idele class group is onto for coefficients flat over the integers.**
* `InverseGalois.CFT.range_tateMap_tensorHomRight_le_baseTateNakayama`: **a map of coefficients out
  of a flat representation produces nothing the comparison does not already produce.**
* `InverseGalois.CFT.range_shaTorusPTorsionMap_of_free`: **the everywhere locally trivial classes of
  the units tensored with coefficients killed by a prime are exactly the image of the complete
  cohomology of the coefficients three degrees lower**, as soon as the idele classes tensored with
  the coefficients are spanned by what the free presentation and the ideles produce.
* `InverseGalois.CFT.range_shaTorusPTorsionMap_of_sylow`: **the same conclusion from the same
  spanning condition read on a Sylow subgroup for the prime.**

## Tags

number field, idele class group, Tate-Nakayama, free presentation, Tate-Shafarevich group
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open CategoryTheory

namespace InverseGalois.CFT

noncomputable section

open Tate

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-! ### The comparison for flat coefficients -/

/-- The theorem of Tate and Nakayama for the idele class group is carried by the comparison map. -/
theorem coe_baseTateNakayamaEquiv (M : Rep ℤ Gal(K/k)) (hM : Module.Flat ℤ ↥M.V) (n : ℤ) :
    ⇑(baseTateNakayamaEquiv k K M hM n)
      = tateNakayamaTwoMap (ideleClassRep k K) (baseFundamentalClass k K) M n :=
  rfl

/-- **The comparison of Tate and Nakayama for the idele class group is onto for coefficients flat
over the integers.** -/
theorem surjective_baseTateNakayamaTwoMap (M : Rep ℤ Gal(K/k)) (hM : Module.Flat ℤ ↥M.V) (n : ℤ) :
    Function.Surjective
      (tateNakayamaTwoMap (ideleClassRep k K) (baseFundamentalClass k K) M n) := by
  rw [← coe_baseTateNakayamaEquiv k K M hM n]
  exact (baseTateNakayamaEquiv k K M hM n).surjective

/-! ### What a presentation produces -/

/-- **A map of coefficients out of a representation flat over the integers produces nothing the
comparison of Tate and Nakayama does not already produce.** -/
theorem range_tateMap_tensorHomRight_le_baseTateNakayama {M N : Rep ℤ Gal(K/k)}
    (hM : Module.Flat ℤ ↥M.V) (ψ : M ⟶ N) (n : ℤ) :
    LinearMap.range (tateMap (tensorHomRight (ideleClassRep k K) ψ) (n + 1 + 1)).hom
      ≤ LinearMap.range
        (tateNakayamaTwoMap (ideleClassRep k K) (baseFundamentalClass k K) N n) :=
  range_tateMap_tensorHomRight_le (ideleClassRep k K) (baseFundamentalClass k K) ψ n
    (surjective_baseTateNakayamaTwoMap k K M hM n)

/-- **The free presentation of the coefficients produces nothing the comparison of Tate and
Nakayama does not already produce.** -/
theorem range_tateMap_freeCounit_le_baseTateNakayama (N : Rep ℤ Gal(K/k)) (n : ℤ) :
    LinearMap.range (tateMap (tensorHomRight (ideleClassRep k K) (freeCounit N))
        (n + 1 + 1)).hom
      ≤ LinearMap.range
        (tateNakayamaTwoMap (ideleClassRep k K) (baseFundamentalClass k K) N n) :=
  range_tateMap_tensorHomRight_le_baseTateNakayama k K (flat_freeRep N) (freeCounit N) n

/-! ### The criterion along a free presentation -/

section Sha

variable {p : ℕ} [Fact p.Prime] (W : Rep ℤ Gal(K/k)) (hW : ∀ w : ↥W.V, p • w = 0)

include hW

/-- The classes of the idele classes tensored with coefficients killed by a prime on which the
obstruction of Tate and Nakayama vanishes are exactly the values of the comparison. -/
theorem ker_baseTateNakayamaPTorsionRight (n : ℤ) :
    LinearMap.ker (baseTateNakayamaPTorsionRight k K W hW n)
      = LinearMap.range (baseTateNakayamaPTorsionMap k K W n) :=
  LinearMap.exact_iff.1 (exact_baseTateNakayamaPTorsionRight k K W hW n)

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**, as
soon as the classes of the idele classes tensored with the coefficients are spanned by those the
free presentation of the coefficients produces together with those coming from the ideles. -/
theorem range_shaTorusPTorsionMap_of_free (n : ℤ)
    (h : LinearMap.range (tateMap (tensorHomRight (ideleClassRep k K) (freeCounit W))
          (n + 1 + 1)).hom
        ⊔ LinearMap.range (tateMap (tensorHomLeft W (ideleToIdeleClass k K)) (n + 1 + 1)).hom
      = ⊤) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom := by
  refine range_shaTorusPTorsionMap_of_sup_eq_top k K W hW n (eq_top_iff.2 ?_)
  rw [← h, ker_baseTateNakayamaPTorsionRight k K W hW n]
  exact sup_le_sup_right (range_tateMap_freeCounit_le_baseTateNakayama k K W n) _

/-! ### The criterion on a Sylow subgroup -/

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**, as
soon as the classes of the idele classes tensored with the coefficients are spanned, on a Sylow
subgroup for that prime, by those the comparison of Tate and Nakayama produces together with those
coming from the ideles. -/
theorem range_shaTorusPTorsionMap_of_sylow (P : Sylow p Gal(K/k)) (n : ℤ)
    (h : LinearMap.range (resTateNakayamaTwoMap (P : Subgroup Gal(K/k)) (ideleClassRep k K)
          (baseFundamentalClass k K) W n)
        ⊔ LinearMap.range (tateMap (resHom (P : Subgroup Gal(K/k))
            (tensorHomLeft W (ideleToIdeleClass k K))) (n + 1 + 1)).hom = ⊤) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom := by
  refine range_shaTorusPTorsionMap_of_sup_eq_top k K W hW n ?_
  rw [ker_baseTateNakayamaPTorsionRight k K W hW n]
  exact sup_range_eq_top_of_cor_two (P : Subgroup Gal(K/k)) (ideleClassRep k K)
    (baseFundamentalClass k K) W (tensorHomLeft W (ideleToIdeleClass k K)) n
    (surjective_tateCor_sylow_of_prime P (tensorObj (ideleClassRep k K) W) (n + 1 + 1)
      (nsmul_tensorObj_eq_zero (ideleClassRep k K) W p hW)) h

end Sha

end

end InverseGalois.CFT
