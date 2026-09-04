/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleTorusShaTorsion

/-!
# Exactly when the locally trivial classes come from the coefficients

The everywhere locally trivial classes of the units of a Galois extension of number fields, tensored
with coefficients killed by a prime, are always the classes the connecting map produces out of those
idele classes on which the obstruction of Tate and Nakayama vanishes.  They are all of the locally
trivial classes as soon as that obstruction group vanishes, but the obstruction group does not
vanish in general, so the sufficient condition is not the answer.

This file replaces it by a condition which is not merely sufficient but necessary.  The image of a
submodule under a linear map is everything the map reaches exactly when the submodule and the kernel
together span, and the kernel of the connecting map is what comes from the ideles.  So **the locally
trivial classes are exactly the image of the complete cohomology of the coefficients three degrees
lower precisely when every class of the idele classes tensored with the coefficients is the sum of
one on which the obstruction vanishes and one coming from the ideles** — equivalently, precisely
when the obstruction takes no value on the idele classes that it does not already take on the
ideles.

That is a statement purely about the obstruction and the ideles, with the units and the locally
trivial classes eliminated, and it is the shape a duality theorem for the everywhere locally trivial
classes has to take: the local data at the places has to account for the whole obstruction.

## Main results

* `InverseGalois.CFT.map_eq_range_iff_sup_ker_eq_top`: **the image of a submodule is the whole image
  of the map exactly when the submodule and the kernel together span.**
* `InverseGalois.CFT.ker_tateδ_tensor_ideleClass`: the classes of the idele classes tensored with
  coefficients killed by a prime which the connecting map kills are exactly those coming from the
  ideles.
* `InverseGalois.CFT.range_shaTorusPTorsionMap_eq_iff`,
  `InverseGalois.CFT.range_shaTorusPTorsionMap_eq_iff'`: **the everywhere locally trivial classes of
  the units tensored with coefficients killed by a prime are exactly the image of the complete
  cohomology of the coefficients three degrees lower if and only if the obstruction of Tate and
  Nakayama takes no value on the idele classes that it does not already take on the ideles.**
* `InverseGalois.CFT.range_shaTorusPTorsionMap_of_sup_eq_top`: the usable direction.

## Tags

number field, idele class group, Tate cohomology, Tate-Nakayama, Tate-Shafarevich group, duality
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open CategoryTheory

namespace InverseGalois.CFT

noncomputable section

open Tate

/-! ### When the image of a submodule is everything -/

section Map

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **The image of a submodule under a linear map is the whole image of the map exactly when the
submodule and the kernel together span.** -/
theorem map_eq_range_iff_sup_ker_eq_top (f : M →ₗ[R] N) (S : Submodule R M) :
    Submodule.map f S = LinearMap.range f ↔ S ⊔ LinearMap.ker f = ⊤ := by
  have hbot : Submodule.map f (LinearMap.ker f) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact LinearMap.mem_ker.1 hy
  constructor
  · intro h
    calc S ⊔ LinearMap.ker f = Submodule.comap f (Submodule.map f S) :=
          (Submodule.comap_map_eq f S).symm
      _ = Submodule.comap f (Submodule.map f ⊤) := by rw [h, Submodule.map_top]
      _ = ⊤ ⊔ LinearMap.ker f := Submodule.comap_map_eq f ⊤
      _ = ⊤ := top_sup_eq _
  · intro h
    rw [← Submodule.map_top, ← h, Submodule.map_sup, hbot, sup_bot_eq]

end Map

/-! ### The criterion -/

section Sha

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {p : ℕ} [Fact p.Prime] (W : Rep ℤ Gal(K/k)) (hW : ∀ w : ↥W.V, p • w = 0)

include hW

omit [IsGalois k K] in
/-- The classes of the idele classes tensored with coefficients killed by a prime which the
connecting map kills are exactly those coming from the ideles. -/
theorem ker_tateδ_tensor_ideleClass (n : ℤ) :
    LinearMap.ker (tateδ (tensorSeq_ideleClassShortComplex_shortExact_of_nsmul
        (Fact.out : p.Prime) W hW) n).hom
      = LinearMap.range (tateMap (tensorHomLeft W (ideleToIdeleClass k K)) n).hom := by
  ext x
  simpa only [LinearMap.mem_ker, LinearMap.mem_range, Set.mem_range] using
    tateExact_map_δ (tensorSeq_ideleClassShortComplex_shortExact_of_nsmul
      (Fact.out : p.Prime) W hW) n x

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower if
and only if every class of the idele classes tensored with the coefficients is the sum of one on
which the obstruction of Tate and Nakayama vanishes and one coming from the ideles.** -/
theorem range_shaTorusPTorsionMap_eq_iff (n : ℤ) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
        = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K))
          (n + 1 + 1 + 1)).hom ↔
      LinearMap.ker (baseTateNakayamaPTorsionRight k K W hW n)
          ⊔ LinearMap.range (tateMap (tensorHomLeft W (ideleToIdeleClass k K))
            (n + 1 + 1)).hom = ⊤ := by
  rw [range_shaTorusPTorsionMap,
    ← range_tateδ_tensor_ideleClass (Fact.out : p.Prime) W hW (n + 1 + 1),
    map_eq_range_iff_sup_ker_eq_top, ker_tateδ_tensor_ideleClass k K W hW (n + 1 + 1)]

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower if
and only if the obstruction of Tate and Nakayama takes no value on the idele classes that it does
not already take on the ideles.** -/
theorem range_shaTorusPTorsionMap_eq_iff' (n : ℤ) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
        = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K))
          (n + 1 + 1 + 1)).hom ↔
      Submodule.map (baseTateNakayamaPTorsionRight k K W hW n)
          (LinearMap.range (tateMap (tensorHomLeft W (ideleToIdeleClass k K)) (n + 1 + 1)).hom)
        = LinearMap.range (baseTateNakayamaPTorsionRight k K W hW n) := by
  rw [range_shaTorusPTorsionMap_eq_iff, map_eq_range_iff_sup_ker_eq_top, sup_comm]

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**, as
soon as every class of the idele classes tensored with the coefficients is the sum of one on which
the obstruction of Tate and Nakayama vanishes and one coming from the ideles. -/
theorem range_shaTorusPTorsionMap_of_sup_eq_top (n : ℤ)
    (h : LinearMap.ker (baseTateNakayamaPTorsionRight k K W hW n)
        ⊔ LinearMap.range (tateMap (tensorHomLeft W (ideleToIdeleClass k K))
          (n + 1 + 1)).hom = ⊤) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom :=
  (range_shaTorusPTorsionMap_eq_iff k K W hW n).2 h

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**, as
soon as the obstruction of Tate and Nakayama takes no value on the idele classes that it does not
already take on the ideles. -/
theorem range_shaTorusPTorsionMap_of_map_eq_range (n : ℤ)
    (h : Submodule.map (baseTateNakayamaPTorsionRight k K W hW n)
        (LinearMap.range (tateMap (tensorHomLeft W (ideleToIdeleClass k K)) (n + 1 + 1)).hom)
      = LinearMap.range (baseTateNakayamaPTorsionRight k K W hW n)) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom :=
  (range_shaTorusPTorsionMap_eq_iff' k K W hW n).2 h

end Sha

end

end InverseGalois.CFT
