/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.MapCoboundary
import InverseGalois.CFT.Units.IdeleClassSES
import InverseGalois.CFT.Units.IdeleCoboundary

/-!
# A two-cocycle of the units which is locally a coboundary is a coboundary

The second cohomology of the units of a Galois extension of number fields injects into the second
cohomology of its ideles, and a two-cocycle of the ideles which is a coboundary at every place is a
coboundary.  Putting the two together: a two-cocycle with values in the units of the top field
whose image at every place of the field is a coboundary is a coboundary.

In the language of the Brauer group this says that a class split by the extension is trivial as
soon as all of its local components are, which is the Albert-Brauer-Hasse-Noether theorem; in the
language of Tate-Shafarevich groups it says that the second one attached to the units of a Galois
extension of number fields vanishes.

## Main results

* `InverseGalois.CFT.exists_sub_add_eq_globalUnits`: **a two-cocycle of the Galois group with
  values in the units of the top field which is a coboundary at every place is a coboundary.**

## Tags

number field, idele, Brauer group, group cohomology, two-cocycle, coboundary,
Albert-Brauer-Hasse-Noether
-/

open CategoryTheory IsDedekindDomain MulAction NumberField groupCohomology

namespace InverseGalois.CFT

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **A two-cocycle of the Galois group with values in the units of the top field which is a
coboundary at every place is a coboundary.**  Its principal ideles form a two-cocycle of the ideles
which is locally a coboundary, hence a coboundary, and the second cohomology of the units injects
into the second cohomology of the ideles. -/
theorem exists_sub_add_eq_globalUnits {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (ha : ∀ x y z : Gal(K/k),
      globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y)
    (hinf : ∀ w : InfinitePlace K, ∃ c : ↥(stabilizer Gal(K/k) w) → Additive w.Completionˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) w),
        Additive.ofMul (infiniteUnitHom w (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ b : Gal(K/k) → Additive Kˣ,
      ∀ x y : Gal(K/k), a x y = globalUnitsAut x (b y) - b (x * y) + b x := by
  obtain ⟨b, hb⟩ := exists_coboundary_idele (k := k) (K := K)
    (a := fun x y => ideleDiag K (a x y))
    (by
      intro x y z
      rw [ideleAut_ideleDiag, ← map_add, ← map_add]
      exact congrArg (ideleDiag K) (ha x y z))
    hinf hfin
  have hcoc : (fun p : Gal(K/k) × Gal(K/k) => a p.1 p.2) ∈ cocycles₂ (globalUnitsRep k K) := by
    rw [mem_cocycles₂_iff]
    intro g h j
    exact (ha g h j).symm
  have hcob : (fun p : Gal(K/k) × Gal(K/k) => (globalUnitsToIdele k K).hom (a p.1 p.2))
      ∈ coboundaries₂ (ideleRep k K) :=
    ⟨b, funext fun p => (hb p.1 p.2).symm⟩
  obtain ⟨c, hc⟩ := mem_coboundaries₂_of_injective_map (globalUnitsToIdele k K)
    (injective_map_H2_globalUnits k K) hcoc hcob
  exact ⟨c, fun x y => (congrFun hc (x, y)).symm⟩

end InverseGalois.CFT
