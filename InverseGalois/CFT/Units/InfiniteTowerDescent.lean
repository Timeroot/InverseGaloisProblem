/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ABHNPlaces
import InverseGalois.CFT.Units.InfiniteHilbert90
import InverseGalois.CFT.Units.PlaceRestrict
import InverseGalois.CFT.Units.TowerDescent

/-!
# Descending a local coboundary at an infinite place along a tower

Let `k ⊆ F ⊆ K` be a tower of number fields with `F` and `K` normal over `k`, let `a` be a family
of units of `k` indexed by pairs of automorphisms of `F` over `k`, and let `w` be an infinite place
of `K`.  Composing with the restriction map turns `a` into a family indexed by pairs of
automorphisms of `K` over `k`, and this file descends the archimedean local hypothesis of the
Albert-Brauer-Hasse-Noether theorem from `K` to `F`: if the inflated family is a coboundary in the
local units at `w`, then `a` itself is a coboundary in the local units at the place below.

The descent has the same three ingredients as at a finite place.  The decomposition group at `w`
maps onto the decomposition group at the place below, because the Galois group over the middle
field already acts transitively on the infinite places above a given one.  The local units of the
middle field are exactly the local units of the top field fixed by the kernel of that map, which is
the decomposition group of the top field over the middle one.  And Hilbert's theorem 90 for that
kernel lets the trivialising cochain be corrected so as to be constant on it.  A cochain constant
on the kernel and trivialising an inflated cocycle descends, which is the general descent of a
two-coboundary along a surjection.

## Main definitions

* `InverseGalois.CFT.infiniteUnitsComapHom`: the local units of the base field inside the local
  units at an infinite place above, written multiplicatively.
* `InverseGalois.CFT.stabilizerRestrictPlaceInfinite`: the decomposition group at an infinite place
  of the top field maps to the decomposition group at the place of the middle field below it.

## Main results

* `InverseGalois.CFT.stabilizerRestrictPlaceInfinite_surjective`: **the decomposition group at an
  infinite place maps onto the decomposition group at the place of the middle field below it.**
* `InverseGalois.CFT.exists_infiniteUnitsComapHom_eq_of_ker`: a local unit fixed by the
  decomposition group of the top field over the middle one comes from the completion of the middle
  field.
* `InverseGalois.CFT.exists_sub_add_eq_infiniteUnits_descent`: **a family of units of the base
  field whose inflation is a local coboundary at an infinite place of the top field is a local
  coboundary at the place of the middle field below it.**

## Tags

number field, tower, infinite place, completion, decomposition group, two-cocycle, coboundary,
inflation, Hilbert ninety, relative Brauer group
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

open MulAction NumberField groupCohomology

namespace InverseGalois.CFT

/-! ### The local units of the base field, written multiplicatively -/

section Generic

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : InfinitePlace K)

omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- **The action of the decomposition group at an infinite place on the units of the completion is
the action carried along the passage to additive notation.** -/
theorem toMul_smulUnitsAut_stabilizerInfinite (σ : ↥(stabilizer Gal(K/k) w))
    (u : Additive (w.Completion)ˣ) :
    Additive.toMul (smulUnitsAut σ u) = σ • Additive.toMul u :=
  Units.ext rfl

variable (k) in
omit [IsGalois k K] in
/-- **The units of the completion of the base field, viewed in the completion at an infinite place
above**, written multiplicatively. -/
noncomputable def infiniteUnitsComapHom :
    ((w.comap (algebraMap k K)).Completion)ˣ →* (w.Completion)ˣ :=
  Units.map (algebraMap (w.comap (algebraMap k K)).Completion w.Completion).toMonoidHom

variable (k) in
omit [NumberField k] [NumberField K] [IsGalois k K] in
@[simp]
theorem coe_infiniteUnitsComapHom (u : ((w.comap (algebraMap k K)).Completion)ˣ) :
    ((infiniteUnitsComapHom k w u : (w.Completion)ˣ) : w.Completion)
      = algebraMap (w.comap (algebraMap k K)).Completion w.Completion
        (u : (w.comap (algebraMap k K)).Completion) := rfl

variable (k) in
omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- The multiplicative and the additive readings of the local units of the base field agree. -/
theorem ofMul_infiniteUnitsComapHom (u : ((w.comap (algebraMap k K)).Completion)ˣ) :
    Additive.ofMul (infiniteUnitsComapHom k w u) = infiniteUnitsComap k w (Additive.ofMul u) := rfl

variable (k) in
omit [IsGalois k K] in
/-- **The inclusion of the local units of the base field is injective.** -/
theorem infiniteUnitsComapHom_injective : Function.Injective (infiniteUnitsComapHom k w) := by
  intro u u' h
  refine Additive.ofMul.injective (infiniteUnitsComap_injective k w ?_)
  rw [← ofMul_infiniteUnitsComapHom, ← ofMul_infiniteUnitsComapHom, h]

end Generic

/-! ### The automorphism of a completion on the image of the field -/

section InfiniteCoe

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The automorphism of the completion at an infinite place attached to an automorphism fixing
the place carries the section determined by an element of the field to the section determined by
its image.** -/
@[simp]
theorem infiniteCompletionAut_infiniteCoe (w : InfinitePlace K) (σ : Gal(K/k)) (hσ : σ • w = w)
    (y : K) : infiniteCompletionAut w σ hσ (infiniteCoe y w) = infiniteCoe (σ y) w := by
  rw [infiniteCoe, infiniteCompletionAut_coe]
  rfl

end InfiniteCoe

/-! ### The decomposition groups at an infinite place along a tower -/

section TowerDescent

variable {k F K : Type} [Field k] [NumberField k] [Field F] [NumberField F] [Field K]
  [NumberField K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]
  [IsGalois k F] [IsGalois k K] (w : InfinitePlace K)

variable (F) in
omit [NumberField k] [NumberField F] [NumberField K] [IsGalois k K] in
/-- **An automorphism of the top field fixing an infinite place fixes the place of the middle field
below it.** -/
theorem restrictNormalHom_smul_comap {σ : Gal(K/k)} (hσ : σ • w = w) :
    AlgEquiv.restrictNormalHom F σ • w.comap (algebraMap F K) = w.comap (algebraMap F K) := by
  rw [← comap_smul_algebraMap F σ w, hσ]

variable (F) in
/-- **The decomposition group at an infinite place of the top field maps to the decomposition group
at the place of the middle field below it**, by restriction of automorphisms. -/
noncomputable def stabilizerRestrictPlaceInfinite :
    ↥(stabilizer Gal(K/k) w) →* ↥(stabilizer Gal(F/k) (w.comap (algebraMap F K))) where
  toFun σ := ⟨AlgEquiv.restrictNormalHom F σ.1,
    mem_stabilizer_iff.mpr (restrictNormalHom_smul_comap F w (mem_stabilizer_iff.mp σ.2))⟩
  map_one' := Subtype.ext (map_one (AlgEquiv.restrictNormalHom F))
  map_mul' σ τ := Subtype.ext (map_mul (AlgEquiv.restrictNormalHom F) σ.1 τ.1)

variable (F) in
omit [NumberField k] [NumberField F] [NumberField K] [IsGalois k K] in
@[simp]
theorem coe_stabilizerRestrictInfinite (σ : ↥(stabilizer Gal(K/k) w)) :
    (stabilizerRestrictPlaceInfinite F w σ : Gal(F/k)) = AlgEquiv.restrictNormalHom F σ.1 := rfl

variable (F) in
omit [NumberField k] [NumberField F] [NumberField K] in
/-- **The decomposition group at an infinite place maps onto the decomposition group at the place
of the middle field below it.**  An automorphism of the middle field fixing the place there lifts
to the top field; the lift moves the place above to another place above the same one, and the
Galois group of the top field over the middle one moves it back. -/
theorem stabilizerRestrictPlaceInfinite_surjective :
    Function.Surjective (stabilizerRestrictPlaceInfinite (k := k) F w) := by
  haveI : IsGalois F K := IsGalois.tower_top_of_isGalois k F K
  intro τ
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom F : Gal(K/k) →* Gal(F/k)) :=
    AlgEquiv.restrictNormalHom_surjective K
  obtain ⟨σ₀, hσ₀⟩ := hsurj τ.1
  have hcomap : (σ₀ • w).comap (algebraMap F K) = w.comap (algebraMap F K) := by
    rw [comap_smul_algebraMap F σ₀ w, hσ₀]
    exact mem_stabilizer_iff.mp τ.2
  obtain ⟨ρ₀, hρ₀⟩ :=
    NumberField.InfinitePlace.exists_smul_eq_of_comap_eq (k := F) (K := K) hcomap
  have hstab : (ρ₀.restrictScalars k * σ₀) • w = w := by
    rw [mul_smul]
    exact hρ₀
  refine ⟨⟨ρ₀.restrictScalars k * σ₀, mem_stabilizer_iff.mpr hstab⟩, Subtype.ext ?_⟩
  rw [coe_stabilizerRestrictInfinite]
  show AlgEquiv.restrictNormalHom F (ρ₀.restrictScalars k * σ₀) = τ.1
  rw [map_mul, restrictNormalHom_restrictScalars k F ρ₀, one_mul, hσ₀]

/-! ### The completions at an infinite place along a tower -/

variable (F) in
omit [NumberField k] [NumberField F] [NumberField K] [IsGalois k K] in
/-- **The automorphisms of the completions at an infinite place attached to an automorphism fixing
the place and to its restriction to the middle field agree on the completion of the middle
field**: both sides are continuous and agree on the dense image of the middle field. -/
theorem infiniteCompletionAut_infiniteCompletionComap_restrict (σ : Gal(K/k)) (hσ : σ • w = w)
    (c : (w.comap (algebraMap F K)).Completion) :
    infiniteCompletionAut w σ hσ (infiniteCompletionComap F w c)
      = infiniteCompletionComap F w
          (infiniteCompletionAut (w.comap (algebraMap F K)) (AlgEquiv.restrictNormalHom F σ)
            (restrictNormalHom_smul_comap F w hσ) c) := by
  refine UniformSpace.Completion.induction_on c ?_ ?_
  · exact isClosed_eq
      ((continuous_infiniteCompletionAut w σ hσ).comp (continuous_infiniteCompletionComap F w))
      ((continuous_infiniteCompletionComap F w).comp
        (continuous_infiniteCompletionAut (w.comap (algebraMap F K))
          (AlgEquiv.restrictNormalHom F σ) (restrictNormalHom_smul_comap F w hσ)))
  · intro x
    set y : F := WithAbs.equiv (w.comap (algebraMap F K)).1 x with hy
    have h1 : infiniteCompletionComap F w (infiniteCoe y (w.comap (algebraMap F K)))
        = infiniteCoe (algebraMap F K y) w := infiniteCompletionComap_coe F w _
    have h2 : infiniteCompletionComap F w
          (infiniteCoe (AlgEquiv.restrictNormalHom F σ y) (w.comap (algebraMap F K)))
        = infiniteCoe (algebraMap F K (AlgEquiv.restrictNormalHom F σ y)) w :=
      infiniteCompletionComap_coe F w _
    show infiniteCompletionAut w σ hσ
        (infiniteCompletionComap F w (infiniteCoe y (w.comap (algebraMap F K))))
      = infiniteCompletionComap F w
          (infiniteCompletionAut (w.comap (algebraMap F K)) (AlgEquiv.restrictNormalHom F σ)
            (restrictNormalHom_smul_comap F w hσ) (infiniteCoe y (w.comap (algebraMap F K))))
    rw [h1, infiniteCompletionAut_infiniteCoe, infiniteCompletionAut_infiniteCoe, h2,
      algebraMap_restrictNormalHom F]

omit [NumberField k] [NumberField F] [NumberField K] [IsGalois k F] [IsGalois k K] in
/-- The automorphism of a completion at an infinite place attached to an automorphism over the
middle field does not depend on which base field the automorphism is read over. -/
theorem infiniteCompletionAut_restrictScalars (σ : Gal(K/F)) (hσ : σ • w = w)
    (hσ' : σ.restrictScalars k • w = w) (z : w.Completion) :
    infiniteCompletionAut w (σ.restrictScalars k) hσ' z = infiniteCompletionAut w σ hσ z := rfl

variable (F) in
omit [NumberField k] in
/-- **A unit of the completion at an infinite place fixed by the decomposition group of the top
field over the middle field comes from the completion of the middle field at the place below.**
The elements of the completion fixed by the whole decomposition group over the middle field are the
elements of the completion of the middle field. -/
theorem exists_infiniteUnitsComapHom_eq_of_ker (x : (w.Completion)ˣ)
    (hx : ∀ n : ↥(stabilizerRestrictPlaceInfinite (k := k) F w).ker,
      (n : ↥(stabilizer Gal(K/k) w)) • x = x) :
    ∃ b : ((w.comap (algebraMap F K)).Completion)ˣ, infiniteUnitsComapHom F w b = x := by
  haveI : IsGalois F K := IsGalois.tower_top_of_isGalois k F K
  have hfix : ∀ σ : ↥(stabilizer Gal(K/F) w),
      smulUnitsAut σ (Additive.ofMul x) = Additive.ofMul x := by
    intro σ
    have hσ : σ.1 • w = w := mem_stabilizer_iff.mp σ.2
    have hσ' : (σ.1.restrictScalars k) • w = w := hσ
    have hker : (⟨σ.1.restrictScalars k, mem_stabilizer_iff.mpr hσ'⟩ :
        ↥(stabilizer Gal(K/k) w)) ∈ (stabilizerRestrictPlaceInfinite (k := k) F w).ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext (restrictNormalHom_restrictScalars k F σ.1)
    have h : infiniteCompletionAut w (σ.1.restrictScalars k) hσ' (x : w.Completion)
        = (x : w.Completion) := congrArg Units.val (hx ⟨_, hker⟩)
    refine Additive.toMul.injective (Units.ext ?_)
    rw [coe_smulUnitsAut_apply, toMul_ofMul, stabilizer_smul_infiniteCompletion_def,
      ← infiniteCompletionAut_restrictScalars (k := k) w σ.1 hσ hσ']
    exact h
  obtain ⟨c, hc⟩ := (mem_range_infiniteUnitsComap_iff F w (Additive.ofMul x)).mpr hfix
  refine ⟨Additive.toMul c, Additive.ofMul.injective ?_⟩
  rw [ofMul_infiniteUnitsComapHom, ofMul_toMul]
  exact hc

variable (F) in
omit [NumberField F] [NumberField K] in
/-- **A unit of the middle field, read in the local units of the top field, is the image of its
reading in the local units of the middle field.** -/
theorem infiniteUnitsComap_infiniteUnitHom (y : Fˣ) :
    infiniteUnitsComap F w (Additive.ofMul (infiniteUnitHom (w.comap (algebraMap F K)) y))
      = Additive.ofMul (infiniteUnitHom w (Units.map (algebraMap F K : F →* K) y)) := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [coe_infiniteUnitsComap, toMul_ofMul, coe_infiniteUnitHom, toMul_ofMul, coe_infiniteUnitHom,
    algebraMap_infiniteCompletion F w]
  exact infiniteCompletionComap_coe F w _

variable (F) in
omit [NumberField k] [NumberField F] [NumberField K] [IsGalois k F] [IsGalois k K] in
/-- **A unit of the base field, read in the local units of the top field, is the image of its
reading in the local units of the middle field.** -/
theorem infiniteUnitsComapHom_infiniteUnitHom (q : kˣ) :
    infiniteUnitsComapHom F w (infiniteUnitHom (w.comap (algebraMap F K))
        (Units.map (algebraMap k F : k →* F) q))
      = infiniteUnitHom w (Units.map (algebraMap k K : k →* K) q) := by
  refine Additive.ofMul.injective ?_
  rw [ofMul_infiniteUnitsComapHom, infiniteUnitsComap_infiniteUnitHom F w,
    units_map_algebraMap_tower]

/-! ### The descent of the local hypothesis -/

set_option maxHeartbeats 4000000 in
variable (F) in
/-- **A family of units of the base field whose inflation is a local coboundary at an infinite
place of the top field is a local coboundary at the place of the middle field below it.**  The
decomposition group above maps onto the decomposition group below, the local units below are the
local units above fixed by the kernel, and Hilbert's theorem 90 for the kernel makes the
trivialising cochain constant there, so the cochain descends. -/
theorem exists_sub_add_eq_infiniteUnits_descent {a : Gal(F/k) → Gal(F/k) → kˣ}
    (ha : ∀ x y z : Gal(F/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (h : ∃ c : ↥(stabilizer Gal(K/k) w) → Additive (w.Completion)ˣ,
        ∀ s t : ↥(stabilizer Gal(K/k) w),
          Additive.ofMul (infiniteUnitHom w (Units.map (algebraMap k K : k →* K)
              (a (AlgEquiv.restrictNormalHom F s.1) (AlgEquiv.restrictNormalHom F t.1))))
            = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ c : ↥(stabilizer Gal(F/k) (w.comap (algebraMap F K))) →
          Additive ((w.comap (algebraMap F K)).Completion)ˣ,
      ∀ s t : ↥(stabilizer Gal(F/k) (w.comap (algebraMap F K))),
        Additive.ofMul (infiniteUnitHom (w.comap (algebraMap F K))
            (Units.map (algebraMap k F : k →* F) (a s.1 t.1)))
          = smulUnitsAut s (c t) - c (s * t) + c s := by
  obtain ⟨c, hc⟩ := h
  -- the units of the base field are fixed by the decomposition group below
  have hfix : ∀ (s : ↥(stabilizer Gal(F/k) (w.comap (algebraMap F K)))) (q : kˣ),
      s • infiniteUnitHom (w.comap (algebraMap F K)) (Units.map (algebraMap k F : k →* F) q)
        = infiniteUnitHom (w.comap (algebraMap F K)) (Units.map (algebraMap k F : k →* F) q) := by
    intro s q
    have h := congrArg Additive.toMul
      (smulUnitsAut_infiniteUnitHom_algebraMap (k := k) (w.comap (algebraMap F K)) s q)
    rwa [toMul_smulUnitsAut_stabilizerInfinite, toMul_ofMul] at h
  -- the embedding of the units of the base field into the local units is multiplicative
  have hmul : ∀ x y : kˣ,
      infiniteUnitHom (w.comap (algebraMap F K)) (Units.map (algebraMap k F : k →* F) x)
          * infiniteUnitHom (w.comap (algebraMap F K)) (Units.map (algebraMap k F : k →* F) y)
        = infiniteUnitHom (w.comap (algebraMap F K))
            (Units.map (algebraMap k F : k →* F) (x * y)) := by
    intro x y
    rw [map_mul, map_mul]
  -- the family is a two-cocycle downstairs
  have hcoc : IsMulCocycle₂ (fun p : ↥(stabilizer Gal(F/k) (w.comap (algebraMap F K)))
      × ↥(stabilizer Gal(F/k) (w.comap (algebraMap F K))) =>
        infiniteUnitHom (w.comap (algebraMap F K))
          (Units.map (algebraMap k F : k →* F) (a p.1.1 p.2.1))) := by
    intro g h j
    simp only [Subgroup.coe_mul]
    rw [hfix, hmul, hmul, ha g.1 h.1 j.1]
  -- the inclusion of the local units below intertwines the two actions
  have hjmap : ∀ (s : ↥(stabilizer Gal(K/k) w))
      (b : ((w.comap (algebraMap F K)).Completion)ˣ),
      s • infiniteUnitsComapHom F w b
        = infiniteUnitsComapHom F w (stabilizerRestrictPlaceInfinite F w s • b) := by
    intro s b
    refine Units.ext ?_
    simp only [val_stabilizer_smul_infiniteUnits, coe_infiniteUnitsComapHom,
      stabilizer_smul_infiniteCompletion_def, algebraMap_infiniteCompletion F w]
    exact infiniteCompletionAut_infiniteCompletionComap_restrict F w s.1
      (mem_stabilizer_iff.mp s.2) _
  -- the trivialising cochain upstairs, written multiplicatively
  have hcb : coboundary₂ (fun s : ↥(stabilizer Gal(K/k) w) => Additive.toMul (c s))
      = fun p : ↥(stabilizer Gal(K/k) w) × ↥(stabilizer Gal(K/k) w) =>
        infiniteUnitsComapHom F w (infiniteUnitHom (w.comap (algebraMap F K))
          (Units.map (algebraMap k F : k →* F)
            (a (stabilizerRestrictPlaceInfinite F w p.1).1
              (stabilizerRestrictPlaceInfinite F w p.2).1))) := by
    funext p
    obtain ⟨s, t⟩ := p
    rw [coboundary₂_apply, infiniteUnitsComapHom_infiniteUnitHom F w,
      coe_stabilizerRestrictInfinite, coe_stabilizerRestrictInfinite]
    have h := congrArg Additive.toMul (hc s t)
    rw [toMul_ofMul, toMul_add, toMul_sub, toMul_smulUnitsAut_stabilizerInfinite] at h
    exact h.symm
  obtain ⟨d, hd⟩ := exists_coboundary₂_eq_of_comap
    (stabilizerRestrictPlaceInfinite_surjective F w) (infiniteUnitsComapHom_injective F w) hjmap
    (exists_infiniteUnitsComapHom_eq_of_ker F w)
    (fun e he => isMulCoboundary₁_of_isMulCocycle₁_stabilizerInfinite k w _ e he) hcoc hcb
  refine ⟨fun q => Additive.ofMul (d q), fun s t => ?_⟩
  refine Additive.toMul.injective ?_
  rw [toMul_ofMul, toMul_add, toMul_sub, toMul_smulUnitsAut_stabilizerInfinite, toMul_ofMul,
    toMul_ofMul, toMul_ofMul]
  have h := congrFun hd (s, t)
  rw [coboundary₂_apply] at h
  exact h.symm

end TowerDescent

end InverseGalois.CFT
