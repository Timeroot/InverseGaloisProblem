/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CrossedProductInflate
import InverseGalois.CFT.GroupCohomology.Inflation
import InverseGalois.CFT.Profinite.Hilbert90
import InverseGalois.CFT.Units.DecompositionRestrict

/-!
# A smooth two cocycle with values in the units comes from a finite level

A smooth two cochain of the Galois group of an arbitrary Galois extension is constant on the cosets
of an open normal subgroup, and the subgroups fixing a finite Galois intermediate field are cofinal
among those.  The values of a smooth two cocycle are fixed by the subgroup it is constant for, so
for such a level they lie in the level field itself, and they are units there because the level is
a field and they are nonzero.

Restriction to the level is surjective with that subgroup as kernel, so a cocycle constant on the
cosets of the subgroup only depends on the restrictions of its two arguments.  Choosing a preimage
of each automorphism of the level therefore produces a two cocycle of the level with values in its
units, whose inflation is the cocycle one started with.

Inflation from a level is moreover injective on cohomology classes.  A trivialising cochain of the
inflated cocycle can be corrected to be constant on the cosets of the subgroup fixing the level and
to take values fixed by it, the correction being supplied by Hilbert's theorem ninety for the
Galois group over the level, which is reached from the group over the base by restriction of
scalars along the tower.  The corrected cochain then descends to the level and trivialises the
cocycle there.

## Main results

* `InverseGalois.CFT.mem_of_isMulCocycle₂_of_smooth`: the values of a smooth two cocycle with
  values in the units of the extension lie in every intermediate field whose fixing subgroup the
  cocycle is constant for.
* `InverseGalois.CFT.isSmooth₂_inflateCocycle`: **a cocycle inflated from a finite Galois level is
  smooth.**
* `InverseGalois.CFT.inflateCocycle_injective`: **inflation of two cochains from a finite Galois
  level is injective.**
* `InverseGalois.CFT.exists_levelCocycle₂`: **a two cocycle constant on the cosets of a finite
  Galois level is inflated from a two cocycle of that level with values in its units.**
* `InverseGalois.CFT.exists_smul_div_eq_of_mem_fixingSubgroup`: **Hilbert's theorem ninety relative
  to an intermediate field.**
* `InverseGalois.CFT.isMulCoboundary₂_of_smoothH2Mk_eq_one`: **a two cochain of a finite Galois
  level whose inflation is trivial in the cohomology of the whole Galois group is already a
  coboundary at that level.**
* `InverseGalois.CFT.exists_isGalois_levelCocycle₂`: **every class of the second cohomology of an
  infinite Galois group with values in the units of the extension is inflated from a finite Galois
  level.**

## Tags

infinite Galois theory, Krull topology, Galois cohomology, inflation, smooth cochain, crossed
product
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

universe u

namespace InverseGalois.CFT

open groupCohomology

section Level

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]

/-- The values of a smooth two cocycle with values in the units of the extension lie in every
intermediate field whose fixing subgroup the cocycle is constant for. -/
theorem mem_of_isMulCocycle₂_of_smooth {N : Subgroup Gal(K/k)} (hN : IsOpenNormal N)
    {a : Gal(K/k) × Gal(K/k) → Kˣ} (ha : IsMulCocycle₂ a)
    (hcon : ∀ x y : Gal(K/k), ∀ n ∈ N, ∀ m ∈ N, a (x * n, y * m) = a (x, y))
    (E : IntermediateField k K) (hle : E.fixingSubgroup ≤ N) (g h : Gal(K/k)) :
    (a (g, h) : K) ∈ E := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hfix := smul_eq_self_of_isMulCocycle₂_of_smooth ha hN.normal hcon (hle hσ) g h
  simpa using congrArg (Units.val (α := K)) hfix

variable (E : IntermediateField k K) [FiniteDimensional k E] [IsGalois k E]

omit [IsGalois k K] [FiniteDimensional k E] in
/-- Restriction to a finite Galois level kills the subgroup fixing it. -/
theorem restrictNormalHom_eq_one_of_mem_fixingSubgroup {c : Gal(K/k)} (hc : c ∈ E.fixingSubgroup) :
    AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E c = 1 := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker E]
  exact hc

omit [IsGalois k K] [FiniteDimensional k E] in
/-- A cochain inflated from a finite Galois level is unchanged when either entry is multiplied on
the right by an element of the subgroup fixing the level. -/
theorem inflateCocycle_apply_mul_of_mem_fixingSubgroup (w : Gal(↥E/k) × Gal(↥E/k) → (↥E)ˣ)
    (x y n : Gal(K/k)) (hn : n ∈ E.fixingSubgroup) (m : Gal(K/k)) (hm : m ∈ E.fixingSubgroup) :
    inflateCocycle (L := ↥E) K w (x * n, y * m) = inflateCocycle (L := ↥E) K w (x, y) := by
  have hx : AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E (x * n)
      = AlgEquiv.restrictNormalHom E x := by
    rw [map_mul, restrictNormalHom_eq_one_of_mem_fixingSubgroup E hn, mul_one]
  have hy : AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E (y * m)
      = AlgEquiv.restrictNormalHom E y := by
    rw [map_mul, restrictNormalHom_eq_one_of_mem_fixingSubgroup E hm, mul_one]
  show Units.map _ (w (AlgEquiv.restrictNormalHom E (x * n), AlgEquiv.restrictNormalHom E (y * m)))
    = Units.map _ (w (AlgEquiv.restrictNormalHom E x, AlgEquiv.restrictNormalHom E y))
  rw [hx, hy]

omit [IsGalois k K] in
/-- **A cocycle inflated from a finite Galois level is smooth.** -/
theorem isSmooth₂_inflateCocycle (w : Gal(↥E/k) × Gal(↥E/k) → (↥E)ˣ) :
    IsSmooth₂ (inflateCocycle (L := ↥E) K w) :=
  ⟨E.fixingSubgroup, isOpenNormal_fixingSubgroup E,
    inflateCocycle_apply_mul_of_mem_fixingSubgroup E w⟩

omit [FiniteDimensional k E] in
/-- **Inflation of two cochains from a finite Galois level is injective**, restriction to the level
being surjective and the inclusion of the level being injective. -/
theorem inflateCocycle_injective :
    Function.Injective (inflateCocycle (K := k) (L := ↥E) K) := by
  intro w₁ w₂ hw
  have hinj : Function.Injective (Units.map (algebraMap ↥E K : ↥E →* K)) :=
    Units.map_injective (algebraMap ↥E K).injective
  refine funext fun p => hinj ?_
  obtain ⟨σ, hσ⟩ := restrictNormalHom_surjective_level (k := k) (K := K) E p.1
  obtain ⟨τ, hτ⟩ := restrictNormalHom_surjective_level (k := k) (K := K) E p.2
  have h : Units.map (algebraMap ↥E K : ↥E →* K)
        (w₁ (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E σ,
          AlgEquiv.restrictNormalHom E τ))
      = Units.map (algebraMap ↥E K : ↥E →* K)
        (w₂ (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E σ,
          AlgEquiv.restrictNormalHom E τ)) := congrFun hw (σ, τ)
  rwa [hσ, hτ] at h

omit [FiniteDimensional k E] in
/-- **A two cocycle constant on the cosets of a finite Galois level is inflated from a two cocycle
of that level with values in its units.** -/
theorem exists_levelCocycle₂ {N : Subgroup Gal(K/k)} (hN : IsOpenNormal N)
    {a : Gal(K/k) × Gal(K/k) → Kˣ} (ha : IsMulCocycle₂ a)
    (hcon : ∀ x y : Gal(K/k), ∀ n ∈ N, ∀ m ∈ N, a (x * n, y * m) = a (x, y))
    (hle : E.fixingSubgroup ≤ N) :
    ∃ w : Gal(↥E/k) × Gal(↥E/k) → (↥E)ˣ, IsMulCocycle₂ w ∧
      inflateCocycle (L := ↥E) K w = a := by
  classical
  have hmem : ∀ g h : Gal(K/k), (a (g, h) : K) ∈ E :=
    mem_of_isMulCocycle₂_of_smooth hN ha hcon E hle
  -- a cocycle constant on the cosets of the fixing subgroup only depends on the restrictions
  have hres : ∀ g h g' h' : Gal(K/k),
      AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E g = AlgEquiv.restrictNormalHom E g' →
      AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E h = AlgEquiv.restrictNormalHom E h' →
      a (g, h) = a (g', h') := by
    intro g h g' h' hg hh
    have hkg : g⁻¹ * g' ∈ E.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker E, MonoidHom.mem_ker, map_mul, map_inv, hg,
        inv_mul_cancel]
    have hkh : h⁻¹ * h' ∈ E.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker E, MonoidHom.mem_ker, map_mul, map_inv, hh,
        inv_mul_cancel]
    have hval := hcon g h _ (hle hkg) _ (hle hkh)
    rwa [mul_inv_cancel_left, mul_inv_cancel_left, eq_comm] at hval
  -- a section of the restriction to the finite Galois level
  choose lift hlift using restrictNormalHom_surjective_level (k := k) (K := K) E
  have hne : ∀ p : Gal(↥E/k) × Gal(↥E/k),
      (⟨(a (lift p.1, lift p.2) : K), hmem _ _⟩ : ↥E) ≠ 0 := by
    intro p hp
    exact (a (lift p.1, lift p.2)).ne_zero (congrArg Subtype.val hp)
  obtain ⟨w, hwval⟩ : ∃ w : Gal(↥E/k) × Gal(↥E/k) → (↥E)ˣ,
      ∀ p : Gal(↥E/k) × Gal(↥E/k), ((w p : ↥E) : K) = (a (lift p.1, lift p.2) : K) :=
    ⟨fun p => Units.mk0 _ (hne p), fun _ => rfl⟩
  -- an automorphism of the extension acts on the level through its restriction
  have hsmul : ∀ (g : Gal(K/k)) (x : ↥E),
      ((AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E g • x : ↥E) : K) = g (x : K) :=
    fun g x => AlgEquiv.restrictNormal_commutes g ↥E x
  have hKsmul : ∀ (g : Gal(K/k)) (x : Kˣ), ((g • x : Kˣ) : K) = g (x : K) := fun _ _ => rfl
  have hliftsmul : ∀ (τ : Gal(↥E/k)) (x : ↥E), ((τ • x : ↥E) : K) = (lift τ) ((x : K)) := by
    intro τ x
    have h := hsmul (lift τ) x
    rwa [hlift] at h
  refine ⟨w, ?_, ?_⟩
  · intro σ τ ρ
    refine Units.ext (Subtype.ext ?_)
    have hστ : AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E (lift (σ * τ))
        = AlgEquiv.restrictNormalHom E (lift σ * lift τ) := by
      rw [hlift, map_mul, hlift, hlift]
    have hτρ : AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E (lift (τ * ρ))
        = AlgEquiv.restrictNormalHom E (lift τ * lift ρ) := by
      rw [hlift, map_mul, hlift, hlift]
    have hleft : (((w (σ * τ, ρ) * w (σ, τ) : (↥E)ˣ) : ↥E) : K)
        = (a (lift σ * lift τ, lift ρ) : K) * (a (lift σ, lift τ) : K) := by
      show ((w (σ * τ, ρ) : ↥E) : K) * ((w (σ, τ) : ↥E) : K) = _
      rw [hwval, hwval, hres _ _ _ _ hστ rfl]
    have hright : (((σ • w (τ, ρ) * w (σ, τ * ρ) : (↥E)ˣ) : ↥E) : K)
        = (lift σ) ((a (lift τ, lift ρ) : K)) * (a (lift σ, lift τ * lift ρ) : K) := by
      show ((σ • (w (τ, ρ) : ↥E) : ↥E) : K) * ((w (σ, τ * ρ) : ↥E) : K) = _
      rw [hliftsmul, hwval, hwval, hres _ _ _ _ rfl hτρ]
    have hcoc := congrArg (Units.val (α := K)) (ha (lift σ) (lift τ) (lift ρ))
    rw [Units.val_mul, Units.val_mul, hKsmul] at hcoc
    rw [hleft, hright]
    exact hcoc
  · refine funext fun p => Units.ext ?_
    have hp := hwval (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E p.1,
      AlgEquiv.restrictNormalHom E p.2)
    show ((w (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E p.1,
      AlgEquiv.restrictNormalHom E p.2) : ↥E) : K) = (a p : K)
    rw [hp]
    exact congrArg (Units.val (α := K)) (hres _ _ _ _ (hlift _) (hlift _))

end Level

section Relative

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  (E : IntermediateField k K)

omit [IsGalois k K] in
/-- An automorphism over an intermediate field fixes that field. -/
theorem galRestrictScalarsHom_mem_fixingSubgroup (σ : Gal(K/↥E)) :
    galRestrictScalarsHom k ↥E K σ ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro z hz
  exact σ.commutes ⟨z, hz⟩

omit [IsGalois k K] in
/-- Every element of the subgroup fixing an intermediate field is an automorphism over that field,
read as an automorphism over the base. -/
theorem exists_galRestrictScalarsHom_eq {x : Gal(K/k)} (hx : x ∈ E.fixingSubgroup) :
    ∃ σ : Gal(K/↥E), galRestrictScalarsHom k ↥E K σ = x :=
  ⟨IntermediateField.fixingSubgroupEquiv E ⟨x, hx⟩, rfl⟩

/-- **Hilbert's theorem ninety relative to an intermediate field**: a smooth cochain of the Galois
group of the extension which obeys the one cocycle law on the subgroup fixing an intermediate field
is, on that subgroup, the coboundary of a single unit. -/
theorem exists_smul_div_eq_of_mem_fixingSubgroup {f : Gal(K/k) → Kˣ} (hs : IsSmooth₁ f)
    (hc : ∀ x ∈ E.fixingSubgroup, ∀ y ∈ E.fixingSubgroup, f (x * y) = x • f y * f x) :
    ∃ t : Kˣ, ∀ x ∈ E.fixingSubgroup, x • t / t = f x := by
  have hsmul : ∀ (σ : Gal(K/↥E)) (v : Kˣ), galRestrictScalarsHom k ↥E K σ • v = σ • v :=
    fun _ _ => rfl
  have hcoc : IsMulCocycle₁ fun σ : Gal(K/↥E) => f (galRestrictScalarsHom k ↥E K σ) := by
    intro σ τ
    show f (galRestrictScalarsHom k ↥E K (σ * τ)) = _
    rw [map_mul, hc _ (galRestrictScalarsHom_mem_fixingSubgroup E σ) _
      (galRestrictScalarsHom_mem_fixingSubgroup E τ), hsmul]
  have hsm : IsSmooth₁ fun σ : Gal(K/↥E) => f (galRestrictScalarsHom k ↥E K σ) := by
    obtain ⟨N, hN, hcon⟩ := hs
    obtain ⟨N', hN', hle⟩ := isSmoothHom_galRestrictScalarsHom k ↥E K N hN
    refine ⟨N', hN', fun σ n hn => ?_⟩
    show f (galRestrictScalarsHom k ↥E K (σ * n)) = f (galRestrictScalarsHom k ↥E K σ)
    rw [map_mul]
    exact hcon _ _ (hle hn)
  obtain ⟨t, ht⟩ := isMulCoboundary₁_of_isMulCocycle₁_smooth hcoc hsm
  refine ⟨t, fun x hx => ?_⟩
  obtain ⟨σ, rfl⟩ := exists_galRestrictScalarsHom_eq E hx
  rw [hsmul]
  exact ht σ

end Relative

section Injective

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  (E : IntermediateField k K) [FiniteDimensional k E] [IsGalois k E]

omit [FiniteDimensional k E] in
/-- **Inflation from a finite Galois level is injective in degree two**: a two cochain of the level
whose inflation is the coboundary of a smooth cochain is already a coboundary at the level.  The
trivialising cochain is corrected to be constant on the cosets of the subgroup fixing the level and
to take values fixed by it, which is possible by Hilbert's theorem ninety relative to the level, and
the corrected cochain then descends. -/
theorem isMulCoboundary₂_of_coboundary₂_inflateCocycle
    {v : Gal(↥E/k) × Gal(↥E/k) → (↥E)ˣ} {u : Gal(K/k) → Kˣ} (hus : IsSmooth₁ u)
    (hu : coboundary₂ u = inflateCocycle (L := ↥E) K v) : IsMulCoboundary₂ v := by
  classical
  haveI : E.fixingSubgroup.Normal := normal_fixingSubgroup E
  have hinfl := inflateCocycle_apply_mul_of_mem_fixingSubgroup E v
  -- the failure of the trivialising cochain to be constant on a coset is a coboundary there
  have hH1 : ∃ t : Kˣ, ∀ x ∈ E.fixingSubgroup, x • t / t = u x / u 1 := by
    refine exists_smul_div_eq_of_mem_fixingSubgroup E ?_
      (isMulCocycle₁_div_one_of_inflated hinfl hu)
    obtain ⟨N, hN, hcon⟩ := hus
    refine ⟨N, hN, fun x n hn => ?_⟩
    show u (x * n) / u 1 = u x / u 1
    rw [hcon x n hn]
  obtain ⟨u', hcoset, hinv, hcb⟩ := exists_coboundary₂_inflated_of_cochain hinfl hu hH1
  -- the corrected cochain takes its values in the level and is constant on its cosets
  have hmemE : ∀ g : Gal(K/k), (u' g : K) ∈ E := by
    intro g
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    simpa using congrArg (Units.val (α := K)) (hinv g σ hσ)
  have hres : ∀ g h : Gal(K/k),
      AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E g = AlgEquiv.restrictNormalHom E h →
      u' g = u' h := by
    intro g h hgh
    have hker : g⁻¹ * h ∈ E.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker E, MonoidHom.mem_ker, map_mul, map_inv, hgh,
        inv_mul_cancel]
    have hval := hcoset g (g⁻¹ * h) hker
    rwa [mul_inv_cancel_left, eq_comm] at hval
  -- the descent of the corrected cochain to the level
  choose lift hlift using restrictNormalHom_surjective_level (k := k) (K := K) E
  have hcst : ∀ (τ : Gal(↥E/k)) (g : Gal(K/k)),
      AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E g = τ → u' (lift τ) = u' g :=
    fun τ g hgτ => hres _ _ (by rw [hlift, hgτ])
  have hne : ∀ τ : Gal(↥E/k), (⟨(u' (lift τ) : K), hmemE _⟩ : ↥E) ≠ 0 := by
    intro τ hτ
    exact (u' (lift τ)).ne_zero (congrArg Subtype.val hτ)
  obtain ⟨t, htval⟩ : ∃ t : Gal(↥E/k) → (↥E)ˣ,
      ∀ τ, Units.map (algebraMap ↥E K : ↥E →* K) (t τ) = u' (lift τ) :=
    ⟨fun τ => Units.mk0 _ (hne τ), fun _ => Units.ext rfl⟩
  refine isMulCoboundary₂_iff.2 ⟨t, inflateCocycle_injective E ?_⟩
  rw [← hcb]
  refine funext fun p => ?_
  obtain ⟨g, h⟩ := p
  show Units.map (algebraMap ↥E K : ↥E →* K) (coboundary₂ t
      (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E g, AlgEquiv.restrictNormalHom E h))
    = coboundary₂ u' (g, h)
  rw [coboundary₂_apply, coboundary₂_apply, map_mul, map_div, smul_units_map_algebraMap, htval,
    htval, htval, hcst _ h rfl, hcst _ (g * h) (map_mul _ _ _), hcst _ g rfl]

/-- **A two cochain of a finite Galois level whose inflation is trivial in the cohomology of the
whole Galois group is already a coboundary at that level.** -/
theorem isMulCoboundary₂_of_smoothH2Mk_eq_one {v : Gal(↥E/k) × Gal(↥E/k) → (↥E)ˣ}
    (hv : IsMulCocycle₂ v)
    (h : smoothH2Mk (inflateCocycle (L := ↥E) K v) (isMulCocycle₂_inflateCocycle (L' := K) hv)
      (isSmooth₂_inflateCocycle E v) = 1) :
    IsMulCoboundary₂ v := by
  obtain ⟨u, hus, hu⟩ := (smoothH2Mk_eq_one_iff _ _).1 h
  exact isMulCoboundary₂_of_coboundary₂_inflateCocycle E hus hu

end Injective

section Class

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]

/-- **Every class of the second cohomology of an infinite Galois group with values in the units of
the extension is inflated from a two cocycle of a finite Galois level.** -/
theorem exists_isGalois_levelCocycle₂ (z : SmoothH2 Gal(K/k) Kˣ) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E) (_ : IsGalois k E)
      (w : Gal(↥E/k) × Gal(↥E/k) → (↥E)ˣ) (hw : IsMulCocycle₂ w),
      smoothH2Mk (inflateCocycle (L := ↥E) K w) (isMulCocycle₂_inflateCocycle (L' := K) hw)
        (isSmooth₂_inflateCocycle E w) = z := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective z
  obtain ⟨N, hN, hcon⟩ := hs
  obtain ⟨E, hfin, hgal, hle⟩ := exists_fixingSubgroup_le hN
  haveI := hfin
  haveI := hgal
  obtain ⟨w, hw, hwa⟩ := exists_levelCocycle₂ E hN ha hcon hle
  refine ⟨E, hfin, hgal, w, hw, ?_⟩
  congr 1

end Class

end InverseGalois.CFT
