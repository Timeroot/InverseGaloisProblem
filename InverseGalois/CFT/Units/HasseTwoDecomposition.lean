/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Res
import InverseGalois.CFT.Units.HasseTwo
import InverseGalois.CFT.Units.InfiniteDecomposition
import InverseGalois.CFT.Units.InfiniteTowerDescent
import InverseGalois.CFT.Units.TowerDescent

/-!
# The decomposition subgroups and the local conditions at a level, in degree two

A class of the second cohomology of the Galois group of an arbitrary Galois extension of a number
field is represented by a cocycle inflated from a finite Galois level, and the local conditions of
a local-global principle in degree two are stated at the places of that level.  What a family of
decomposition subgroups of the whole group provides is instead a trivialisation on the stabiliser
of a nonzero prime of the ring of integers of the top field, or of an infinite place of it.  This
file turns the second into the first at both kinds of place, and deduces that a class dying on
every decomposition subgroup is trivial.

The trivialising cochain on a decomposition subgroup is smooth, so it is constant on the cosets of
the automorphisms fixing some finite Galois level, and the decomposition subgroup maps onto the
decomposition group of that level at the place below the prime.  The cochain therefore descends to
a cochain of the decomposition group of a level large enough to contain the level one started from,
where its values may be read in the units of the completion; descending the resulting local
coboundary along the tower of the two levels gives the local condition at the smaller one.

## Main definitions

* `InverseGalois.CFT.stabilizerRestrictPrime`: **the decomposition group at a nonzero prime maps to
  the decomposition group of a level at the place below it.**
* `InverseGalois.CFT.stabilizerRestrictInfinitePlace`: the same at an infinite place.

## Main results

* `InverseGalois.CFT.stabilizerRestrictPrime_surjective`: **that map is onto.**
* `InverseGalois.CFT.exists_fixingSubgroup_le_subgroup`: an open normal subgroup of a subgroup of
  the Galois group contains the automorphisms of the subgroup fixing a finite Galois level.
* `InverseGalois.CFT.exists_sub_add_eq_adicUnits_of_resH2`: **a class of the second cohomology
  dying on every decomposition subgroup at a nonzero prime splits at every finite place of a level
  it is inflated from.**
* `InverseGalois.CFT.stabilizerRestrictInfinitePlace_surjective`: **the decomposition group at an
  infinite place maps onto the decomposition group of a level at the place below it.**
* `InverseGalois.CFT.exists_sub_add_eq_infiniteUnits_of_resH2`: **a class of the second cohomology
  dying on every decomposition subgroup at an infinite place splits at every infinite place of a
  level it is inflated from.**
* `InverseGalois.CFT.eq_one_of_mem_sha2`: **a class of the second cohomology with roots of unity
  coefficients dying on every decomposition subgroup of the absolute Galois group is trivial.**

## Tags

number field, Galois cohomology, second cohomology, decomposition group, local-global principle,
Tate-Shafarevich group
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

open IsDedekindDomain MulAction NumberField groupCohomology

open scoped Pointwise

namespace InverseGalois.CFT

/-! ### The decomposition group at a prime and at the place of a level below it -/

section RestrictPrime

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  (L : IntermediateField k Ω) [NumberField ↥L] [IsGalois k ↥L]
  {P : Ideal (𝓞 Ω)} [P.IsPrime] {v : HeightOneSpectrum (𝓞 ↥L)}
  (hv : v.asIdeal = Ideal.under (𝓞 ↥L) P)

include hv

omit [IsGalois k Ω] [NumberField ↥L] [P.IsPrime] in
/-- **An automorphism fixing a nonzero prime of the integers of the whole extension fixes the place
of a level below it.** -/
theorem restrictNormalHom_smul_place_of_smul_eq {σ : Gal(Ω/k)} (hσ : σ • P = P) :
    AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L σ • v = v := by
  refine HeightOneSpectrum.ext ?_
  rw [asIdeal_smul, hv, ← under_smul_ringOfIntegers ↥L σ P, hσ]

/-- **The decomposition group at a nonzero prime maps to the decomposition group of a level at the
place below it**, by restriction of automorphisms. -/
noncomputable def stabilizerRestrictPrime :
    ↥(stabilizer Gal(Ω/k) P) →* ↥(stabilizer Gal(↥L/k) v) where
  toFun σ := ⟨AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L σ.1,
    mem_stabilizer_iff.mpr
      (restrictNormalHom_smul_place_of_smul_eq L hv (mem_stabilizer_iff.mp σ.2))⟩
  map_one' := Subtype.ext (map_one (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L))
  map_mul' σ τ := Subtype.ext (map_mul (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L) σ.1 τ.1)

omit [IsGalois k Ω] [NumberField ↥L] [P.IsPrime] in
@[simp]
theorem coe_stabilizerRestrictPrime (σ : ↥(stabilizer Gal(Ω/k) P)) :
    (stabilizerRestrictPrime L hv σ : Gal(↥L/k))
      = AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L σ.1 := rfl

omit [NumberField ↥L] in
/-- **The decomposition group at a nonzero prime maps onto the decomposition group of a level at
the place below it.**  An automorphism of the level fixing the place lifts to the whole extension;
the lift moves the prime to another prime above the same place, and the Galois group over the level
moves it back. -/
theorem stabilizerRestrictPrime_surjective :
    Function.Surjective (stabilizerRestrictPrime L hv) := by
  haveI : IsGalois ↥L Ω := IsGalois.tower_top_of_isGalois k ↥L Ω
  intro τ
  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L : Gal(Ω/k) →* Gal(↥L/k)) :=
    AlgEquiv.restrictNormalHom_surjective Ω
  obtain ⟨σ₀, hσ₀⟩ := hsurj τ.1
  have hτv : τ.1 • v = v := mem_stabilizer_iff.mp τ.2
  have h1 : Ideal.under (𝓞 ↥L) (σ₀ • P) = Ideal.under (𝓞 ↥L) P := by
    rw [under_smul_ringOfIntegers ↥L, hσ₀, ← hv, ← asIdeal_smul, hτv, hv]
  obtain ⟨ρ₀, hρ₀⟩ := exists_smul_eq_of_under_eq_ringOfIntegers (F := ↥L) (σ₀ • P) P h1
  have hstab : (ρ₀.restrictScalars k * σ₀) • P = P := by
    rw [mul_smul]
    exact hρ₀.symm
  refine ⟨⟨ρ₀.restrictScalars k * σ₀, mem_stabilizer_iff.mpr hstab⟩, Subtype.ext ?_⟩
  rw [coe_stabilizerRestrictPrime]
  show AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L (ρ₀.restrictScalars k * σ₀) = τ.1
  rw [map_mul, restrictNormalHom_restrictScalars k ↥L ρ₀, one_mul, hσ₀]

omit [IsGalois k Ω] [NumberField ↥L] [P.IsPrime] in
/-- The kernel of the map to the decomposition group of a level consists of the automorphisms
fixing that level. -/
theorem mem_ker_stabilizerRestrictPrime_iff {σ : ↥(stabilizer Gal(Ω/k) P)} :
    σ ∈ (stabilizerRestrictPrime L hv).ker ↔ (σ : Gal(Ω/k)) ∈ L.fixingSubgroup := by
  rw [MonoidHom.mem_ker, ← IntermediateField.restrictNormalHom_ker L, MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end RestrictPrime

/-! ### Smoothness on a subgroup of the Galois group -/

section SmoothLevel

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- **An open normal subgroup of a subgroup of the Galois group contains the automorphisms of the
subgroup which fix a finite Galois level.**  The subgroup carries the subspace topology, so an open
subgroup of it is cut out by a neighbourhood of the identity, and such a neighbourhood contains the
automorphisms fixing a finite Galois level. -/
theorem exists_fixingSubgroup_le_subgroup (D : Subgroup Gal(Ω/k)) {N : Subgroup ↥D}
    (hN : IsOpenNormal N) :
    ∃ E : IntermediateField k Ω, FiniteDimensional k ↥E ∧ IsGalois k ↥E ∧
      ∀ n : ↥D, (n : Gal(Ω/k)) ∈ E.fixingSubgroup → n ∈ N := by
  obtain ⟨U, hUopen, hUeq⟩ := isOpen_induced_iff.1 hN.isOpen
  have h1U : (1 : Gal(Ω/k)) ∈ U := by
    have h1 : (1 : ↥D) ∈ (N : Set ↥D) := N.one_mem
    rw [← hUeq] at h1
    exact h1
  obtain ⟨E, hfin, hnorm, hle⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal k Ω U).1 (hUopen.mem_nhds h1U)
  haveI := hfin
  haveI := hnorm
  obtain ⟨-, hgal⟩ := (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois E).1
    ⟨E.fixingSubgroup_isOpen, normal_fixingSubgroup E⟩
  refine ⟨E, hfin, hgal, fun n hn => ?_⟩
  have hmem : (n : Gal(Ω/k)) ∈ U := hle hn
  show n ∈ (N : Set ↥D)
  rw [← hUeq]
  exact hmem

end SmoothLevel

/-! ### The local condition at a finite place of a level -/

section FiniteBridge

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M]

/-- **A class of the second cohomology dying on every decomposition subgroup at a nonzero prime
splits at every finite place of a level it is inflated from.**  A prime of the integers of the
whole extension above the place carries a trivialising cochain of its decomposition subgroup; the
cochain is smooth, hence constant on the automorphisms fixing a finite Galois level, and enlarging
the level one started from by that one makes the cochain descend to the decomposition group of a
level.  Descending the resulting local coboundary along the tower of the two levels gives the local
condition at the place of the smaller one. -/
theorem exists_sub_add_eq_adicUnits_of_resH2
    (htriv : ∀ (g : Gal(Ω/k)) (m : M), g • m = m) (ι : M →* kˣ)
    (E : IntermediateField k Ω) [NumberField ↥E] [IsGalois k ↥E]
    {b : Gal(↥E/k) → Gal(↥E/k) → M}
    (hb : ∀ x y z : Gal(↥E/k), b y z * b x (y * z) = b (x * y) z * b x y)
    {A : Gal(Ω/k) × Gal(Ω/k) → M} (hA : IsMulCocycle₂ A) (hAs : IsSmooth₂ A)
    (hAinf : A = fun p : Gal(Ω/k) × Gal(Ω/k) =>
      b (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E p.1)
        (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E p.2))
    (hz : ∀ D ∈ finiteDecompositionSubgroups k Ω, resH2 D (smoothH2Mk A hA hAs) = 1)
    (v : HeightOneSpectrum (𝓞 ↥E)) :
    ∃ c : ↥(stabilizer Gal(↥E/k) v) → Additive (v.adicCompletion ↥E)ˣ,
      ∀ s t : ↥(stabilizer Gal(↥E/k) v),
        Additive.ofMul (adicUnitHom v
            (Units.map (algebraMap k ↥E : k →* ↥E) (ι (b s.1 t.1))))
          = smulUnitsAut s (c t) - c (s * t) + c s := by
  classical
  haveI : FiniteDimensional k ↥E := Module.Finite.of_restrictScalars_finite ℚ k ↥E
  haveI := v.isPrime
  -- a prime of the integers of the whole extension above the place
  obtain ⟨P, -, hPp, hPu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (R := 𝓞 ↥E) (S := 𝓞 Ω) v.asIdeal ⊥ (by simp)
  haveI := hPp
  have hPunder : Ideal.under (𝓞 ↥E) P = v.asIdeal := hPu
  have hPbot : P ≠ ⊥ := by
    intro h
    refine v.ne_bot ?_
    rw [← hPunder, h, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      RingOfIntegers.ker_algebraMap_eq_bot]
  -- the trivialising cochain of the decomposition subgroup there
  obtain ⟨u, hu, hcob⟩ := (resH2_eq_one_iff (stabilizer Gal(Ω/k) P) hA hAs).1
    (hz _ ⟨P, hPp, hPbot, rfl⟩)
  obtain ⟨N, hN, hNu⟩ := hu
  obtain ⟨E₀, hE₀fin, hE₀gal, hE₀N⟩ :=
    exists_fixingSubgroup_le_subgroup (stabilizer Gal(Ω/k) P) hN
  -- a finite Galois level containing both the given one and the level of smoothness
  obtain ⟨E'', hEE'', hE₀E'', hE''fin, hE''gal⟩ :
      ∃ E'' : IntermediateField k Ω, E ≤ E'' ∧ E₀ ≤ E'' ∧ FiniteDimensional k ↥E'' ∧
        IsGalois k ↥E'' := by
    haveI := hE₀fin
    haveI := hE₀gal
    haveI : FiniteDimensional k ↥(E ⊔ E₀) := inferInstance
    refine ⟨E ⊔ E₀, le_sup_left, le_sup_right, inferInstance, ?_⟩
    exact ((InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois (E ⊔ E₀)).1
      ⟨(E ⊔ E₀).fixingSubgroup_isOpen, normal_fixingSubgroup (E ⊔ E₀)⟩).2
  haveI := hE''fin
  haveI := hE''gal
  haveI : NumberField ↥E'' := NumberField.of_module_finite k ↥E''
  letI : Algebra ↥E ↥E'' := (IntermediateField.inclusion hEE'').toRingHom.toAlgebra
  haveI : IsScalarTower k ↥E ↥E'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ↥E ↥E'' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the place of the larger level below the prime
  have hunderE'' : Ideal.under (𝓞 ↥E) (Ideal.under (𝓞 ↥E'') P) = v.asIdeal := by
    rw [Ideal.under_under, hPunder]
  have hE''bot : Ideal.under (𝓞 ↥E'') P ≠ ⊥ := by
    intro h
    refine v.ne_bot ?_
    rw [← hunderE'', h, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      RingOfIntegers.ker_algebraMap_eq_bot]
  haveI : (Ideal.under (𝓞 ↥E'') P).IsPrime := Ideal.IsPrime.under _ P
  let v'' : HeightOneSpectrum (𝓞 ↥E'') := ⟨Ideal.under (𝓞 ↥E'') P, inferInstance, hE''bot⟩
  have hv'' : v''.asIdeal = Ideal.under (𝓞 ↥E'') P := rfl
  have hveq : primeUnder (𝓞 ↥E) v'' = v := HeightOneSpectrum.ext hunderE''
  -- the cochain descends to the decomposition group of the larger level
  have hπsurj : Function.Surjective (stabilizerRestrictPrime E'' hv'') :=
    stabilizerRestrictPrime_surjective E'' hv''
  have hkerN : ∀ n : ↥(stabilizer Gal(Ω/k) P),
      n ∈ (stabilizerRestrictPrime E'' hv'').ker → n ∈ N := fun n hn =>
    hE₀N n (IntermediateField.fixingSubgroup_le hE₀E''
      ((mem_ker_stabilizerRestrictPrime_iff E'' hv'').1 hn))
  have hwd : ∀ x y : ↥(stabilizer Gal(Ω/k) P),
      stabilizerRestrictPrime E'' hv'' x = stabilizerRestrictPrime E'' hv'' y → u x = u y := by
    intro x y h
    obtain ⟨n, hn, rfl⟩ := exists_mem_ker_eq_mul h
    exact (hNu x n (hkerN n hn)).symm
  obtain ⟨c'', hc''⟩ : ∃ c'' : ↥(stabilizer Gal(↥E''/k) v'') → M,
      ∀ x : ↥(stabilizer Gal(Ω/k) P), c'' (stabilizerRestrictPrime E'' hv'' x) = u x :=
    ⟨fun q => u (Function.surjInv hπsurj q), fun x => hwd _ _ (Function.surjInv_eq hπsurj _)⟩
  -- the trivialising identity, read at the larger level
  have hact : ∀ (x : ↥(stabilizer Gal(Ω/k) P)) (m : M), x • m = m := fun x m => htriv x.1 m
  have hcobval : ∀ x y : ↥(stabilizer Gal(Ω/k) P),
      u y / u (x * y) * u x
        = b (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E (x : Gal(Ω/k)))
            (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E (y : Gal(Ω/k))) := by
    intro x y
    have h := congrFun hcob (x, y)
    rw [coboundary₂_apply, hact, hAinf] at h
    exact h
  have hres : ∀ (g : Gal(↥E''/k)) (x : Ω) (hx : x ∈ E) (hx' : x ∈ E''),
      ((AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E'') ↥E g ⟨x, hx⟩ : ↥E) : Ω)
        = ((g ⟨x, hx'⟩ : ↥E'') : Ω) := by
    intro g x hx _
    exact congrArg (fun z : ↥E'' => (z : Ω)) (AlgEquiv.restrictNormal_commutes g ↥E ⟨x, hx⟩)
  have hρ : ∀ g : Gal(Ω/k),
      AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E'') ↥E
          (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E'' g)
        = AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E g :=
    restrictNormalHom_eq_of_res hEE'' hres
  have hcoc'' : ∀ s t : ↥(stabilizer Gal(↥E''/k) v''),
      c'' t / c'' (s * t) * c'' s
        = b (AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E'') ↥E s.1)
            (AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E'') ↥E t.1) := by
    intro s t
    obtain ⟨x, rfl⟩ := hπsurj s
    obtain ⟨y, rfl⟩ := hπsurj t
    rw [← map_mul]
    simp only [hc'']
    rw [hcobval x y]
    simp only [coe_stabilizerRestrictPrime, hρ]
  -- the local coboundary at the place of the larger level
  have hloc'' : ∃ c : ↥(stabilizer Gal(↥E''/k) v'') → Additive (v''.adicCompletion ↥E'')ˣ,
      ∀ s t : ↥(stabilizer Gal(↥E''/k) v''),
        Additive.ofMul (adicUnitHom v'' (Units.map (algebraMap k ↥E'' : k →* ↥E'')
            (ι (b (AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E'') ↥E s.1)
                  (AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E'') ↥E t.1)))))
          = smulUnitsAut s (c t) - c (s * t) + c s := by
    refine ⟨fun s => Additive.ofMul (adicUnitHom v''
      (Units.map (algebraMap k ↥E'' : k →* ↥E'') (ι (c'' s)))), fun s t => ?_⟩
    simp only [smulUnitsAut_adicUnitHom_algebraMap]
    rw [← hcoc'' s t]
    simp only [map_mul, map_div, ofMul_mul, ofMul_div]
  -- and its descent to the place of the smaller one
  have hafin : ∀ x y z : Gal(↥E/k),
      ι (b y z) * ι (b x (y * z)) = ι (b (x * y) z) * ι (b x y) := by
    intro x y z
    rw [← map_mul, ← map_mul, hb]
  have hdesc := exists_sub_add_eq_adicUnits_descent (k := k) (F := ↥E) (K := ↥E'') v''
    (a := fun x y => ι (b x y)) hafin hloc''
  rw [hveq] at hdesc
  exact hdesc

end FiniteBridge

/-! ### The decomposition group at an infinite place and at the place of a level below it -/

section RestrictInfinitePlace

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  (L : IntermediateField k Ω) [NumberField ↥L] [IsGalois k ↥L]
  {w : InfinitePlace Ω} {v : InfinitePlace ↥L} (hv : v = w.comap (algebraMap ↥L Ω))

include hv

omit [IsGalois k Ω] [NumberField ↥L] in
/-- **An automorphism fixing an infinite place of the whole extension fixes the place of a level
below it.** -/
theorem restrictNormalHom_smul_infinitePlace_of_smul_eq {σ : Gal(Ω/k)} (hσ : σ • w = w) :
    AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L σ • v = v := by
  rw [hv, ← comap_smul_algebraMap ↥L σ w, hσ]

/-- **The decomposition group at an infinite place maps to the decomposition group of a level at
the place below it**, by restriction of automorphisms. -/
noncomputable def stabilizerRestrictInfinitePlace :
    ↥(stabilizer Gal(Ω/k) w) →* ↥(stabilizer Gal(↥L/k) v) where
  toFun σ := ⟨AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L σ.1,
    mem_stabilizer_iff.mpr
      (restrictNormalHom_smul_infinitePlace_of_smul_eq L hv (mem_stabilizer_iff.mp σ.2))⟩
  map_one' := Subtype.ext (map_one (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L))
  map_mul' σ τ := Subtype.ext (map_mul (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L) σ.1 τ.1)

omit [IsGalois k Ω] [NumberField ↥L] in
@[simp]
theorem coe_stabilizerRestrictInfinitePlace (σ : ↥(stabilizer Gal(Ω/k) w)) :
    (stabilizerRestrictInfinitePlace L hv σ : Gal(↥L/k))
      = AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L σ.1 := rfl

omit [NumberField ↥L] in
/-- **The decomposition group at an infinite place maps onto the decomposition group of a level at
the place below it.**  An automorphism of the level fixing the place lifts to the whole extension;
the lift moves the place to another place above the same one, and the Galois group over the level
moves it back. -/
theorem stabilizerRestrictInfinitePlace_surjective :
    Function.Surjective (stabilizerRestrictInfinitePlace L hv) := by
  haveI : IsGalois ↥L Ω := IsGalois.tower_top_of_isGalois k ↥L Ω
  intro τ
  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L : Gal(Ω/k) →* Gal(↥L/k)) :=
    AlgEquiv.restrictNormalHom_surjective Ω
  obtain ⟨σ₀, hσ₀⟩ := hsurj τ.1
  have h1 : (σ₀ • w).comap (algebraMap ↥L Ω) = w.comap (algebraMap ↥L Ω) := by
    rw [comap_smul_algebraMap ↥L σ₀ w, hσ₀, ← hv]
    exact mem_stabilizer_iff.mp τ.2
  obtain ⟨ρ₀, hρ₀⟩ :=
    NumberField.InfinitePlace.exists_smul_eq_of_comap_eq (k := ↥L) (K := Ω) h1
  have hstab : (ρ₀.restrictScalars k * σ₀) • w = w := by
    rw [mul_smul]
    exact hρ₀
  refine ⟨⟨ρ₀.restrictScalars k * σ₀, mem_stabilizer_iff.mpr hstab⟩, Subtype.ext ?_⟩
  rw [coe_stabilizerRestrictInfinitePlace]
  show AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L (ρ₀.restrictScalars k * σ₀) = τ.1
  rw [map_mul, restrictNormalHom_restrictScalars k ↥L ρ₀, one_mul, hσ₀]

omit [IsGalois k Ω] [NumberField ↥L] in
/-- The kernel of the map to the decomposition group of a level consists of the automorphisms
fixing that level. -/
theorem mem_ker_stabilizerRestrictInfinitePlace_iff {σ : ↥(stabilizer Gal(Ω/k) w)} :
    σ ∈ (stabilizerRestrictInfinitePlace L hv).ker ↔ (σ : Gal(Ω/k)) ∈ L.fixingSubgroup := by
  rw [MonoidHom.mem_ker, ← IntermediateField.restrictNormalHom_ker L, MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end RestrictInfinitePlace

/-! ### The local condition at an infinite place of a level -/

section InfiniteBridge

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M]

set_option maxHeartbeats 4000000 in
/-- **A class of the second cohomology dying on every decomposition subgroup at an infinite place
splits at every infinite place of a level it is inflated from.**  An infinite place of the whole
extension above the place carries a trivialising cochain of its decomposition subgroup; the cochain
is smooth, hence constant on the automorphisms fixing a finite Galois level, and enlarging the
level one started from by that one makes the cochain descend to the decomposition group of a level.
Descending the resulting local coboundary along the tower of the two levels gives the local
condition at the place of the smaller one. -/
theorem exists_sub_add_eq_infiniteUnits_of_resH2
    (htriv : ∀ (g : Gal(Ω/k)) (m : M), g • m = m) (ι : M →* kˣ)
    (E : IntermediateField k Ω) [NumberField ↥E] [IsGalois k ↥E]
    {b : Gal(↥E/k) → Gal(↥E/k) → M}
    (hb : ∀ x y z : Gal(↥E/k), b y z * b x (y * z) = b (x * y) z * b x y)
    {A : Gal(Ω/k) × Gal(Ω/k) → M} (hA : IsMulCocycle₂ A) (hAs : IsSmooth₂ A)
    (hAinf : A = fun p : Gal(Ω/k) × Gal(Ω/k) =>
      b (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E p.1)
        (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E p.2))
    (hz : ∀ D ∈ infiniteDecompositionSubgroups k Ω, resH2 D (smoothH2Mk A hA hAs) = 1)
    (v : InfinitePlace ↥E) :
    ∃ c : ↥(stabilizer Gal(↥E/k) v) → Additive (v.Completion)ˣ,
      ∀ s t : ↥(stabilizer Gal(↥E/k) v),
        Additive.ofMul (infiniteUnitHom v
            (Units.map (algebraMap k ↥E : k →* ↥E) (ι (b s.1 t.1))))
          = smulUnitsAut s (c t) - c (s * t) + c s := by
  classical
  haveI : FiniteDimensional k ↥E := Module.Finite.of_restrictScalars_finite ℚ k ↥E
  haveI : Algebra.IsAlgebraic ↥E Ω := Algebra.IsAlgebraic.tower_top (K := k) (L := ↥E) (A := Ω)
  -- an infinite place of the whole extension above the place
  obtain ⟨w, hw⟩ := NumberField.InfinitePlace.comap_surjective (k := ↥E) (K := Ω) v
  have hw' : w.comap (algebraMap ↥E Ω) = v := hw
  -- the trivialising cochain of the decomposition subgroup there
  obtain ⟨u, hu, hcob⟩ := (resH2_eq_one_iff (stabilizer Gal(Ω/k) w) hA hAs).1 (hz _ ⟨w, rfl⟩)
  obtain ⟨N, hN, hNu⟩ := hu
  obtain ⟨E₀, hE₀fin, hE₀gal, hE₀N⟩ :=
    exists_fixingSubgroup_le_subgroup (stabilizer Gal(Ω/k) w) hN
  -- a finite Galois level containing both the given one and the level of smoothness
  obtain ⟨E'', hEE'', hE₀E'', hE''fin, hE''gal⟩ :
      ∃ E'' : IntermediateField k Ω, E ≤ E'' ∧ E₀ ≤ E'' ∧ FiniteDimensional k ↥E'' ∧
        IsGalois k ↥E'' := by
    haveI := hE₀fin
    haveI := hE₀gal
    haveI : FiniteDimensional k ↥(E ⊔ E₀) := inferInstance
    refine ⟨E ⊔ E₀, le_sup_left, le_sup_right, inferInstance, ?_⟩
    exact ((InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois (E ⊔ E₀)).1
      ⟨(E ⊔ E₀).fixingSubgroup_isOpen, normal_fixingSubgroup (E ⊔ E₀)⟩).2
  haveI := hE''fin
  haveI := hE''gal
  haveI : NumberField ↥E'' := NumberField.of_module_finite k ↥E''
  letI : Algebra ↥E ↥E'' := (IntermediateField.inclusion hEE'').toRingHom.toAlgebra
  haveI : IsScalarTower k ↥E ↥E'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ↥E ↥E'' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the place of the larger level below it
  set v'' : InfinitePlace ↥E'' := w.comap (algebraMap ↥E'' Ω) with hv''
  have hveq : v''.comap (algebraMap ↥E ↥E'') = v := by
    rw [hv'', ← NumberField.InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq, hw']
  -- the cochain descends to the decomposition group of the larger level
  have hπsurj : Function.Surjective (stabilizerRestrictInfinitePlace E'' hv'') :=
    stabilizerRestrictInfinitePlace_surjective E'' hv''
  have hkerN : ∀ n : ↥(stabilizer Gal(Ω/k) w),
      n ∈ (stabilizerRestrictInfinitePlace E'' hv'').ker → n ∈ N := fun n hn =>
    hE₀N n (IntermediateField.fixingSubgroup_le hE₀E''
      ((mem_ker_stabilizerRestrictInfinitePlace_iff E'' hv'').1 hn))
  have hwd : ∀ x y : ↥(stabilizer Gal(Ω/k) w),
      stabilizerRestrictInfinitePlace E'' hv'' x = stabilizerRestrictInfinitePlace E'' hv'' y →
        u x = u y := by
    intro x y h
    obtain ⟨n, hn, rfl⟩ := exists_mem_ker_eq_mul h
    exact (hNu x n (hkerN n hn)).symm
  obtain ⟨c'', hc''⟩ : ∃ c'' : ↥(stabilizer Gal(↥E''/k) v'') → M,
      ∀ x : ↥(stabilizer Gal(Ω/k) w), c'' (stabilizerRestrictInfinitePlace E'' hv'' x) = u x :=
    ⟨fun q => u (Function.surjInv hπsurj q), fun x => hwd _ _ (Function.surjInv_eq hπsurj _)⟩
  -- the trivialising identity, read at the larger level
  have hact : ∀ (x : ↥(stabilizer Gal(Ω/k) w)) (m : M), x • m = m := fun x m => htriv x.1 m
  have hcobval : ∀ x y : ↥(stabilizer Gal(Ω/k) w),
      u y / u (x * y) * u x
        = b (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E (x : Gal(Ω/k)))
            (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E (y : Gal(Ω/k))) := by
    intro x y
    have h := congrFun hcob (x, y)
    rw [coboundary₂_apply, hact, hAinf] at h
    exact h
  have hres : ∀ (g : Gal(↥E''/k)) (x : Ω) (hx : x ∈ E) (hx' : x ∈ E''),
      ((AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E'') ↥E g ⟨x, hx⟩ : ↥E) : Ω)
        = ((g ⟨x, hx'⟩ : ↥E'') : Ω) := by
    intro g x hx _
    exact congrArg (fun z : ↥E'' => (z : Ω)) (AlgEquiv.restrictNormal_commutes g ↥E ⟨x, hx⟩)
  have hρ : ∀ g : Gal(Ω/k),
      AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E'') ↥E
          (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E'' g)
        = AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E g :=
    restrictNormalHom_eq_of_res hEE'' hres
  have hcoc'' : ∀ s t : ↥(stabilizer Gal(↥E''/k) v''),
      c'' t / c'' (s * t) * c'' s
        = b (AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E'') ↥E s.1)
            (AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E'') ↥E t.1) := by
    intro s t
    obtain ⟨x, rfl⟩ := hπsurj s
    obtain ⟨y, rfl⟩ := hπsurj t
    rw [← map_mul]
    simp only [hc'']
    rw [hcobval x y]
    simp only [coe_stabilizerRestrictInfinitePlace, hρ]
  -- the local coboundary at the place of the larger level
  have hloc'' : ∃ c : ↥(stabilizer Gal(↥E''/k) v'') → Additive (v''.Completion)ˣ,
      ∀ s t : ↥(stabilizer Gal(↥E''/k) v''),
        Additive.ofMul (infiniteUnitHom v'' (Units.map (algebraMap k ↥E'' : k →* ↥E'')
            (ι (b (AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E'') ↥E s.1)
                  (AlgEquiv.restrictNormalHom (F := k) (K₁ := ↥E'') ↥E t.1)))))
          = smulUnitsAut s (c t) - c (s * t) + c s := by
    refine ⟨fun s => Additive.ofMul (infiniteUnitHom v''
      (Units.map (algebraMap k ↥E'' : k →* ↥E'') (ι (c'' s)))), fun s t => ?_⟩
    simp only [smulUnitsAut_infiniteUnitHom_algebraMap]
    rw [← hcoc'' s t]
    simp only [map_mul, map_div, ofMul_mul, ofMul_div]
  -- and its descent to the place of the smaller one
  have hafin : ∀ x y z : Gal(↥E/k),
      ι (b y z) * ι (b x (y * z)) = ι (b (x * y) z) * ι (b x y) := by
    intro x y z
    rw [← map_mul, ← map_mul, hb]
  have hdesc := exists_sub_add_eq_infiniteUnits_descent (k := k) (F := ↥E) (K := ↥E'') v''
    (a := fun x y => ι (b x y)) hafin hloc''
  rw [hveq] at hdesc
  exact hdesc

end InfiniteBridge

/-! ### The vanishing of the everywhere locally trivial classes -/

section Sha

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M]

set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
/-- **A class of the second cohomology with roots of unity coefficients dying on every
decomposition subgroup of the absolute Galois group is trivial.**  Every class is represented by a
cocycle inflated from a finite Galois level, and dying on the decomposition subgroups at the primes
and at the infinite places of the algebraic closure makes that representative split at every place
of its level; a locally split cocycle at a level is a coboundary. -/
theorem eq_one_of_mem_sha2
    {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (htriv : ∀ (g : Gal(Ω/k)) (m : M), g • m = m)
    {ι : M →* kˣ} (hιinj : Function.Injective ι) (hιpow : ∀ m : M, ι m ^ n = 1)
    (hιsurj : ∀ y : kˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    (z : SmoothH2 Gal(Ω/k) M)
    (hz : z ∈ sha2 M (decompositionSubgroups k Ω)) :
    z = 1 := by
  refine eq_one_of_forall_isLocallySplitLevel hζ htriv hιinj hιpow hιsurj z ?_
  rintro E _ _ b hb ⟨A, hA, hAs, hAinf, hAz⟩
  have hzD : ∀ D ∈ decompositionSubgroups k Ω,
      resH2 D (smoothH2Mk A hA hAs) = 1 := by
    intro D hD
    rw [hAz]
    exact mem_sha2.1 hz D hD
  exact ⟨fun w => exists_sub_add_eq_infiniteUnits_of_resH2 htriv ι E hb hA hAs hAinf
      (fun D hD => hzD D (infiniteDecompositionSubgroups_subset hD)) w,
    fun v => exists_sub_add_eq_adicUnits_of_resH2 htriv ι E hb hA hAs hAinf
      (fun D hD => hzD D (finiteDecompositionSubgroups_subset hD)) v⟩

end Sha

end InverseGalois.CFT
