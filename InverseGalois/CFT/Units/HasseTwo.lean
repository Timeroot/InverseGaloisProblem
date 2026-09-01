/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ABHNPlaces
import InverseGalois.CFT.Kummer.CocycleDescent
import InverseGalois.CFT.Profinite.Krull

/-!
# Locally trivial classes of the second cohomology with roots of unity coefficients

A class of the second cohomology of the absolute Galois group of a number field lives at a finite
Galois level: it is represented by a two-cocycle inflated from the Galois group of a finite Galois
subextension.  When the coefficients are the `n`-th roots of unity of the base field, the level
cocycle takes its values in the units of the base field, so the Albert-Brauer-Hasse-Noether theorem
applies to it: a splitting at every place of the level makes it the coboundary of a one-cochain
with values in the units of the level.  Kummer theory rescales that cochain over a further radical
extension so that its values are roots of unity again, and the rescaled cochain, read on the
absolute Galois group through restriction to the larger level, is a smooth one-cochain whose
coboundary is the cocycle one started from.

An everywhere locally trivial class of the second cohomology with roots of unity coefficients is
therefore trivial.  Only the places of the level enter, so no places of the algebraic closure are
needed, and nothing is assumed about the number of roots of unity, so the prime `2` is covered.

## Main definitions

* `InverseGalois.CFT.IsLocallySplitLevel`: **a two-cocycle at a level splits at every place of that
  level**, archimedean places included.

## Main results

* `InverseGalois.CFT.exists_level_cochain₂`: a two-cochain constant on the cosets of the kernel is
  a two-cochain of the quotient.
* `InverseGalois.CFT.restrictNormalHom_eq_of_res`: restriction to a level factors through
  restriction to a larger level.
* `InverseGalois.CFT.exists_isSmooth₁_coboundary₂_eq_of_isLocallySplitLevel`: **a locally split
  cocycle at a level, inflated to the absolute Galois group, is the coboundary of a smooth
  one-cochain.**
* `InverseGalois.CFT.smoothH2Mk_eq_one_of_isLocallySplitLevel`: the class of such a cocycle in the
  second cohomology of the absolute Galois group is trivial.
* `InverseGalois.CFT.eq_one_of_forall_isLocallySplitLevel`: **an everywhere locally trivial class
  of the second cohomology with roots of unity coefficients is trivial.**

## Tags

number field, Galois cohomology, second cohomology, local-global principle, roots of unity,
Albert-Brauer-Hasse-Noether, Kummer theory, Tate-Shafarevich group
-/

open IsDedekindDomain MulAction NumberField groupCohomology

namespace InverseGalois.CFT

/-! ### Descending a two-cochain to a quotient -/

section Descend

variable {G Q M : Type*} [Group G] [Group Q] {π : G →* Q}

/-- **A two-cochain constant on the cosets of the kernel is a two-cochain of the quotient.** -/
theorem exists_level_cochain₂ (hsurj : Function.Surjective π) {a : G × G → M}
    (hs : ∀ x y : G, ∀ n ∈ π.ker, ∀ m ∈ π.ker, a (x * n, y * m) = a (x, y)) :
    ∃ b : Q → Q → M, ∀ x y : G, b (π x) (π y) = a (x, y) := by
  classical
  refine ⟨fun p q => a (Function.surjInv hsurj p, Function.surjInv hsurj q), fun x y => ?_⟩
  exact eq_of_map_eq_of_smooth₂ hs (Function.surjInv_eq hsurj (π x))
    (Function.surjInv_eq hsurj (π y))

end Descend

/-! ### Two levels of the same Galois extension -/

section Tower

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- **Restriction to a level factors through restriction to a larger level.**  A homomorphism of
the Galois groups of the two levels which is the restriction of automorphisms is the comparison
map. -/
theorem restrictNormalHom_eq_of_res {L E : IntermediateField k Ω} [Normal k ↥L] [Normal k ↥E]
    (hLE : L ≤ E) {ρ : Gal(↥E/k) →* Gal(↥L/k)}
    (hres : ∀ (g : Gal(↥E/k)) (x : Ω) (hx : x ∈ L) (hx' : x ∈ E),
      ((ρ g ⟨x, hx⟩ : ↥L) : Ω) = ((g ⟨x, hx'⟩ : ↥E) : Ω))
    (g : Gal(Ω/k)) :
    ρ (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E g)
      = AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L g := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  have h1 := hres (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E g) (x : Ω) x.2 (hLE x.2)
  have h2 : ((AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E g ⟨(x : Ω), hLE x.2⟩ : ↥E) : Ω)
      = g (x : Ω) := AlgEquiv.restrictNormal_commutes g ↥E ⟨(x : Ω), hLE x.2⟩
  have h3 : ((AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L g x : ↥L) : Ω) = g (x : Ω) :=
    AlgEquiv.restrictNormal_commutes g ↥L x
  rw [show (⟨(x : Ω), x.2⟩ : ↥L) = x from Subtype.ext rfl] at h1
  rw [h1, h2, h3]

end Tower

/-! ### Splitting at every place of a level -/

section LocallySplit

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  {M : Type*} [CommGroup M]

/-- **A two-cocycle at a level splits at every place of that level.**  The values of the cocycle
lie in the base field; carried into the completion at a place of the level, each of them is the
coboundary of a one-cochain of the decomposition group at that place.  Archimedean places are
included. -/
def IsLocallySplitLevel (ι : M →* kˣ) (L : IntermediateField k Ω) [NumberField ↥L] [IsGalois k ↥L]
    (a : Gal(↥L/k) → Gal(↥L/k) → M) : Prop :=
  (∀ w : InfinitePlace ↥L, ∃ c : ↥(stabilizer Gal(↥L/k) w) → Additive w.Completionˣ,
      ∀ s t : ↥(stabilizer Gal(↥L/k) w),
        Additive.ofMul (infiniteUnitHom w
            (Units.map (algebraMap k ↥L : k →* ↥L) (ι (a s.1 t.1))))
          = smulUnitsAut s (c t) - c (s * t) + c s) ∧
  (∀ v : HeightOneSpectrum (𝓞 ↥L),
      ∃ c : ↥(stabilizer Gal(↥L/k) v) → Additive (v.adicCompletion ↥L)ˣ,
      ∀ s t : ↥(stabilizer Gal(↥L/k) v),
        Additive.ofMul (adicUnitHom v
            (Units.map (algebraMap k ↥L : k →* ↥L) (ι (a s.1 t.1))))
          = smulUnitsAut s (c t) - c (s * t) + c s)

end LocallySplit

/-! ### The vanishing of the locally trivial classes -/

section Vanishing

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A locally split cocycle at a level, inflated to the absolute Galois group, is the coboundary
of a smooth one-cochain.**  The Albert-Brauer-Hasse-Noether theorem trivialises the cocycle in the
units of the level, Kummer theory rescales the trivialising cochain over a larger level so that its
values are roots of unity, and restriction to that larger level turns the rescaled cochain into a
smooth one-cochain of the absolute Galois group. -/
theorem exists_isSmooth₁_coboundary₂_eq_of_isLocallySplitLevel
    {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (htriv : ∀ (g : Gal(Ω/k)) (m : M), g • m = m)
    {ι : M →* kˣ} (hιinj : Function.Injective ι) (hιpow : ∀ m : M, ι m ^ n = 1)
    (hιsurj : ∀ y : kˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    (L : IntermediateField k Ω) [NumberField ↥L] [IsGalois k ↥L]
    {a : Gal(↥L/k) → Gal(↥L/k) → M}
    (ha : ∀ x y z : Gal(↥L/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (hloc : IsLocallySplitLevel ι L a) :
    ∃ u : Gal(Ω/k) → M, IsSmooth₁ u ∧ coboundary₂ u =
      fun p : Gal(Ω/k) × Gal(Ω/k) =>
        a (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L p.1)
          (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L p.2) := by
  classical
  have hAcoc : ∀ x y z : Gal(↥L/k),
      ι (a y z) * ι (a x (y * z)) = ι (a (x * y) z) * ι (a x y) := by
    intro x y z
    rw [← map_mul, ← map_mul, ha]
  obtain ⟨b, hb⟩ := exists_isMulCoboundary_of_forall_place (k := k) (K := ↥L)
    (a := fun x y => ι (a x y)) hAcoc hloc.1 hloc.2
  obtain ⟨E, hLE, hEnum, hEgal, ρ, -, hres, c, hcpow, hc⟩ :=
    exists_intermediateField_cochain_of_isMulCoboundary hζ
      (a := fun x y => ι (a x y)) (fun x y => hιpow (a x y)) hb
  haveI : NumberField ↥E := hEnum
  haveI : IsGalois k ↥E := hEgal
  haveI : FiniteDimensional k ↥E := Module.Finite.of_restrictScalars_finite ℚ k ↥E
  choose d hd using fun g : Gal(↥E/k) => hιsurj (c g) (hcpow g)
  refine ⟨fun g => d (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E g),
    (isSmoothHom_restrictNormalHom E).isSmooth₁ (isSmooth₁_of_discreteTopology d), ?_⟩
  funext p
  obtain ⟨x, y⟩ := p
  have hρx : ρ (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E x)
      = AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L x :=
    restrictNormalHom_eq_of_res hLE hres x
  have hρy : ρ (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E y)
      = AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L y :=
    restrictNormalHom_eq_of_res hLE hres y
  have hkey := hc (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E x)
    (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E y)
  rw [hρx, hρy, ← hd, ← hd, ← hd, ← map_inv, ← map_mul, ← map_mul] at hkey
  simp only [coboundary₂_apply, htriv, map_mul, hιinj hkey]
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The class of a locally split cocycle at a level is trivial in the second cohomology of the
absolute Galois group.** -/
theorem smoothH2Mk_eq_one_of_isLocallySplitLevel
    {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (htriv : ∀ (g : Gal(Ω/k)) (m : M), g • m = m)
    {ι : M →* kˣ} (hιinj : Function.Injective ι) (hιpow : ∀ m : M, ι m ^ n = 1)
    (hιsurj : ∀ y : kˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    (L : IntermediateField k Ω) [NumberField ↥L] [IsGalois k ↥L]
    {a : Gal(↥L/k) → Gal(↥L/k) → M}
    (ha : ∀ x y z : Gal(↥L/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (hloc : IsLocallySplitLevel ι L a)
    {A : Gal(Ω/k) × Gal(Ω/k) → M} (hA : IsMulCocycle₂ A) (hAs : IsSmooth₂ A)
    (hAinf : A = fun p : Gal(Ω/k) × Gal(Ω/k) =>
      a (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L p.1)
        (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥L p.2)) :
    smoothH2Mk A hA hAs = 1 := by
  obtain ⟨u, hu, hcob⟩ := exists_isSmooth₁_coboundary₂_eq_of_isLocallySplitLevel hζ htriv
    hιinj hιpow hιsurj L ha hloc
  exact (smoothH2Mk_eq_one_iff hA hAs).2 ⟨u, hu, by rw [hcob, hAinf]⟩

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **An everywhere locally trivial class of the second cohomology with roots of unity coefficients
is trivial.**  Every class is represented by a cocycle inflated from a finite Galois level, and a
representative that splits at every place of its level is a coboundary. -/
theorem eq_one_of_forall_isLocallySplitLevel
    {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (htriv : ∀ (g : Gal(Ω/k)) (m : M), g • m = m)
    {ι : M →* kˣ} (hιinj : Function.Injective ι) (hιpow : ∀ m : M, ι m ^ n = 1)
    (hιsurj : ∀ y : kˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    (z : SmoothH2 Gal(Ω/k) M)
    (hloc : ∀ (E : IntermediateField k Ω) [NumberField ↥E] [IsGalois k ↥E]
      (b : Gal(↥E/k) → Gal(↥E/k) → M),
      (∀ x y w : Gal(↥E/k), b y w * b x (y * w) = b (x * y) w * b x y) →
      (∃ (A : Gal(Ω/k) × Gal(Ω/k) → M) (hA : IsMulCocycle₂ A) (hAs : IsSmooth₂ A),
        (A = fun p : Gal(Ω/k) × Gal(Ω/k) =>
          b (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E p.1)
            (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E p.2)) ∧
        smoothH2Mk A hA hAs = z) →
      IsLocallySplitLevel ι E b) :
    z = 1 := by
  classical
  haveI : IsSmoothAction Gal(Ω/k) M := ⟨⊤, isOpenNormal_top, fun σ _ m => htriv σ m⟩
  obtain ⟨E, hEfin, hEgal, -, A, hA, hAs, hcon, hz⟩ := exists_isGalois_smooth₂ z
  haveI : FiniteDimensional k ↥E := hEfin
  haveI : IsGalois k ↥E := hEgal
  haveI : NumberField ↥E := NumberField.of_module_finite k ↥E
  have hker : ∀ x y : Gal(Ω/k),
      ∀ σ ∈ (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E).ker,
      ∀ τ ∈ (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E).ker,
        A (x * σ, y * τ) = A (x, y) := by
    intro x y σ hσ τ hτ
    rw [IntermediateField.restrictNormalHom_ker E] at hσ hτ
    exact hcon x y σ hσ τ hτ
  obtain ⟨b, hbeq⟩ := exists_level_cochain₂ (restrictNormalHom_surjective_level E) hker
  have hbcoc : ∀ x y w : Gal(↥E/k), b y w * b x (y * w) = b (x * y) w * b x y := by
    intro x y w
    obtain ⟨x', rfl⟩ := restrictNormalHom_surjective_level E x
    obtain ⟨y', rfl⟩ := restrictNormalHom_surjective_level E y
    obtain ⟨w', rfl⟩ := restrictNormalHom_surjective_level E w
    simp only [← map_mul, hbeq]
    have h := hA x' y' w'
    rw [htriv] at h
    exact h.symm
  have hAinf : A = fun p : Gal(Ω/k) × Gal(Ω/k) =>
      b (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E p.1)
        (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E p.2) :=
    funext fun p => (hbeq p.1 p.2).symm
  rw [← hz]
  exact smoothH2Mk_eq_one_of_isLocallySplitLevel hζ htriv hιinj hιpow hιsurj E hbcoc
    (hloc E b hbcoc ⟨A, hA, hAs, hAinf, hz⟩) hA hAs hAinf

end Vanishing

end InverseGalois.CFT
