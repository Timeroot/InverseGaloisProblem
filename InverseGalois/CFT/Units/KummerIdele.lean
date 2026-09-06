/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.DecompositionLocalPower
import InverseGalois.CFT.Kummer.SupKummerData
import InverseGalois.CFT.Kummer.SupPowSurjective
import InverseGalois.CFT.Profinite.KummerFinite
import InverseGalois.CFT.Profinite.KummerLocalTate
import InverseGalois.CFT.Units.DecompositionClosed
import InverseGalois.CFT.Units.GlobalUnitsLocal
import InverseGalois.CFT.Units.HasseTwoDecomposition

/-!
# An everywhere locally trivial Kummer class dies in the ideles

A class of the first cohomology of the absolute Galois group of a number field with coefficients in
the kernel of a lifting problem which dies on every decomposition subgroup is, read through the
twisted Kummer identification, a class of the first cohomology of the Galois group of a finite level
with coefficients in the units of that level tensored with the coefficients of the problem.  **That
class dies in the ideles.**

The proof is a place-by-place assembly of three earlier pieces.  At a place of the level, choose a
place of the whole extension above it; the fixed field of its decomposition subgroup is an
intermediate field whose compositum with the level receives the units of the level, and the
inclusion of the units is surjective after tensoring while its kernel is annihilated by the
embedding of the units of the level into the completion at the place.  Those are exactly the two
conditions under which local triviality of the class forces the reading of the class at the place to
vanish.  The units of a number field read at one place through the ideles are that embedding, so the
detection theorem for the ideles applies and the class dies there.

The compositum inherits the Kummer situation of the level: a primitive root of unity of the level
stays primitive in the compositum, so no new roots of unity appear, and the whole extension supplies
the radicals.

## Main results

* `InverseGalois.CFT.tateMap_tateRes_kummerFiniteH1Equiv_adic_eq_zero`,
  `InverseGalois.CFT.tateMap_tateRes_kummerFiniteH1Equiv_infinite_eq_zero`: **an everywhere locally
  trivial class, read over the Galois group of the level, dies in the completion at every finite,
  respectively archimedean, place of the level.**
* `InverseGalois.CFT.tateMap_globalUnitsToIdele_kummerFiniteH1Equiv_eq_zero`: **an everywhere
  locally trivial class, read over the Galois group of the level, dies in the ideles.**

## Tags

number field, Kummer theory, idele, decomposition group, local-global principle, Tate cohomology
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

open scoped Pointwise TensorProduct

noncomputable section

/-! ### Tensoring on the two sides commutes -/

section Commute

variable {A B C D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
  [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D]

/-- **A map of the left factor and a map of the right factor of a tensor product commute.** -/
theorem tensorMap_id_comm (f : A →ₗ[ℤ] B) (g : C →ₗ[ℤ] D) (t : A ⊗[ℤ] C) :
    TensorProduct.map f LinearMap.id (TensorProduct.map LinearMap.id g t)
      = TensorProduct.map LinearMap.id g (TensorProduct.map f LinearMap.id t) := by
  rw [TensorProduct.map_map, TensorProduct.map_map]
  simp

end Commute

/-! ### The decomposition group of a level and the quotient of a decomposition subgroup -/

section Bridge

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  (L : IntermediateField k Ω) [IsGalois k ↥L]

/-- **The decomposition group of a level at the place below a prime is the quotient of the
decomposition subgroup at the prime, read inside the Galois group of the level.** -/
theorem coe_stabilizerQuotientEquivPrime_eq {P : Ideal (𝓞 Ω)} [P.IsPrime]
    {v : HeightOneSpectrum (𝓞 ↥L)} (hv : v.asIdeal = Ideal.under (𝓞 ↥L) P)
    (g : ↥(stabilizer Gal(Ω/k) P) ⧸ L.fixingSubgroup.subgroupOf (stabilizer Gal(Ω/k) P)) :
    ((stabilizerQuotientEquivPrime L hv g : ↥(stabilizer Gal(↥L/k) v)) : Gal(↥L/k))
      = quotientFixingSubgroupEquiv L
        (quotSubHom L.fixingSubgroup (stabilizer Gal(Ω/k) P) g) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  rw [coe_stabilizerQuotientEquivPrime, quotSubHom_mk, quotientFixingSubgroupEquiv_mk]

/-- **The decomposition group of a level at the place below an archimedean place is the quotient of
the decomposition subgroup at that place, read inside the Galois group of the level.** -/
theorem coe_stabilizerQuotientEquivInfinitePlace_eq {w : InfinitePlace Ω}
    {v : InfinitePlace ↥L} (hv : v = w.comap (algebraMap ↥L Ω))
    (g : ↥(stabilizer Gal(Ω/k) w) ⧸ L.fixingSubgroup.subgroupOf (stabilizer Gal(Ω/k) w)) :
    ((stabilizerQuotientEquivInfinitePlace L hv g : ↥(stabilizer Gal(↥L/k) v)) : Gal(↥L/k))
      = quotientFixingSubgroupEquiv L
        (quotSubHom L.fixingSubgroup (stabilizer Gal(Ω/k) w) g) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  rw [coe_stabilizerQuotientEquivInfinitePlace, quotSubHom_mk, quotientFixingSubgroupEquiv_mk]

end Bridge

/-! ### The reading of a locally trivial class at one place -/

section Place

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K : IntermediateField k Ω} [NumberField ↥K] [K.fixingSubgroup.Normal] [Normal k ↥K]
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/k) M] {ιK : M →* (↥K)ˣ}
variable {p d dW : ℕ} [Fact p.Prime] [NeZero p] [IsCyclic M]
variable {E : Type} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
variable (hK : IsKummerData ↥K Ω M ιK p)
variable (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivEK : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable {J : Type} [Fintype J] [DecidableEq J] (α : E ≃* (J → M)) (hEp : ∀ e : E, e ^ p = 1)
variable (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
  σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m))
variable [ActsTrivially K.fixingSubgroup (M →* E)] [Finite Gal(↥K/k)]
variable (W : Rep ℤ Gal(↥K/k))
  (φ : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E) ≃+ ↥(tensorObj (globalUnitsRep k ↥K) W).V)
  (hφ : ∀ (g : Gal(Ω/k) ⧸ K.fixingSubgroup) (t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)),
    φ (g • t)
      = (tensorObj (globalUnitsRep k ↥K) W).ρ (quotientFixingSubgroupEquiv K g) (φ t))
variable {ρ : Additive (M →* E) →ₗ[ℤ] ↥W.V}
  (hφmap : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
    φ t = TensorProduct.map LinearMap.id ρ t)
variable (eM : Additive (M →* E) ≃+ (Fin d → ZMod p))
variable (hroot : ∀ x : Ωˣ, ∃ y : Ωˣ, y ^ p = x)
variable (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k)))

include hφmap eM hroot in
/-- **An everywhere locally trivial class, read over the Galois group of the level, dies in the
completion of the level at a finite place.**  A prime of the integers of the whole extension above
the place has a decomposition subgroup whose fixed field, composed with the level, receives the
units of the level surjectively after tensoring, with a kernel the embedding into the completion
kills. -/
theorem tateMap_tateRes_kummerFiniteH1Equiv_adic_eq_zero (v : HeightOneSpectrum (𝓞 ↥K))
    {z : SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E)}
    (hz : z ∈ sha1Level E K.fixingSubgroup hop (decompositionSubgroups k Ω)) :
    tateMap (globalUnitsAdicLocalHom k ↥K W v) 1
      (tateRes (stabilizer Gal(↥K/k) v) (tensorObj (globalUnitsRep k ↥K) W) 1
        (Multiplicative.toAdd (kummerFiniteH1Equiv hK htriv htrivEK α hEp hfix
          (tensorObj (globalUnitsRep k ↥K) W) φ hφ hop z))) = 0 := by
  classical
  haveI : IsGalois k ↥K := ⟨⟩
  haveI := v.isPrime
  obtain ⟨P, -, hPp, hPu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (R := 𝓞 ↥K) (S := 𝓞 Ω) v.asIdeal ⊥ (by simp)
  haveI := hPp
  have hPunder : v.asIdeal = Ideal.under (𝓞 ↥K) P := hPu.symm
  have hPbot : P ≠ ⊥ := by
    intro h
    refine v.ne_bot ?_
    rw [hPunder, h, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      RingOfIntegers.ker_algebraMap_eq_bot]
  have hDS : stabilizer Gal(Ω/k) P ∈ decompositionSubgroups k Ω :=
    finiteDecompositionSubgroups_subset ⟨P, hPp, hPbot, rfl⟩
  obtain ⟨F, hD⟩ : ∃ F : IntermediateField k Ω, F.fixingSubgroup = stabilizer Gal(Ω/k) P :=
    ⟨_, fixingSubgroup_fixedField_of_mem_decompositionSubgroups hDS⟩
  letI := trivialMulDistribMulAction Gal(Ω/↥(K ⊔ F)) M
  obtain ⟨ζ, hζ⟩ := hK.exists_isPrimitiveRoot
  have hjalg := algebraMap_unitsInclusion (le_sup_left : K ≤ K ⊔ F)
  have htrivEL : ∀ (x : ↥(K ⊔ F).fixingSubgroup) (e : E), x • e = e := fun x e =>
    htrivEK ⟨x.1, IntermediateField.fixingSubgroup_le le_sup_left x.2⟩ e
  have hlocker : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
      TensorProduct.map (MonoidHom.toAdditive (unitsInclusion
        (le_sup_left : K ≤ K ⊔ F))).toIntLinearMap LinearMap.id t = 0 →
        (globalUnitsAdicLocalHom k ↥K W v).hom.hom (φ t) = 0 := by
    intro t ht
    rw [globalUnitsAdicLocalHom_apply, hφmap t, tensorMap_id_comm,
      tensor_adicUnitHom_eq_zero_of_tensor_sup_eq_zero eM _ hjalg hζ hD hPunder ht,
      _root_.map_zero]
  exact tateMap_tateRes_kummerFiniteH1Equiv_eq_zero_of_tensor_eq_zero hK
    (isKummerData_of_le hK le_sup_left hroot) (unitsInclusion le_sup_left) hjalg
    (fun m => hjalg (ιK m)) hD htriv htrivEK htrivEL α hEp hfix _ φ hφ
    (stabilizerQuotientEquivPrime K hPunder) _ (globalUnitsAdicLocalHom k ↥K W v) hop
    (surjective_tensor_sup_of_stabilizer_ideal eM _ hjalg hζ hroot hD hPunder) hlocker
    (coe_stabilizerQuotientEquivPrime_eq K hPunder) hDS hz

include hφmap eM hroot in
/-- **An everywhere locally trivial class, read over the Galois group of the level, dies in the
completion of the level at an archimedean place.** -/
theorem tateMap_tateRes_kummerFiniteH1Equiv_infinite_eq_zero (u : InfinitePlace ↥K)
    {z : SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E)}
    (hz : z ∈ sha1Level E K.fixingSubgroup hop (decompositionSubgroups k Ω)) :
    tateMap (globalUnitsInfiniteLocalHom k ↥K W u) 1
      (tateRes (stabilizer Gal(↥K/k) u) (tensorObj (globalUnitsRep k ↥K) W) 1
        (Multiplicative.toAdd (kummerFiniteH1Equiv hK htriv htrivEK α hEp hfix
          (tensorObj (globalUnitsRep k ↥K) W) φ hφ hop z))) = 0 := by
  classical
  haveI : IsGalois k ↥K := ⟨⟩
  haveI : Algebra.IsAlgebraic ↥K Ω := Algebra.IsAlgebraic.tower_top (K := k) (L := ↥K) (A := Ω)
  obtain ⟨V, hV⟩ := NumberField.InfinitePlace.comap_surjective (k := ↥K) (K := Ω) u
  have hu : u = V.comap (algebraMap ↥K Ω) := hV.symm
  have hDS : stabilizer Gal(Ω/k) V ∈ decompositionSubgroups k Ω :=
    infiniteDecompositionSubgroups_subset ⟨V, rfl⟩
  obtain ⟨F, hD⟩ : ∃ F : IntermediateField k Ω, F.fixingSubgroup = stabilizer Gal(Ω/k) V :=
    ⟨_, fixingSubgroup_fixedField_of_mem_decompositionSubgroups hDS⟩
  letI := trivialMulDistribMulAction Gal(Ω/↥(K ⊔ F)) M
  obtain ⟨ζ, hζ⟩ := hK.exists_isPrimitiveRoot
  have hjalg := algebraMap_unitsInclusion (le_sup_left : K ≤ K ⊔ F)
  have htrivEL : ∀ (x : ↥(K ⊔ F).fixingSubgroup) (e : E), x • e = e := fun x e =>
    htrivEK ⟨x.1, IntermediateField.fixingSubgroup_le le_sup_left x.2⟩ e
  have hlocker : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
      TensorProduct.map (MonoidHom.toAdditive (unitsInclusion
        (le_sup_left : K ≤ K ⊔ F))).toIntLinearMap LinearMap.id t = 0 →
        (globalUnitsInfiniteLocalHom k ↥K W u).hom.hom (φ t) = 0 := by
    intro t ht
    rw [globalUnitsInfiniteLocalHom_apply, hφmap t, tensorMap_id_comm,
      tensor_infiniteUnitHom_eq_zero_of_tensor_sup_eq_zero eM _ hjalg hζ hD hu ht,
      _root_.map_zero]
  exact tateMap_tateRes_kummerFiniteH1Equiv_eq_zero_of_tensor_eq_zero hK
    (isKummerData_of_le hK le_sup_left hroot) (unitsInclusion le_sup_left) hjalg
    (fun m => hjalg (ιK m)) hD htriv htrivEK htrivEL α hEp hfix _ φ hφ
    (stabilizerQuotientEquivInfinitePlace K hu) _ (globalUnitsInfiniteLocalHom k ↥K W u) hop
    (surjective_tensor_sup_of_stabilizer_infinitePlace eM _ hjalg hζ hroot hD hu) hlocker
    (coe_stabilizerQuotientEquivInfinitePlace_eq K hu) hDS hz

include hφmap eM hroot in
/-- **An everywhere locally trivial class of the first cohomology, read over the Galois group of the
level, dies in the ideles.**  Its reading at every finite and every archimedean place of the level
vanishes, and a class of the units of a number field whose local class vanishes everywhere dies in
the ideles. -/
theorem tateMap_globalUnitsToIdele_kummerFiniteH1Equiv_eq_zero
    (eW : ↥W.V ≃+ (Fin dW → ZMod p))
    {z : SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E)}
    (hz : z ∈ sha1Level E K.fixingSubgroup hop (decompositionSubgroups k Ω)) :
    tateMap (tensorHomLeft W (globalUnitsToIdele k ↥K)) 1
      (Multiplicative.toAdd (kummerFiniteH1Equiv hK htriv htrivEK α hEp hfix
        (tensorObj (globalUnitsRep k ↥K) W) φ hφ hop z)) = 0 :=
  tateMap_globalUnitsToIdele_eq_zero W eW _
    (fun u => tateMap_tateRes_kummerFiniteH1Equiv_infinite_eq_zero hK htriv htrivEK α hEp hfix
      W φ hφ hφmap eM hroot hop u hz)
    (fun v => tateMap_tateRes_kummerFiniteH1Equiv_adic_eq_zero hK htriv htrivEK α hEp hfix
      W φ hφ hφmap eM hroot hop v hz)

end Place

end

end InverseGalois.CFT
