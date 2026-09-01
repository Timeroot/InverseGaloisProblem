/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CentralEmbedding
import InverseGalois.CFT.Units.ABHNPlaces

/-!
# The local-global principle for a central embedding problem, with no restriction on the kernel

A central Frattini embedding problem over a number field containing the roots of unity that match
the order of its kernel is solvable as soon as the factor set of a section of the surjection is a
coboundary in the units of the given extension.  The forms of this criterion already available buy
their silence at the archimedean places by restricting the order of the kernel: for odd order, or
more generally for order coprime to the local degrees at infinity, the archimedean places cost
nothing and only the ramified finite places have to be inspected.

Here the order of the kernel is arbitrary.  The price is that the local hypothesis is imposed at
every place of the extension, archimedean places included; the reward is the local-global principle
in the form that also covers the prime `2`, where the real places genuinely obstruct.

## Main results

* `InverseGalois.CFT.exists_surjective_hom_of_forall_place`: **a central Frattini embedding problem
  whose obstruction is a coboundary at every place is solvable over a larger extension.**
* `InverseGalois.CFT.exists_local_coboundary_of_exists_lift_infinitePlace`: a homomorphic lift over
  the decomposition group at an archimedean place makes the obstruction a coboundary there.
* `InverseGalois.CFT.exists_surjective_hom_of_forall_place_lift`: **a central Frattini embedding
  problem that is solvable over the decomposition group at every place is solvable over a larger
  extension.**

## Tags

number field, embedding problem, central extension, Frattini subgroup, local-global principle,
Albert-Brauer-Hasse-Noether, Kummer theory
-/

open IsDedekindDomain MulAction NumberField IntermediateField

namespace InverseGalois.CFT

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem whose obstruction is a coboundary at every place is
solvable over a larger extension.**  The factor set of a section of `f`, transported into `kˣ` by
the identification of the kernel with the `n`-th roots of unity, is a two-cocycle; the
Albert-Brauer-Hasse-Noether theorem makes it a coboundary in the units of the extension, and Kummer
theory descends the trivialising cochain to the roots of unity over a larger field. -/
theorem exists_surjective_hom_of_forall_place
    {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = n)
    {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois k ↥K]
    {π : Gal(↥K/k) →* H} (hπ : Function.Surjective π)
    {χ : ↥f.ker →* kˣ} (hχinj : Function.Injective χ)
    (hχsurj : ∀ y : kˣ, y ^ n = 1 → ∃ z : ↥f.ker, χ z = y)
    {t : H → G} (ht : ∀ h, f (t h) = h)
    (hinf : ∀ w : InfinitePlace ↥K,
      ∃ c : ↥(stabilizer Gal(↥K/k) w) → Additive w.Completionˣ,
      ∀ s u : ↥(stabilizer Gal(↥K/k) w),
        Additive.ofMul (infiniteUnitHom w (Units.map (algebraMap k ↥K : k →* ↥K)
          (χ ⟨sectionFactorSet t (π s.1) (π u.1), sectionFactorSet_mem_ker f ht _ _⟩)))
          = smulUnitsAut s (c u) - c (s * u) + c s)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 ↥K),
      ∃ c : ↥(stabilizer Gal(↥K/k) v) → Additive (v.adicCompletion ↥K)ˣ,
      ∀ s u : ↥(stabilizer Gal(↥K/k) v),
        Additive.ofMul (adicUnitHom v (Units.map (algebraMap k ↥K : k →* ↥K)
          (χ ⟨sectionFactorSet t (π s.1) (π u.1), sectionFactorSet_mem_ker f ht _ _⟩)))
          = smulUnitsAut s (c u) - c (s * u) + c s) :
    HasProperSolution K f π := by
  classical
  set a : Gal(↥K/k) → Gal(↥K/k) → kˣ := fun x y =>
    χ ⟨sectionFactorSet t (π x) (π y), sectionFactorSet_mem_ker f ht _ _⟩ with hadef
  have hacoc : ∀ x y z : Gal(↥K/k), a y z * a x (y * z) = a (x * y) z * a x y := by
    intro x y z
    rw [hadef]
    exact charFactorSet_cocycle f hZ ht χ π x y z
  obtain ⟨b, hb⟩ := exists_isMulCoboundary_of_forall_place (k := k) (K := ↥K) hacoc hinf hfin
  exact exists_surjective_hom_of_isMulCoboundary hζ hZ hfr hcard hπ hχinj hχsurj ht hb

section LocalLift

variable {K : Type} [Field K] [NumberField K] [Algebra k K] [IsGalois k K]

omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- **A homomorphic lift over the decomposition group at an archimedean place makes the obstruction
a coboundary there.**  The difference between the section of `f` and the lift takes its values in
the kernel, hence in the centre, and the factor set of the section is exactly its coboundary;
applying the character of the kernel and embedding into the completion turns that identity into the
local coboundary condition. -/
theorem exists_local_coboundary_of_exists_lift_infinitePlace
    {G H : Type*} [Group G] [Group H] {f : G →* H} (hZ : f.ker ≤ Subgroup.center G)
    {π : Gal(K/k) →* H} {t : H → G} (ht : ∀ h, f (t h) = h) (χ : ↥f.ker →* kˣ)
    (w : InfinitePlace K)
    {σ : ↥(stabilizer Gal(K/k) w) →* G} (hσ : ∀ s, f (σ s) = π s.1) :
    ∃ c : ↥(stabilizer Gal(K/k) w) → Additive w.Completionˣ,
      ∀ s u : ↥(stabilizer Gal(K/k) w),
        Additive.ofMul (infiniteUnitHom w (Units.map (algebraMap k K : k →* K)
          (χ ⟨sectionFactorSet t (π s.1) (π u.1), sectionFactorSet_mem_ker f ht _ _⟩)))
          = smulUnitsAut s (c u) - c (s * u) + c s := by
  classical
  have hd : ∀ x : ↥(stabilizer Gal(K/k) w), t (π x.1) * (σ x)⁻¹ ∈ f.ker := fun x =>
    mem_ker_mul_inv f ht (π.comp (Subgroup.subtype _)) hσ x
  refine ⟨fun x => Additive.ofMul (infiniteUnitHom w (Units.map (algebraMap k K : k →* K)
    (χ ⟨t (π x.1) * (σ x)⁻¹, hd x⟩))), fun s u => ?_⟩
  rw [smulUnitsAut_infiniteUnitHom_algebraMap]
  have hsub : (⟨sectionFactorSet t (π s.1) (π u.1), sectionFactorSet_mem_ker f ht _ _⟩ : ↥f.ker)
      = ⟨t (π s.1) * (σ s)⁻¹, hd s⟩ * ⟨t (π u.1) * (σ u)⁻¹, hd u⟩
        * (⟨t (π (s * u).1) * (σ (s * u))⁻¹, hd (s * u)⟩)⁻¹ :=
    Subtype.ext (sectionFactorSet_eq_of_hom_comp_eq f hZ (π.comp (Subgroup.subtype _)) ht hσ s u)
  have hk : χ ⟨sectionFactorSet t (π s.1) (π u.1), sectionFactorSet_mem_ker f ht _ _⟩
      = χ ⟨t (π u.1) * (σ u)⁻¹, hd u⟩ / χ ⟨t (π (s * u).1) * (σ (s * u))⁻¹, hd (s * u)⟩
        * χ ⟨t (π s.1) * (σ s)⁻¹, hd s⟩ := by
    rw [hsub, map_mul, map_mul, map_inv]
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_div, ofMul_inv]
    abel
  rw [hk, map_mul, map_div, map_mul, map_div, ofMul_mul, ofMul_div]

end LocalLift

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem that is solvable over the decomposition group at every
place is solvable over a larger extension.**  This is the local-global principle for central
embedding problems in the form that places no restriction on the order of the kernel: the only
arithmetic input is a homomorphic lift of the restriction of `π` to each decomposition group,
archimedean places included. -/
theorem exists_surjective_hom_of_forall_place_lift
    {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = n)
    {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois k ↥K]
    {π : Gal(↥K/k) →* H} (hπ : Function.Surjective π)
    {χ : ↥f.ker →* kˣ} (hχinj : Function.Injective χ)
    (hχsurj : ∀ y : kˣ, y ^ n = 1 → ∃ z : ↥f.ker, χ z = y)
    {t : H → G} (ht : ∀ h, f (t h) = h)
    (hliftinf : ∀ w : InfinitePlace ↥K,
      ∃ σ : ↥(stabilizer Gal(↥K/k) w) →* G, ∀ s, f (σ s) = π s.1)
    (hliftfin : ∀ v : HeightOneSpectrum (𝓞 ↥K),
      ∃ σ : ↥(stabilizer Gal(↥K/k) v) →* G, ∀ s, f (σ s) = π s.1) :
    HasProperSolution K f π := by
  refine exists_surjective_hom_of_forall_place hζ hZ hfr hcard hπ hχinj hχsurj ht
    (fun w => ?_) (fun v => ?_)
  · obtain ⟨σ, hσ⟩ := hliftinf w
    exact exists_local_coboundary_of_exists_lift_infinitePlace (k := k) (K := ↥K) hZ ht χ w hσ
  · obtain ⟨σ, hσ⟩ := hliftfin v
    exact exists_local_coboundary_of_exists_lift (k := k) (K := ↥K) hZ ht χ v hσ

end InverseGalois.CFT
