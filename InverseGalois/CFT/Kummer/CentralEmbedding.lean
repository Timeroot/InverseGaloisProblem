/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CentralLift
import InverseGalois.CFT.Kummer.CocycleDescent
import InverseGalois.CFT.Units.ABHNCoboundary

/-!
# Solving a central embedding problem over a field containing the roots of unity

Let `k` be a number field containing a primitive `n`-th root of unity and let `f : G → H` be a
surjection of finite groups with kernel of order `n` inside both the centre and the Frattini
subgroup of `G`.  Given a Galois extension `K/k` with a surjection `π : Gal(K/k) → H`, the
embedding problem asks for a Galois extension `M/k` with a surjection onto `G` compatible with `π`.

The obstruction is the factor set of a set-theoretic section of `f`, pulled back along `π`.  Its
values lie in the kernel, which the choice of a primitive root of unity identifies with the group
of `n`-th roots of unity of `k`, so the obstruction is a two-cocycle with values in `kˣ`.  The
Albert-Brauer-Hasse-Noether theorem makes it a coboundary in `Kˣ` as soon as it is one locally at
the ramified finite places; Kummer theory then descends the trivialising cochain to a cochain of
roots of unity over a larger field `M`; and correcting the section by that cochain produces the
homomorphism, which is surjective because the kernel lies in the Frattini subgroup.

## Main results

* `InverseGalois.CFT.exists_surjective_hom_of_isMulCoboundary`: **a central Frattini embedding
  problem whose obstruction is a coboundary in the units of the given extension is solvable over a
  larger extension.**
* `InverseGalois.CFT.exists_surjective_hom_of_forall_ramified`: **a central Frattini embedding
  problem with kernel of odd order whose obstruction is a coboundary at every ramified finite place
  is solvable over a larger extension.**
* `InverseGalois.CFT.exists_local_coboundary_of_exists_lift`: a homomorphic lift over the
  decomposition group at a finite place makes the obstruction a coboundary there.
* `InverseGalois.CFT.exists_surjective_hom_of_forall_ramified_lift`: **a central Frattini embedding
  problem with kernel of odd order that is solvable over the decomposition group at every ramified
  finite place is solvable over a larger extension.**

## Tags

embedding problem, central extension, Frattini subgroup, Kummer theory, roots of unity,
Albert-Brauer-Hasse-Noether, group cohomology
-/

open IsDedekindDomain MulAction NumberField IntermediateField

namespace InverseGalois.CFT

variable {k : Type} [Field k] [NumberField k]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem whose obstruction is a coboundary in the units of the
given extension is solvable over a larger extension.**  The cochain trivialising the obstruction is
pushed by Kummer theory onto a cochain of `n`-th roots of unity over a larger Galois extension `M`;
those roots of unity already lie in `k`, so they are read back inside the kernel of `f`, and
correcting the section of `f` by them produces a homomorphism `Gal(M/k) → G` lifting `π`.  It is
surjective because its image supplements the kernel, which lies in the Frattini subgroup. -/
theorem exists_surjective_hom_of_isMulCoboundary
    {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = n)
    {K : IntermediateField k (AlgebraicClosure k)} [NumberField ↥K] [IsGalois k ↥K]
    {π : Gal(↥K/k) →* H} (hπ : Function.Surjective π)
    {χ : ↥f.ker →* kˣ} (hχinj : Function.Injective χ)
    (hχsurj : ∀ y : kˣ, y ^ n = 1 → ∃ z : ↥f.ker, χ z = y)
    {t : H → G} (ht : ∀ h, f (t h) = h)
    {b : Gal(↥K/k) → (↥K)ˣ}
    (hb : ∀ g h : Gal(↥K/k), g • b h / b (g * h) * b g =
      Units.map (algebraMap k ↥K : k →* ↥K)
        (χ ⟨sectionFactorSet t (π g) (π h), sectionFactorSet_mem_ker f ht _ _⟩)) :
    ∃ M : IntermediateField k (AlgebraicClosure k), NumberField ↥M ∧ IsGalois k ↥M ∧
      ∃ φ : Gal(↥M/k) →* G, Function.Surjective φ := by
  classical
  have hapow : ∀ x y : Gal(↥K/k),
      χ ⟨sectionFactorSet t (π x) (π y), sectionFactorSet_mem_ker f ht _ _⟩ ^ n = 1 := by
    intro x y
    rw [← map_pow, ← hcard, pow_card_eq_one', map_one]
  obtain ⟨M, hMnf, hMgal, ρ, hρ, c, hcpow, hc⟩ :=
    exists_intermediateField_cochain_of_isMulCoboundary hζ hapow hb
  haveI := hMnf
  haveI := hMgal
  choose cZ hcZ using fun g : Gal(↥M/k) => hχsurj (c g) (hcpow g)
  have hcob : ∀ x y : Gal(↥M/k),
      sectionFactorSet t ((π.comp ρ) x) ((π.comp ρ) y)
        = ((cZ x : G) * (cZ y : G) * ((cZ (x * y) : G))⁻¹) := by
    intro x y
    have hker : (⟨sectionFactorSet t (π (ρ x)) (π (ρ y)),
        sectionFactorSet_mem_ker f ht _ _⟩ : ↥f.ker) = cZ x * cZ y * (cZ (x * y))⁻¹ := by
      refine hχinj ?_
      rw [map_mul, map_mul, map_inv, hcZ, hcZ, hcZ]
      exact hc x y
    exact congrArg Subtype.val hker
  obtain ⟨φ, hφsurj, -⟩ := exists_surjective_hom_comp_eq_of_sectionFactorSet_eq f hZ hfr
    (π.comp ρ) (hπ.comp hρ) ht (c := fun x => (cZ x : G)) (fun x => (cZ x).2) hcob
  exact ⟨M, hMnf, hMgal, φ, hφsurj⟩

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem with kernel of odd order whose obstruction is a
coboundary at every ramified finite place is solvable over a larger extension.**  The factor set of
a section of `f`, transported into `kˣ` by the identification of the kernel with the `n`-th roots of
unity, is a two-cocycle killed by `n`; the Albert-Brauer-Hasse-Noether theorem for cocycles of odd
order makes it a coboundary in the units of the extension, and the previous theorem finishes. -/
theorem exists_surjective_hom_of_forall_ramified
    {n : ℕ} [NeZero n] (hn : Odd n) {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = n)
    {K : IntermediateField k (AlgebraicClosure k)} [NumberField ↥K] [IsGalois k ↥K]
    {π : Gal(↥K/k) →* H} (hπ : Function.Surjective π)
    {χ : ↥f.ker →* kˣ} (hχinj : Function.Injective χ)
    (hχsurj : ∀ y : kˣ, y ^ n = 1 → ∃ z : ↥f.ker, χ z = y)
    {t : H → G} (ht : ∀ h, f (t h) = h)
    (hram : ∀ v : HeightOneSpectrum (𝓞 ↥K), ¬ Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal →
      ∃ c : ↥(stabilizer Gal(↥K/k) v) → Additive (v.adicCompletion ↥K)ˣ,
      ∀ s u : ↥(stabilizer Gal(↥K/k) v),
        Additive.ofMul (adicUnitHom v (Units.map (algebraMap k ↥K : k →* ↥K)
          (χ ⟨sectionFactorSet t (π s.1) (π u.1), sectionFactorSet_mem_ker f ht _ _⟩)))
          = smulUnitsAut s (c u) - c (s * u) + c s) :
    ∃ M : IntermediateField k (AlgebraicClosure k), NumberField ↥M ∧ IsGalois k ↥M ∧
      ∃ φ : Gal(↥M/k) →* G, Function.Surjective φ := by
  classical
  set a : Gal(↥K/k) → Gal(↥K/k) → kˣ := fun x y =>
    χ ⟨sectionFactorSet t (π x) (π y), sectionFactorSet_mem_ker f ht _ _⟩ with hadef
  have hapow : ∀ x y, a x y ^ n = 1 := by
    intro x y
    rw [hadef]
    show χ _ ^ n = 1
    rw [← map_pow, ← hcard, pow_card_eq_one', map_one]
  have hacoc : ∀ x y z : Gal(↥K/k), a y z * a x (y * z) = a (x * y) z * a x y := by
    intro x y z
    have hcom : Commute (sectionFactorSet t (π x) (π y))
        (sectionFactorSet t (π x * π y) (π z)) :=
      (Subgroup.mem_center_iff.1 (hZ (sectionFactorSet_mem_ker f ht (π x) (π y))) _).symm
    have hker : (⟨sectionFactorSet t (π y) (π z), sectionFactorSet_mem_ker f ht _ _⟩ : ↥f.ker)
          * ⟨sectionFactorSet t (π x) (π (y * z)), sectionFactorSet_mem_ker f ht _ _⟩
        = ⟨sectionFactorSet t (π (x * y)) (π z), sectionFactorSet_mem_ker f ht _ _⟩
          * ⟨sectionFactorSet t (π x) (π y), sectionFactorSet_mem_ker f ht _ _⟩ := by
      refine Subtype.ext ?_
      show sectionFactorSet t (π y) (π z) * sectionFactorSet t (π x) (π (y * z))
        = sectionFactorSet t (π (x * y)) (π z) * sectionFactorSet t (π x) (π y)
      rw [map_mul π x y, map_mul π y z,
        ← sectionFactorSet_cocycle f hZ ht (π x) (π y) (π z), hcom.eq]
    rw [hadef]
    show χ _ * χ _ = χ _ * χ _
    rw [← map_mul, ← map_mul, hker]
  obtain ⟨b, hb⟩ := exists_isMulCoboundary_of_odd (k := k) (K := ↥K) hn hapow hacoc hram
  exact exists_surjective_hom_of_isMulCoboundary hζ hZ hfr hcard hπ hχinj hχsurj ht hb

section LocalLift

variable {K : Type} [Field K] [NumberField K] [Algebra k K] [IsGalois k K]

omit [NumberField k] [IsGalois k K] in
/-- **A homomorphic lift over the decomposition group at a finite place makes the obstruction a
coboundary there.**  The difference between the section of `f` and the lift takes its values in the
kernel, hence in the centre, and the factor set of the section is exactly its coboundary; applying
the character of the kernel and embedding into the completion turns that identity into the local
coboundary condition. -/
theorem exists_local_coboundary_of_exists_lift
    {G H : Type*} [Group G] [Group H] {f : G →* H} (hZ : f.ker ≤ Subgroup.center G)
    {π : Gal(K/k) →* H} {t : H → G} (ht : ∀ h, f (t h) = h) (χ : ↥f.ker →* kˣ)
    (v : HeightOneSpectrum (𝓞 K))
    {σ : ↥(stabilizer Gal(K/k) v) →* G} (hσ : ∀ s, f (σ s) = π s.1) :
    ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s u : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (Units.map (algebraMap k K : k →* K)
          (χ ⟨sectionFactorSet t (π s.1) (π u.1), sectionFactorSet_mem_ker f ht _ _⟩)))
          = smulUnitsAut s (c u) - c (s * u) + c s := by
  classical
  have hd : ∀ w : ↥(stabilizer Gal(K/k) v), t (π w.1) * (σ w)⁻¹ ∈ f.ker := fun w =>
    mem_ker_mul_inv f ht (π.comp (Subgroup.subtype _)) hσ w
  refine ⟨fun w => Additive.ofMul (adicUnitHom v (Units.map (algebraMap k K : k →* K)
    (χ ⟨t (π w.1) * (σ w)⁻¹, hd w⟩))), fun s u => ?_⟩
  rw [smulUnitsAut_adicUnitHom_algebraMap]
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
/-- **A central Frattini embedding problem with kernel of odd order that is solvable over the
decomposition group at every ramified finite place is solvable over a larger extension.**  This is
the local-global principle in its final form: the only arithmetic input is a homomorphic lift of the
restriction of `π` to each decomposition group at a ramified place. -/
theorem exists_surjective_hom_of_forall_ramified_lift
    {n : ℕ} [NeZero n] (hn : Odd n) {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = n)
    {K : IntermediateField k (AlgebraicClosure k)} [NumberField ↥K] [IsGalois k ↥K]
    {π : Gal(↥K/k) →* H} (hπ : Function.Surjective π)
    {χ : ↥f.ker →* kˣ} (hχinj : Function.Injective χ)
    (hχsurj : ∀ y : kˣ, y ^ n = 1 → ∃ z : ↥f.ker, χ z = y)
    {t : H → G} (ht : ∀ h, f (t h) = h)
    (hlift : ∀ v : HeightOneSpectrum (𝓞 ↥K), ¬ Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal →
      ∃ σ : ↥(stabilizer Gal(↥K/k) v) →* G, ∀ s, f (σ s) = π s.1) :
    ∃ M : IntermediateField k (AlgebraicClosure k), NumberField ↥M ∧ IsGalois k ↥M ∧
      ∃ φ : Gal(↥M/k) →* G, Function.Surjective φ := by
  refine exists_surjective_hom_of_forall_ramified hn hζ hZ hfr hcard hπ hχinj hχsurj ht
    (fun v hv => ?_)
  obtain ⟨σ, hσ⟩ := hlift v hv
  exact exists_local_coboundary_of_exists_lift (k := k) (K := ↥K) hZ ht χ v hσ

end InverseGalois.CFT
