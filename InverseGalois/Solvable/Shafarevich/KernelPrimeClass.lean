/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CharLift
import InverseGalois.Solvable.Shafarevich.KernelKummer
import InverseGalois.Solvable.Shafarevich.LayerCoord

/-!
# The local classes which carry a prescription at a named prime

A prescription of the repair names a subgroup of the decomposition subgroup at a prime and a
homomorphism of it into the layer.  Over the level the base realization cuts out that subgroup is
either the whole decomposition subgroup or the inertia subgroup — the part of inertia the base
realization kills is all of inertia once one is over the level, every automorphism there fixing the
level anyway — so Kummer theory names each coordinate of the prescribed homomorphism by a class in
the completion at the place below.

That is the shape an arithmetic construction can answer: a family of units of the level whose
classes at that place are the named ones assembles, by the Kummer dictionary, into a homomorphism
of the kernel of the base realization which restricts to the prescribed one.  The prescription at a
named prime therefore becomes a demand on local classes at one place, and nothing else about the
units is used.

The characters to be named must be trivial on an open subgroup, and that is exactly what
smoothness of the prescribed homomorphism gives: an open subgroup of a subgroup of a Galois group
contains the automorphisms of it which fix a finite extension of the base, and the automorphisms
over the level fixing that extension are an open subgroup there.

## Main results

* `InverseGalois.Shafarevich.exists_fixingSubgroup_forall_mem` — an open subgroup of a subgroup of
  a Galois group contains the automorphisms of the subgroup which fix a finite extension of the
  base.
* `InverseGalois.Shafarevich.comap_galSubHom_eq_stabilizer` — the decomposition subgroup at a prime,
  read over a level, is the decomposition subgroup there.
* `InverseGalois.Shafarevich.comap_galSubHom_eq_inertia` — the part of inertia the base realization
  kills, read over the level it cuts out, is the whole inertia subgroup there.
* `InverseGalois.Shafarevich.exists_localClass_forall_kummerKernelHom_eq` — **a prescription at a
  named prime is named by a family of classes in the completion at the place below**: the
  homomorphism assembled out of any family of units of the level carrying those classes restricts
  to the prescribed one.

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, decomposition group, local class
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### An open subgroup of a subgroup -/

section Open

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- **An open subgroup of a subgroup of a Galois group contains the automorphisms of the subgroup
which fix a finite extension of the base.**  Open subgroups over finite extensions are a basis of
the neighbourhoods of the identity, and the subgroup carries the topology induced from the whole
group. -/
theorem exists_fixingSubgroup_forall_mem {A : Subgroup Gal(Ω/k)} {N : Subgroup ↥A}
    (hN : IsOpen (N : Set ↥A)) :
    ∃ E : IntermediateField k Ω, FiniteDimensional k ↥E ∧
      ∀ x : ↥A, (x : Gal(Ω/k)) ∈ E.fixingSubgroup → x ∈ N := by
  obtain ⟨V, hVopen, hVN⟩ := isOpen_induced_iff.1 hN
  have hV1 : (1 : Gal(Ω/k)) ∈ V := by
    have h1 : (1 : ↥A) ∈ Subtype.val ⁻¹' V := by rw [hVN]; exact N.one_mem
    exact h1
  obtain ⟨E, hEfin, hEV⟩ := (krullTopology_mem_nhds_one_iff k Ω V).1 (hVopen.mem_nhds hV1)
  refine ⟨E, hEfin, fun x hx => ?_⟩
  have hxV : x ∈ Subtype.val ⁻¹' V := hEV hx
  rwa [hVN] at hxV

end Open

/-! ### The two shapes of a prescribed subgroup, read over the level -/

section Comap

variable {k Ω U : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Group U]
  {φ : Gal(Ω/k) →* U} {K : IntermediateField k Ω}

omit [IsGalois k Ω] in
/-- **The decomposition subgroup at a prime, read over a level, is the decomposition subgroup
there.** -/
theorem comap_galSubHom_eq_stabilizer {A : Subgroup Gal(Ω/k)} {P : Ideal (𝓞 Ω)}
    (hA : A = stabilizer Gal(Ω/k) P) :
    A.comap (galSubHom K) = stabilizer Gal(Ω/↥K) P := by
  subst hA
  exact Subgroup.ext fun τ => mem_stabilizer_galSubHom_iff K τ P

omit [IsGalois k Ω] in
/-- **The part of inertia the base realization kills, read over the level it cuts out, is the whole
inertia subgroup there**: an automorphism over the level fixes the level, so it is in the kernel of
the base realization to begin with. -/
theorem comap_galSubHom_eq_inertia {A : Subgroup Gal(Ω/k)} {P : Ideal (𝓞 Ω)}
    (hKker : K.fixingSubgroup = φ.ker) (hA : A = Ideal.inertia Gal(Ω/k) P ⊓ φ.ker) :
    A.comap (galSubHom K) = Ideal.inertia Gal(Ω/↥K) P := by
  subst hA
  refine Subgroup.ext fun τ => ?_
  rw [Subgroup.mem_comap, Subgroup.mem_inf, mem_inertia_galSubHom_iff]
  exact and_iff_left (hKker ▸ galSubHom_mem_fixingSubgroup K τ)

end Comap

/-! ### The prescription at a named prime as a demand on local classes -/

section Prime

variable {ℓ : ℕ} [NeZero ℓ] {k Ω U : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [IsAlgClosed Ω] [Group U] {φ : Gal(Ω/k) →* U} {K : IntermediateField k Ω} [NumberField ↥K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ ℓ}

attribute [local instance] zmodTrivialAction

variable (hKker : K.fixingSubgroup = φ.ker)
  (h : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)

/-- **A prescription at a named prime is named by a family of classes in the completion at the place
below**: the homomorphism assembled out of any family of units of the level carrying those classes
restricts to the prescribed one.

Each coordinate of the prescribed homomorphism is a character of the subgroup, read over the level
as a character of the decomposition subgroup there or of the whole inertia subgroup there, and such
a character is the Kummer character of any unit of the level with the named class.  Smoothness of
the prescribed homomorphism is what makes each character trivial on an open subgroup. -/
theorem exists_localClass_forall_kummerKernelHom_eq (hlift : HasKummerCharInertiaLift h)
    {M : Type*} [CommGroup M] {d : ℕ} (b : Fin d → M) (hb : ∀ t, b t ^ ℓ = 1)
    {χ : Fin d → M → ZMod ℓ} (hχ : ∀ m : M, ∏ t, b t ^ (χ t m).val = m)
    (hχadd : ∀ (t : Fin d) (m m' : M), χ t (m * m') = χ t m + χ t m')
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥) {v : HeightOneSpectrum (𝓞 ↥K)}
    (hv : v.asIdeal = Ideal.under (𝓞 ↥K) P) {A : Subgroup Gal(Ω/k)}
    (hA : A = stabilizer Gal(Ω/k) P ∨ (A = Ideal.inertia Gal(Ω/k) P ⊓ φ.ker ∧ (ℓ : 𝓞 Ω) ∉ P))
    (a : ↥A →* M) (hasm : IsSmooth₁ (a : ↥A → M)) :
    ∃ c : Fin d → localClasses v ℓ, ∀ z : Fin d → (↥K)ˣ,
      (∀ t, localClassHom v ℓ (z t) = c t) →
        ∀ (x : ↥A) (hx : (x : Gal(Ω/k)) ∈ φ.ker),
          kummerKernelHom hKker h b hb z ⟨(x : Gal(Ω/k)), hx⟩ = a x := by
  classical
  have hA' : A.comap (galSubHom K) = stabilizer Gal(Ω/↥K) P ∨
      (A.comap (galSubHom K) = Ideal.inertia Gal(Ω/↥K) P ∧ (ℓ : 𝓞 Ω) ∉ P) := by
    rcases hA with hA | ⟨hA, hℓP⟩
    · exact Or.inl (comap_galSubHom_eq_stabilizer hA)
    · exact Or.inr ⟨comap_galSubHom_eq_inertia hKker hA, hℓP⟩
  set r : ↥(A.comap (galSubHom K)) →* ↥A := (galSubHom K).subgroupComap A with hr
  have hrc : ∀ x : ↥(A.comap (galSubHom K)),
      (r x : Gal(Ω/k)) = galSubHom K (x : Gal(Ω/↥K)) := fun _ => rfl
  have hadd : ∀ (t : Fin d) (x y : ↥(A.comap (galSubHom K))),
      χ t (a (r (x * y))) = χ t (a (r x)) + χ t (a (r y)) := by
    intro t x y
    rw [_root_.map_mul, _root_.map_mul, hχadd]
  have hone : ∀ t : Fin d, χ t (1 : M) = 0 := fun t =>
    map_one_eq_zero_of_map_mul_eq_add (hχadd t)
  have hsm : ∀ t : Fin d, ∃ N : Subgroup Gal(Ω/↥K), IsOpen (N : Set Gal(Ω/↥K)) ∧
      ∀ x : ↥(A.comap (galSubHom K)), (x : Gal(Ω/↥K)) ∈ N → χ t (a (r x)) = 0 := by
    intro t
    obtain ⟨N₀, hN₀, hcon⟩ := hasm
    obtain ⟨E, hEfin, hEN⟩ := exists_fixingSubgroup_forall_mem hN₀.isOpen
    haveI := hEfin
    refine ⟨E.fixingSubgroup.comap (galSubHom K), ?_, fun x hx => ?_⟩
    · rw [Subgroup.coe_comap]
      exact E.fixingSubgroup_isOpen.preimage (continuous_galSubHom K)
    · have hker : a (r x) = 1 := by
        have h1 := hcon 1 (r x) (hEN (r x) (by rw [hrc]; exact Subgroup.mem_comap.1 hx))
        rwa [one_mul, _root_.map_one] at h1
      rw [hker, hone]
  have hex : ∀ t : Fin d, ∃ c : localClasses v ℓ, ∀ u : (↥K)ˣ, localClassHom v ℓ u = c →
      ∀ x : ↥(A.comap (galSubHom K)),
        kummerChar h u (x : Gal(Ω/↥K)) = χ t (a (r x)) := fun t =>
    exists_localClass_forall_kummerChar_eq h hlift hP hv hA' _ (hadd t) (hsm t)
  choose c hc using hex
  refine ⟨c, fun z hz x hx => ?_⟩
  refine kummerKernelHom_eq_of_forall_kummerChar_eq hKker h b hb z hχ fun t => ?_
  have hxA' : (kerGalEquiv hKker ⟨(x : Gal(Ω/k)), hx⟩ : Gal(Ω/↥K)) ∈ A.comap (galSubHom K) := by
    refine Subgroup.mem_comap.2 ?_
    rw [galSubHom_kerGalEquiv]
    exact x.2
  have hval := hc t (z t) (hz t) ⟨_, hxA'⟩
  refine hval.trans (congrArg (χ t) (congrArg a (Subtype.ext ?_)))
  rw [hrc]
  exact galSubHom_kerGalEquiv hKker _

end Prime

end InverseGalois.Shafarevich
