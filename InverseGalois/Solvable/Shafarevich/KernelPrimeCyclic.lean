/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.InertiaCharLift
import InverseGalois.Solvable.Shafarevich.KernelPrimeClass

/-!
# A prescription with cyclic values is named by classes on a single line

A prescription at a named prime is a homomorphism of the decomposition subgroup there into the
layer, and each of its coordinates is named by a class in the completion at the place below.  The
classes so named are unrelated to one another, and a family of units of the level carrying an
unrelated family of classes at a family of places is more than the reciprocity law permits: the
power residue symbol of two coordinates over all the places is trivial, and away from the named
places the symbol contributes nothing, so the coordinates at the named places satisfy one relation.

The relation is empty as soon as the prescribed classes lie on a single line, because the symbol is
alternating.  That is the case here whenever the prescription itself has cyclic image: the
coordinates of a homomorphism with cyclic image are all multiples of one character of the subgroup,
carried by one class in the completion, and the coordinates are then the powers of that one class by
the coordinates of a generator of the image.

## Main statements

* `InverseGalois.Shafarevich.exists_zmodChar_forall_eq_smul` — **the coordinates of a homomorphism
  with cyclic image are the multiples of a single character** of the source.
* `InverseGalois.Shafarevich.exists_localClass_zpowers_forall_kummerKernelHom_eq` — **a prescription
  with cyclic values at a named prime is named by a family of classes on a single line**.
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

/-! ### The coordinates of a homomorphism with cyclic image -/

section Cyclic

variable {ℓ : ℕ}

/-- **The coordinates of a homomorphism with cyclic image are the multiples of a single
character.**

A generator of the image carries the whole image, so every value is a power of it and every
coordinate of a value is that power of the corresponding coordinate of the generator.  Dividing one
nonzero coordinate of the generator out of that exhibits the common character; if every coordinate
of the generator vanishes then the generator is trivial and so is the whole homomorphism. -/
theorem exists_zmodChar_forall_eq_smul {A M : Type*} [Group A] [CommGroup M] (hℓ : ℓ.Prime) {d : ℕ}
    {b : Fin d → M} {χ : Fin d → M → ZMod ℓ} (hχ : ∀ m : M, ∏ t, b t ^ (χ t m).val = m)
    (hχadd : ∀ (t : Fin d) (m m' : M), χ t (m * m') = χ t m + χ t m') (a : A →* M)
    (hcyc : ∃ x₀ : A, ∀ x : A, a x ∈ Subgroup.zpowers (a x₀)) :
    ∃ (e : A → ZMod ℓ) (μ : Fin d → ZMod ℓ),
      (∀ x y : A, e (x * y) = e x + e y) ∧ (∀ x : A, a x = 1 → e x = 0) ∧
        ∀ (t : Fin d) (x : A), χ t (a x) = μ t * e x := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨x₀, hx₀⟩ := hcyc
  have hone : ∀ t : Fin d, χ t (1 : M) = 0 := fun t =>
    zmodChar_one_eq_zero fun m m' => hχadd t m m'
  by_cases hm₀ : a x₀ = 1
  · refine ⟨fun _ => 0, fun _ => 0, fun _ _ => (add_zero _).symm, fun _ _ => rfl, fun t x => ?_⟩
    have hax : a x = 1 := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hx₀ x)
      rw [← hi, hm₀, one_zpow]
    rw [hax, hone, mul_zero]
  · have hex : ∃ t : Fin d, χ t (a x₀) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      refine hm₀ ?_
      rw [← hχ (a x₀)]
      refine Finset.prod_eq_one fun t _ => ?_
      rw [hcon t, ZMod.val_zero, pow_zero]
    obtain ⟨t₀, ht₀⟩ := hex
    refine ⟨fun x => (χ t₀ (a x₀))⁻¹ * χ t₀ (a x), fun t => χ t (a x₀), fun x y => ?_,
      fun x hx => ?_, fun t x => ?_⟩
    · show (χ t₀ (a x₀))⁻¹ * χ t₀ (a (x * y))
        = (χ t₀ (a x₀))⁻¹ * χ t₀ (a x) + (χ t₀ (a x₀))⁻¹ * χ t₀ (a y)
      rw [_root_.map_mul, hχadd, mul_add]
    · show (χ t₀ (a x₀))⁻¹ * χ t₀ (a x) = 0
      rw [hx, hone, mul_zero]
    · show χ t (a x) = χ t (a x₀) * ((χ t₀ (a x₀))⁻¹ * χ t₀ (a x))
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hx₀ x)
      rw [← hi, zmodChar_zpow (fun m m' => hχadd t m m'),
        zmodChar_zpow (fun m m' => hχadd t₀ m m'), zsmul_eq_mul, zsmul_eq_mul]
      field_simp

end Cyclic

/-! ### The classes which carry a prescription with cyclic values -/

section Prime

variable {ℓ : ℕ} [NeZero ℓ] {k Ω U : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [IsAlgClosed Ω] [Group U] {φ : Gal(Ω/k) →* U} {K : IntermediateField k Ω} [NumberField ↥K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ ℓ}

attribute [local instance] zmodTrivialAction

variable (hKker : K.fixingSubgroup = φ.ker)
  (h : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)

/-- **A prescription with cyclic values at a named prime is named by a family of classes on a single
line**: the homomorphism assembled out of any family of units of the level carrying those classes
restricts to the prescribed one.

The coordinates of the prescription are the multiples of one character of the subgroup, read over
the level as a character of the decomposition subgroup there or of the whole inertia subgroup there,
and such a character is named by a class in the completion at the place below in the strong sense
that a unit whose class is a power of it carries that multiple of the character.  The coordinates
are then carried by the powers of the one class by the coordinates of a generator of the image. -/
theorem exists_localClass_zpowers_forall_kummerKernelHom_eq (hlift : HasKummerCharInertiaLift h)
    (hℓ : ℓ.Prime) {M : Type*} [CommGroup M] {d : ℕ} (b : Fin d → M) (hb : ∀ t, b t ^ ℓ = 1)
    {χ : Fin d → M → ZMod ℓ} (hχ : ∀ m : M, ∏ t, b t ^ (χ t m).val = m)
    (hχadd : ∀ (t : Fin d) (m m' : M), χ t (m * m') = χ t m + χ t m')
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥) {v : HeightOneSpectrum (𝓞 ↥K)}
    (hv : v.asIdeal = Ideal.under (𝓞 ↥K) P) {A : Subgroup Gal(Ω/k)}
    (hA : A = stabilizer Gal(Ω/k) P ∨ (A = Ideal.inertia Gal(Ω/k) P ⊓ φ.ker ∧ (ℓ : 𝓞 Ω) ∉ P))
    (a : ↥A →* M) (hasm : IsSmooth₁ (a : ↥A → M))
    (hcyc : ∃ x₀ : ↥A, ∀ x : ↥A, a x ∈ Subgroup.zpowers (a x₀)) :
    ∃ (c₀ : localClasses v ℓ) (c : Fin d → localClasses v ℓ),
      (∀ t, c t ∈ Subgroup.zpowers c₀) ∧
        ∀ z : Fin d → (↥K)ˣ, (∀ t, localClassHom v ℓ (z t) = c t) →
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
  obtain ⟨e, μ, headd, hetriv, hemul⟩ := exists_zmodChar_forall_eq_smul hℓ hχ hχadd a hcyc
  have hadd : ∀ x y : ↥(A.comap (galSubHom K)), e (r (x * y)) = e (r x) + e (r y) := by
    intro x y
    rw [_root_.map_mul, headd]
  have hsm : ∃ N : Subgroup Gal(Ω/↥K), IsOpen (N : Set Gal(Ω/↥K)) ∧
      ∀ x : ↥(A.comap (galSubHom K)), (x : Gal(Ω/↥K)) ∈ N → e (r x) = 0 := by
    obtain ⟨N₀, hN₀, hcon⟩ := hasm
    obtain ⟨E, hEfin, hEN⟩ := exists_fixingSubgroup_forall_mem hN₀.isOpen
    haveI := hEfin
    refine ⟨E.fixingSubgroup.comap (galSubHom K), ?_, fun x hx => ?_⟩
    · rw [Subgroup.coe_comap]
      exact E.fixingSubgroup_isOpen.preimage (continuous_galSubHom K)
    · refine hetriv _ ?_
      have h1 := hcon 1 (r x) (hEN (r x) (by rw [hrc]; exact Subgroup.mem_comap.1 hx))
      rwa [one_mul, _root_.map_one] at h1
  obtain ⟨c₀, hc₀⟩ :=
    exists_localClass_forall_kummerChar_nsmul h hlift hP hv hA' (fun x => e (r x)) hadd hsm
  refine ⟨c₀, fun t => c₀ ^ (μ t).val,
    fun t => Subgroup.mem_zpowers_iff.2 ⟨(μ t).val, zpow_natCast c₀ _⟩, fun z hz x hx => ?_⟩
  refine kummerKernelHom_eq_of_forall_kummerChar_eq hKker h b hb z hχ fun t => ?_
  have hxA' : (kerGalEquiv hKker ⟨(x : Gal(Ω/k)), hx⟩ : Gal(Ω/↥K)) ∈ A.comap (galSubHom K) := by
    refine Subgroup.mem_comap.2 ?_
    rw [galSubHom_kerGalEquiv]
    exact x.2
  have hrx : r ⟨_, hxA'⟩ = x := by
    refine Subtype.ext ?_
    rw [hrc]
    exact galSubHom_kerGalEquiv hKker _
  have hval := hc₀ (μ t).val (z t) (hz t) ⟨_, hxA'⟩
  rw [hval, hrx, hemul t x, nsmul_eq_mul, ZMod.natCast_zmod_val]

end Prime

end InverseGalois.Shafarevich
