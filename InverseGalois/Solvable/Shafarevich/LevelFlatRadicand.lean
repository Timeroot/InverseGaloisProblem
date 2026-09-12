/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.InertiaCharLift
import InverseGalois.CFT.Profinite.KummerConjTwist
import InverseGalois.Solvable.Shafarevich.InertiaCyclic
import InverseGalois.Solvable.Shafarevich.KernelKummer

/-!
# The homomorphism of the kernel carried by the powers of a single unit

At a prime away from the exponent, the part of inertia the base realization kills is carried by a
single element modulo an open subgroup, so a prescribed homomorphism there is a power of one of its
own values and the arithmetic which answers it need produce only one radicand.  This file assembles
what one radicand gives: the homomorphism built out of the powers of a single unit of the level,
its behaviour under conjugation of the argument, the proportionality of any smooth character of
that part of inertia to the Kummer character of the unit, and one open subgroup on which a whole
finite family of such homomorphisms is trivial at once.

The conjugation formula is what lets the prescription be made at a single prime.  An automorphism
of the extension over the base carries the chosen root of unity to a power of itself, and it
carries a unit which it fixes up to an exponent-th power to a unit with the same Kummer class;
conjugating the argument of the character therefore multiplies it by that power alone, and the
homomorphism assembled out of the powers of that unit is raised to the same power.  That is exactly
the equivariance a prescription at one prime can ask for: equivariance for the whole group would
ask the radicand to be rational.

## Main results

* `InverseGalois.Shafarevich.kummerKernelHom_units_pow_apply` — the homomorphism assembled out of
  the powers of a single unit is a single power of a single element of the target.
* `InverseGalois.Shafarevich.kummerKernelHom_units_pow_conj` — **conjugating the argument by an
  automorphism which fixes the radicand up to an exponent-th power raises the assembled
  homomorphism to the power by which that automorphism raises the roots of unity.**
* `InverseGalois.Shafarevich.exists_forall_eq_mul_kummerChar` — **every smooth character of the
  part of inertia the base realization kills is proportional to the Kummer character of a unit
  whose own character there takes a unit value.**
* `InverseGalois.Shafarevich.exists_isUnit_kummerChar_of_not_dvd_ord` — a unit whose order at the
  place below a prime is prime to the exponent has a Kummer character taking a unit value there.
* `InverseGalois.Shafarevich.exists_isOpenNormal_forall_kummerKernelHom_eq_one` — one open normal
  subgroup on which every member of a finite family of assembled homomorphisms is trivial.

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, radicand, inertia subgroup, character
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### Powers modulo the exponent -/

section Pow

variable {ℓ : ℕ}

/-- Two powers of an element killed by the exponent whose exponents agree modulo the exponent are
equal. -/
theorem pow_eq_pow_of_pow_eq_one {M : Type*} [Monoid M] {V : M} (hV : V ^ ℓ = 1) {i j : ℕ}
    (hij : (i : ZMod ℓ) = (j : ZMod ℓ)) : V ^ i = V ^ j := by
  rw [← pow_mod_of_pow_eq_one hV i, ← pow_mod_of_pow_eq_one hV j,
    (ZMod.natCast_eq_natCast_iff' i j ℓ).1 hij]

/-- A product of powers of elements killed by the exponent is killed by the exponent. -/
theorem prod_pow_val_pow_eq_one {M : Type*} [CommMonoid M] {d : ℕ} {b : Fin d → M}
    (hb : ∀ t, b t ^ ℓ = 1) (m : Fin d → ZMod ℓ) : (∏ t, b t ^ (m t).val) ^ ℓ = 1 := by
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun t _ => ?_
  rw [← pow_mul, mul_comm (m t).val ℓ, pow_mul, hb t, one_pow]

end Pow

/-! ### A character vanishing where a smooth homomorphism is trivial -/

section Smooth

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*} [CommGroup M] {ℓ : ℕ}

/-- A character vanishing wherever a smooth homomorphism is trivial is itself smooth. -/
theorem isSmooth₁_of_map_eq_one {a : G →* M} (hasm : IsSmooth₁ ((a : G →* M) : G → M))
    {e : G → ZMod ℓ} (headd : ∀ x y : G, e (x * y) = e x + e y)
    (hetriv : ∀ x : G, a x = 1 → e x = 0) : IsSmooth₁ e := by
  obtain ⟨N, hN, hcon⟩ := hasm
  refine ⟨N, hN, fun x n hn => ?_⟩
  have h2 : a x * a n = a x := by
    rw [← _root_.map_mul]
    exact hcon x n hn
  have h1 : a n = 1 := mul_left_cancel (h2.trans (mul_one (a x)).symm)
  rw [headd, hetriv n h1, add_zero]

end Smooth

/-! ### The homomorphism carried by the powers of a single unit -/

section Single

variable {ℓ : ℕ} [NeZero ℓ] {k Ω U : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [Group U] {φ : Gal(Ω/k) →* U} {K : IntermediateField k Ω} [NumberField ↥K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ ℓ}

attribute [local instance] zmodTrivialAction

variable (hKker : K.fixingSubgroup = φ.ker)
  (h : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)
  {M : Type*} [CommGroup M] {d : ℕ} (b : Fin d → M) (hb : ∀ t, b t ^ ℓ = 1)

omit [NumberField ↥K] in
/-- **The homomorphism assembled out of the powers of a single unit is a single power of a single
element of the target**, the exponent being the Kummer character of that unit. -/
theorem kummerKernelHom_units_pow_apply (z : (↥K)ˣ) (m : Fin d → ZMod ℓ) (y : ↥φ.ker) :
    kummerKernelHom hKker h b hb (fun t => z ^ (m t).val) y
      = (∏ t, b t ^ (m t).val) ^ (kummerChar h z (kerGalEquiv hKker y)).val := by
  rw [kummerKernelHom_apply, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun t _ => ?_
  show b t ^ (kummerChar h (z ^ (m t).val) (kerGalEquiv hKker y)).val
    = (b t ^ (m t).val) ^ (kummerChar h z (kerGalEquiv hKker y)).val
  rw [kummerChar_units_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, ZMod.val_mul,
    pow_mod_of_pow_eq_one (hb t), ← pow_mul]

variable [Normal k ↥K]

omit [NumberField ↥K] in
/-- **Conjugating the argument by an automorphism which fixes the radicand up to an exponent-th
power raises the assembled homomorphism to the power by which that automorphism raises the roots of
unity.**  The Kummer character of such a unit is multiplied by that power under conjugation of the
argument, and the assembled homomorphism is a power of one element with the character as its
exponent. -/
theorem kummerKernelHom_units_pow_conj (z : (↥K)ˣ) (m : Fin d → ZMod ℓ) {g : Gal(Ω/k)} {e : ℕ}
    (hgζ : g • kummerRootUnit Ω hζ = kummerRootUnit Ω hζ ^ e) {s : (↥K)ˣ}
    (hgz : AlgEquiv.restrictNormalHom (↥K) g • z = z * s ^ ℓ) (y : ↥φ.ker)
    (hy : g * (y : Gal(Ω/k)) * g⁻¹ ∈ φ.ker) :
    kummerKernelHom hKker h b hb (fun t => z ^ (m t).val) ⟨g * (y : Gal(Ω/k)) * g⁻¹, hy⟩
      = kummerKernelHom hKker h b hb (fun t => z ^ (m t).val) y ^ e := by
  have hτ : galSubHom K (kerGalEquiv hKker ⟨g * (y : Gal(Ω/k)) * g⁻¹, hy⟩)
      = g * galSubHom K (kerGalEquiv hKker y) * g⁻¹ := by
    rw [galSubHom_kerGalEquiv, galSubHom_kerGalEquiv]
  have hconj : kummerChar h z (kerGalEquiv hKker ⟨g * (y : Gal(Ω/k)) * g⁻¹, hy⟩)
      = (e : ZMod ℓ) * kummerChar h z (kerGalEquiv hKker y) :=
    kummerChar_conj_of_smul_eq_mul_pow h hgζ hgz hτ
  rw [kummerKernelHom_units_pow_apply, kummerKernelHom_units_pow_apply, hconj, ← pow_mul]
  refine pow_eq_pow_of_pow_eq_one (prod_pow_val_pow_eq_one hb m) ?_
  push_cast [ZMod.natCast_zmod_val]
  ring

end Single

/-! ### The characters of the part of inertia the base realization kills -/

section Line

variable {ℓ : ℕ} [NeZero ℓ] {k Ω U : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [IsAlgClosed Ω] [Group U] {φ : Gal(Ω/k) →* U} {K : IntermediateField k Ω} [NumberField ↥K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ ℓ}

attribute [local instance] zmodTrivialAction

variable (hKker : K.fixingSubgroup = φ.ker)
  (h : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)

/-- **Every smooth character of the part of inertia the base realization kills is proportional to
the Kummer character of a unit whose own character there takes a unit value.**

Read over the level the base realization cuts out, that subgroup is the whole inertia subgroup
there, and every element of it comes from an automorphism over the level; two characters of inertia
at a prime away from the exponent, each trivial on an open subgroup, are proportional as soon as
one of them takes a unit value. -/
theorem exists_forall_eq_mul_kummerChar {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥)
    (hℓP : (ℓ : 𝓞 Ω) ∉ P) {A : Subgroup Gal(Ω/k)}
    (hA : A = Ideal.inertia Gal(Ω/k) P ⊓ φ.ker) (hAker : A ≤ φ.ker)
    {χ : ↥A → ZMod ℓ} (hχadd : ∀ x y : ↥A, χ (x * y) = χ x + χ y) (hχsm : IsSmooth₁ χ)
    (z : (↥K)ˣ) {x₁ : ↥A}
    (hx₁ : IsUnit (kummerChar h z (kerGalEquiv hKker ⟨(x₁ : Gal(Ω/k)), hAker x₁.2⟩))) :
    ∃ c : ZMod ℓ, ∀ x : ↥A,
      χ x = c * kummerChar h z (kerGalEquiv hKker ⟨(x : Gal(Ω/k)), hAker x.2⟩) := by
  have hB : A.comap (galSubHom K) = Ideal.inertia Gal(Ω/↥K) P :=
    comap_galSubHom_eq_inertia hKker hA
  obtain ⟨s, hsc⟩ : ∃ s : ↥(Ideal.inertia Gal(Ω/↥K) P) →* ↥A,
      ∀ x : ↥(Ideal.inertia Gal(Ω/↥K) P), (s x : Gal(Ω/k)) = galSubHom K (x : Gal(Ω/↥K)) :=
    ⟨((galSubHom K).subgroupComap A).comp (MulEquiv.subgroupCongr hB).symm.toMonoidHom,
      fun _ => rfl⟩
  have hker : ∀ (x : ↥A) (x' : ↥(Ideal.inertia Gal(Ω/↥K) P)), s x' = x →
      kerGalEquiv hKker ⟨(x : Gal(Ω/k)), hAker x.2⟩ = (x' : Gal(Ω/↥K)) := by
    intro x x' hx
    refine galSubHom_injective K ?_
    rw [galSubHom_kerGalEquiv, ← hx, hsc]
  have hsurj : ∀ x : ↥A, ∃ x' : ↥(Ideal.inertia Gal(Ω/↥K) P), s x' = x := by
    intro x
    have hxA : (x : Gal(Ω/k)) ∈ Ideal.inertia Gal(Ω/k) P ⊓ φ.ker := by rw [← hA]; exact x.2
    have hyA : (kerGalEquiv hKker ⟨(x : Gal(Ω/k)), (Subgroup.mem_inf.1 hxA).2⟩ : Gal(Ω/↥K))
        ∈ Ideal.inertia Gal(Ω/↥K) P := by
      rw [← hB]
      refine Subgroup.mem_comap.2 ?_
      rw [galSubHom_kerGalEquiv]
      exact x.2
    exact ⟨⟨_, hyA⟩, Subtype.ext (by rw [hsc]; exact galSubHom_kerGalEquiv hKker _)⟩
  have hχ'sm : ∃ N : Subgroup Gal(Ω/↥K), IsOpen (N : Set Gal(Ω/↥K)) ∧
      ∀ x' : ↥(Ideal.inertia Gal(Ω/↥K) P), (x' : Gal(Ω/↥K)) ∈ N → χ (s x') = 0 := by
    obtain ⟨N₀, hN₀, hcon⟩ := hχsm
    obtain ⟨E, hEfin, hEN⟩ := exists_fixingSubgroup_forall_mem hN₀.isOpen
    haveI := hEfin
    refine ⟨E.fixingSubgroup.comap (galSubHom K), ?_, fun x' hx' => ?_⟩
    · rw [Subgroup.coe_comap]
      exact E.fixingSubgroup_isOpen.preimage (continuous_galSubHom K)
    · have h1 := hcon 1 (s x') (hEN (s x') (by rw [hsc]; exact Subgroup.mem_comap.1 hx'))
      rwa [one_mul, zmodChar_one_eq_zero hχadd] at h1
  have hψ'sm : ∃ N : Subgroup Gal(Ω/↥K), IsOpen (N : Set Gal(Ω/↥K)) ∧
      ∀ x' : ↥(Ideal.inertia Gal(Ω/↥K) P), (x' : Gal(Ω/↥K)) ∈ N →
        kummerChar h z (x' : Gal(Ω/↥K)) = 0 := by
    obtain ⟨N, hN, hNz⟩ := exists_isOpen_forall_kummerChar_eq_zero h z
    exact ⟨N, hN, fun x' hx' => hNz _ hx'⟩
  obtain ⟨x₁', hx₁'⟩ := hsurj x₁
  have hu₁ : IsUnit (kummerChar h z (x₁' : Gal(Ω/↥K))) := by
    rw [← hker x₁ x₁' hx₁']
    exact hx₁
  obtain ⟨c, hc⟩ := exists_forall_zmodChar_eq_mul (n := ℓ) hP hℓP
    (χ := fun x' => χ (s x')) (ψ := fun x' => kummerChar h z (x' : Gal(Ω/↥K)))
    (fun x' y' => by
      show χ (s (x' * y')) = χ (s x') + χ (s y')
      rw [_root_.map_mul, hχadd])
    (fun x' y' => by
      show kummerChar h z ((x' : Gal(Ω/↥K)) * (y' : Gal(Ω/↥K))) = _
      exact kummerChar_mul h z _ _)
    hχ'sm hψ'sm hu₁
  refine ⟨c, fun x => ?_⟩
  obtain ⟨x', hx'⟩ := hsurj x
  rw [hker x x' hx', ← hx']
  exact hc x'

omit [IsAlgClosed Ω] in
/-- **A unit whose order at the place below a prime is prime to the exponent has a Kummer character
taking a unit value somewhere on the part of inertia the base realization kills.**  Some element of
the inertia subgroup read over the level has Kummer character not divisible by the exponent, which
for a prime exponent is a value which is a unit; and that subgroup is exactly the part of inertia
the base realization kills, read over the level. -/
theorem exists_isUnit_kummerChar_of_not_dvd_ord (hℓ : ℓ.Prime) {P : Ideal (𝓞 Ω)} [P.IsPrime]
    {A : Subgroup Gal(Ω/k)} (hA : A = Ideal.inertia Gal(Ω/k) P ⊓ φ.ker) (hAker : A ≤ φ.ker)
    (z : (↥K)ˣ) {v : HeightOneSpectrum (𝓞 ↥K)} (hv : v.asIdeal = Ideal.under (𝓞 ↥K) P)
    (hord : ¬ (ℓ : ℤ) ∣ Rigidity.RET.ord ↥K v (z : ↥K)) :
    ∃ x₁ : ↥A, IsUnit (kummerChar h z (kerGalEquiv hKker ⟨(x₁ : Gal(Ω/k)), hAker x₁.2⟩)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : IsGalois ↥K Ω := IsGalois.tower_top_of_isGalois k ↥K Ω
  obtain ⟨σ, hσI, hσ⟩ := exists_mem_inertia_not_dvd_kummerChar h hℓ dvd_rfl z hv hord
  have hB : A.comap (galSubHom K) = Ideal.inertia Gal(Ω/↥K) P :=
    comap_galSubHom_eq_inertia hKker hA
  have hmem : galSubHom K σ ∈ A := Subgroup.mem_comap.1 (by rw [hB]; exact hσI)
  refine ⟨⟨galSubHom K σ, hmem⟩, ?_⟩
  show IsUnit (kummerChar h z (kerGalEquiv hKker ⟨galSubHom K σ, hAker hmem⟩))
  rw [show kerGalEquiv hKker ⟨galSubHom K σ, hAker hmem⟩ = σ from
    galSubHom_injective K (by rw [galSubHom_kerGalEquiv])]
  refine isUnit_iff_ne_zero.2 fun h0 => hσ ?_
  rw [h0]
  exact dvd_zero _

end Line

/-! ### One open subgroup for a whole family -/

section Family

variable {ℓ : ℕ} [NeZero ℓ] {k Ω U : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [Group U] {φ : Gal(Ω/k) →* U} {K : IntermediateField k Ω} [FiniteDimensional k ↥K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ ℓ}

attribute [local instance] zmodTrivialAction

variable (hKker : K.fixingSubgroup = φ.ker)
  (h : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)
  {M : Type*} [CommGroup M] {d : ℕ} (b : Fin d → M) (hb : ∀ t, b t ^ ℓ = 1)

/-- **One open normal subgroup on which every member of a finite family of assembled homomorphisms
is trivial**: the subgroup cutting out the finite level generated by the level itself and the
chosen roots of all the units of all the families. -/
theorem exists_isOpenNormal_forall_kummerKernelHom_eq_one {ι : Type*} [Finite ι]
    (z : ι → Fin d → (↥K)ˣ) :
    ∃ V : Subgroup Gal(Ω/k), IsOpenNormal V ∧
      ∀ (μ : ι) (y : ↥φ.ker), (y : Gal(Ω/k)) ∈ V →
        kummerKernelHom hKker h b hb (z μ) y = 1 := by
  classical
  set rts : Set Ω := Set.range fun p : ι × Fin d => ((h.root (z p.1 p.2) : Ωˣ) : Ω) with hrts
  haveI : Finite ↥rts := by rw [hrts]; exact (Set.finite_range _).to_subtype
  haveI : FiniteDimensional k ↥(IntermediateField.adjoin k rts) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  set W : IntermediateField k Ω := normalClosure k ↥(K ⊔ IntermediateField.adjoin k rts) Ω with hW
  haveI : FiniteDimensional k ↥W := by rw [hW]; infer_instance
  haveI : Normal k ↥W := by rw [hW]; infer_instance
  have hrle : rts ⊆ (W : Set Ω) := fun x hx =>
    le_trans le_sup_right (IntermediateField.le_normalClosure _)
      (IntermediateField.subset_adjoin k rts hx)
  refine ⟨W.fixingSubgroup, isOpenNormal_fixingSubgroup W, fun μ y hy => ?_⟩
  refine kummerKernelHom_eq_one hKker h b hb (z μ) fun t => ?_
  refine (kummerChar_eq_zero_iff_smul_root_eq h (z μ t) _).2 (Units.ext ?_)
  show galSubHom K (kerGalEquiv hKker y) ((h.root (z μ t) : Ωˣ) : Ω)
    = ((h.root (z μ t) : Ωˣ) : Ω)
  rw [galSubHom_kerGalEquiv]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hy _
    (hrle (by rw [hrts]; exact ⟨(μ, t), rfl⟩))

end Family

end InverseGalois.Shafarevich
