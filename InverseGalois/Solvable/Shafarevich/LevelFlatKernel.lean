/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LevelFlatTwist

/-!
# The flat prescription, bought over the field the base realization cuts out

Everything the flat prescription asks of a cocycle is read on the kernel of the base realization:
the subgroups it prescribes values along lie inside that kernel, the finite family is asked about
only where the base realization already vanishes, and the clause confining the new ramification is
read along the part of inertia the base realization kills.  So the whole demand is a demand on the
restriction of the cocycle to that kernel, where the action on the layer is trivial and a cocycle is
nothing but a homomorphism.

A homomorphism there is carried back down to the base field not by averaging but by extending it:
choose a set theoretic section of the base realization sending the identity to the identity, and
send an element of the base group to the value of the homomorphism at the element times the inverse
of the section of its image.  That is a cocycle up to the values of the homomorphism at the factor
set of the section, and it is an honest cocycle as soon as those values are killed.  For the
extension to be equivariant for the action of the base group the homomorphism itself is asked to be
equivariant for conjugation, which is exactly what the restriction of a cocycle to the kernel
satisfies.

The point of the extension over the averaging is the count.  The factor set of a section has one
value for each ordered pair of elements of the operator group, a number settled by the operator
group alone, hence known before the number of letters the data is read at is announced.  A single
shrinking of the operator group therefore annihilates the whole factor set at once, and no
prescription is asked to name primes which split completely anywhere.

The prescription upstairs may spend a shrinking of its own, and the two shrinkings compose: the
number of letters the factor set is killed from is fixed first, the prescription is asked to answer
at that number, and the shrinking it spends is followed by the one paying for the factor set.

Along the kernel the section contributes nothing — the identity is sent to the identity — so the
extension agrees with the homomorphism there, and every clause of the prescription transfers
verbatim.

## Main definitions

* `InverseGalois.Shafarevich.HasFlatKernelPrescription` — **an equivariant smooth homomorphism into
  the layer, defined on the kernel of the base realization, can be prescribed along finitely many
  subgroups of decomposition subgroups at once, be trivial along the finite family, and ramify only
  at the named primes or where the given lift carried down kills the whole decomposition subgroup.**

## Main results

* `InverseGalois.Shafarevich.hasFlatPrescription_of_hasFlatKernelPrescription` — **extending a
  prescribed equivariant homomorphism along a section of the base realization carries the flat
  prescription down to the base field**, one further shrinking of the operator group paying for the
  factor set of the section.

## Tags

Shafarevich's theorem, embedding problem, one cocycle, factor set, ramification, decomposition group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT GroupExtension MulAction NumberField groupCohomology

open scoped Pointwise

attribute [local instance] genericQuotAction

set_option maxHeartbeats 1600000

/-! ### The prescription over the larger field -/

section FlatKernel

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S]
  [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] (φ : Gal(Ω/k) →* U) {t : ℕ} (D : Fin t → Subgroup Gal(Ω/k))

/-- **An equivariant smooth homomorphism into the layer, defined on the kernel of the base
realization, can be prescribed along finitely many subgroups of decomposition subgroups at once, be
trivial along the finite family, and ramify only at the named primes or where the given lift carried
down kills the whole decomposition subgroup.**

This is the flat prescription, made one field up.  The base realization acts trivially on the layer
through its kernel, so a cocycle of that kernel is a homomorphism, and the whole demand is one about
homomorphisms of a profinite group into a finite abelian group.

The subgroups the values are prescribed along are the parts of inertia at the named primes which the
base realization kills, the named primes are away from the exponent, and inertia at a named prime is
killed by the base realization outright, so the prime is unramified in the field that realization
cuts out.

The homomorphism is asked to be equivariant for conjugation by the base group, the operators moving
its values as the base realization moves the conjugating element.  That is what a cocycle over the
base field restricts to, and it is what lets the homomorphism be extended back down along a section
of the base realization.  The prescribed values are asked to be equivariant in the same sense, which
is what makes the demand consistent.

Smoothness is asked in the form the extension consumes: the homomorphism kills an open normal
subgroup of the base group, not merely of the kernel.

As for the prescription below, a shrinking may be spent: a number of letters is announced in
advance, the given lift and the prescribed values are read at that number, and what is answered is a
surjection onto the number asked for together with a homomorphism at that number, the prescribed
values being carried across by the map of layers.  The clause confining the new ramification is read
of the given lift carried down along that surjection. -/
def HasFlatKernelPrescription : Prop :=
  ∃ N : ℕ,
    ∀ (F : Gal(Ω/k) →* GenericQuot ℓ U N S (j + 1)) (ι : Type) [Finite ι]
        (Q : ι → Ideal (𝓞 Ω)) (A : ι → Subgroup Gal(Ω/k))
        (a : (μ : ι) → ↥(A μ) →* ↥(layerSub ℓ (Generic U N S) j)),
      Function.Surjective F → IsSmoothHom F →
      (∀ x, SemidirectProduct.rightHom (F x) = φ x) →
      (∀ μ, (Q μ).IsPrime) → (∀ μ, Q μ ≠ ⊥) → (∀ μ, (ℓ : 𝓞 Ω) ∉ Q μ) →
      (∀ μ, A μ ≤ stabilizer Gal(Ω/k) (Q μ)) → (∀ μ, A μ ≤ φ.ker) →
      (∀ μ, A μ = Ideal.inertia Gal(Ω/k) (Q μ) ⊓ φ.ker) →
      (∀ μ, Ideal.inertia Gal(Ω/k) (Q μ) ≤ φ.ker) →
      (∀ μ, IsSmooth₁ ((a μ : ↥(A μ) →* ↥(layerSub ℓ (Generic U N S) j)) :
        ↥(A μ) → ↥(layerSub ℓ (Generic U N S) j))) →
      (∀ (μ : ι) (g : Gal(Ω/k)) (x : ↥(A μ)) (hx : g * (x : Gal(Ω/k)) * g⁻¹ ∈ A μ),
        a μ ⟨g * (x : Gal(Ω/k)) * g⁻¹, hx⟩ = φ g • a μ x) →
        ∃ (β : Generic U N S →* Generic U n S) (hβ : IsOperatorHom β), Function.Surjective β ∧
          ∃ u : ↥(φ.ker) →* ↥(layerSub ℓ (Generic U n S) j),
            (∃ V : Subgroup Gal(Ω/k), IsOpenNormal V ∧
              ∀ y : ↥(φ.ker), (y : Gal(Ω/k)) ∈ V → u y = 1) ∧
            (∀ (g : Gal(Ω/k)) (y : ↥(φ.ker)) (hy : g * (y : Gal(Ω/k)) * g⁻¹ ∈ φ.ker),
              u ⟨g * (y : Gal(Ω/k)) * g⁻¹, hy⟩ = φ g • u y) ∧
            (∀ (ν : Fin t) (y : ↥(φ.ker)), (y : Gal(Ω/k)) ∈ D ν → u y = 1) ∧
            (∀ (μ : ι) (x : ↥(A μ)) (hx : (x : Gal(Ω/k)) ∈ φ.ker),
              u ⟨(x : Gal(Ω/k)), hx⟩ = layerSubMap ℓ β j (a μ x)) ∧
            ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
              (∃ y : ↥(φ.ker), (y : Gal(Ω/k)) ∈ Ideal.inertia Gal(Ω/k) P ∧ u y ≠ 1) →
              (∃ (μ : ι) (ρ : Gal(Ω/k)), P = ρ • Q μ) ∨
                ∀ x ∈ stabilizer Gal(Ω/k) P, layerSemidirectMap ℓ hβ (j + 1) (F x) = 1

end FlatKernel

/-! ### Extending the prescription down along a section -/

section Descent

variable {ℓ : ℕ} [Fact ℓ.Prime] {U : Type} [Group U] [Finite U] {n : ℕ} {S : Type} [Group S]
  [Finite S] {j : ℕ} {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] {φ : Gal(Ω/k) →* U}
  [MulDistribMulAction Gal(Ω/k) ↥(layerSub ℓ (Generic U n S) j)] {t : ℕ}
  {D : Fin t → Subgroup Gal(Ω/k)}

omit [NumberField k] [IsGalois k Ω] [IsAlgClosed Ω] in
/-- **Extending a prescribed equivariant homomorphism along a section of the base realization
carries the flat prescription down to the base field**, one further shrinking of the operator group
paying for the factor set of the section.

The number of letters the factor set is killed from is fixed first, large enough that a single
surjective shrinking of the operator group annihilates any prescribed family of elements of the
layer indexed by ordered pairs of operators.  The prescription upstairs is asked to answer at that
number, and the number of letters it announces in turn is the one the whole assembly announces.  The
factor set of a section of the base realization is such a family, so whatever homomorphism the
prescription answers with, its values on that factor set are killed by one shrinking, and the
extension of the homomorphism along the section is an honest cocycle at the number of letters asked
for.  The two shrinkings compose to the one the assembly answers with.

The extension is equivariant because the homomorphism was: conjugating by the section of the image
of an element moves the value by that image, which is how the base group acts on the layer.  It is
smooth because the homomorphism kills an open normal subgroup of the base group and the given lift
does too, so their intersection is carried into that subgroup by any conjugation.

Along the kernel of the base realization the section is the identity, so the extension is the
homomorphism itself there.  Every clause of the prescription is read along that kernel, and so
transfers verbatim: the prescribed values, the vanishing along the finite family, and the clause
confining the new ramification, whose lift carried down along the first shrinking is the lift
carried down along the composite once the second is applied. -/
theorem hasFlatPrescription_of_hasFlatKernelPrescription (hS : IsPGroup ℓ S)
    (hactφ : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)), x • v = φ x • v)
    (hpres : ∀ M : ℕ, HasFlatKernelPrescription ℓ U M S j φ D) :
    HasFlatPrescription ℓ U n S j φ D := by
  classical
  obtain ⟨N₁, hN₁⟩ := exists_operatorHom_forall_layerSubMap_eq_one U n S hS (j := j) (U × U)
  obtain ⟨N, hN⟩ := hpres N₁
  refine ⟨N, ?_⟩
  intro F ι _ Q A a hFsurj hFsm hFright hQp hQbot hQℓ hAstab hAker hAeq hAunr hasm haequiv
  obtain ⟨β, hβ, hβsurj, u, ⟨V, hV, hVu⟩, hueq, huD, hua, huram⟩ :=
    hN F ι Q A a hFsurj hFsm hFright hQp hQbot hQℓ hAstab hAker hAeq hAunr hasm haequiv
  have hφsurj : Function.Surjective φ := by
    intro v
    obtain ⟨y, hy⟩ := hFsurj (SemidirectProduct.inr v)
    exact ⟨y, by rw [← hFright y, hy, SemidirectProduct.rightHom_inr]⟩
  obtain ⟨s₀, hs₀⟩ := hφsurj.hasRightInverse
  obtain ⟨s, hs, hs1⟩ : ∃ s : U → Gal(Ω/k), (∀ v, φ (s v) = v) ∧ s 1 = 1 := by
    refine ⟨fun v => if v = 1 then 1 else s₀ v, fun v => ?_, by simp⟩
    by_cases hv : v = 1
    · simp [hv]
    · simpa [hv] using hs₀ v
  have hr : ∀ g : Gal(Ω/k), g * (s (φ g))⁻¹ ∈ φ.ker := by
    intro g
    simp [MonoidHom.mem_ker, hs]
  have hζ : ∀ p : U × U, s p.1 * s p.2 * (s (p.1 * p.2))⁻¹ ∈ φ.ker := by
    intro p
    simp only [MonoidHom.mem_ker, _root_.map_mul, _root_.map_inv, hs]
    group
  obtain ⟨α, hα, hαsurj, hα1⟩ :=
    hN₁ fun p : U × U => u ⟨s p.1 * s p.2 * (s (p.1 * p.2))⁻¹, hζ p⟩
  have hkerv : ∀ (x : Gal(Ω/k)) (hx : x ∈ φ.ker),
      (⟨x * (s (φ x))⁻¹, hr x⟩ : ↥(φ.ker)) = ⟨x, hx⟩ := by
    intro x hx
    apply Subtype.ext
    show x * (s (φ x))⁻¹ = x
    rw [MonoidHom.mem_ker.1 hx, hs1, inv_one, mul_one]
  refine ⟨α.comp β, hα.comp hβ, hαsurj.comp hβsurj,
    fun g => layerSubMap ℓ α j (u ⟨g * (s (φ g))⁻¹, hr g⟩), ?_, ?_, ?_, ?_, ?_⟩
  · intro g h
    have hmem : s (φ g) * (h * (s (φ h))⁻¹) * (s (φ g))⁻¹ ∈ φ.ker := by
      simp [MonoidHom.mem_ker, hs]
    have hsplit : (⟨g * h * (s (φ (g * h)))⁻¹, hr (g * h)⟩ : ↥(φ.ker))
        = ⟨g * (s (φ g))⁻¹, hr g⟩ * ⟨s (φ g) * (h * (s (φ h))⁻¹) * (s (φ g))⁻¹, hmem⟩
          * ⟨s (φ g) * s (φ h) * (s (φ g * φ h))⁻¹, hζ (φ g, φ h)⟩ := by
      apply Subtype.ext
      show g * h * (s (φ (g * h)))⁻¹
        = g * (s (φ g))⁻¹ * (s (φ g) * (h * (s (φ h))⁻¹) * (s (φ g))⁻¹)
          * (s (φ g) * s (φ h) * (s (φ g * φ h))⁻¹)
      rw [_root_.map_mul]
      group
    have hconj : u ⟨s (φ g) * (h * (s (φ h))⁻¹) * (s (φ g))⁻¹, hmem⟩
        = φ g • u ⟨h * (s (φ h))⁻¹, hr h⟩ := by
      have h2 := hueq (s (φ g)) ⟨h * (s (φ h))⁻¹, hr h⟩ hmem
      rwa [hs] at h2
    have hz : layerSubMap ℓ α j (u ⟨s (φ g) * s (φ h) * (s (φ g * φ h))⁻¹, hζ (φ g, φ h)⟩) = 1 :=
      hα1 (φ g, φ h)
    show layerSubMap ℓ α j (u ⟨g * h * (s (φ (g * h)))⁻¹, hr (g * h)⟩)
      = g • layerSubMap ℓ α j (u ⟨h * (s (φ h))⁻¹, hr h⟩)
        * layerSubMap ℓ α j (u ⟨g * (s (φ g))⁻¹, hr g⟩)
    rw [hsplit, _root_.map_mul u, _root_.map_mul u, hconj, _root_.map_mul, _root_.map_mul, hz,
      mul_one, layerSubMap_smul hα, hactφ]
    exact mul_comm _ _
  · refine ⟨V ⊓ F.ker, hV.inf (isOpenNormal_ker_of_isSmoothHom hFsm), fun g m hm => ?_⟩
    have hmφ : φ m = 1 := by
      rw [← hFright m, MonoidHom.mem_ker.1 hm.2, _root_.map_one]
    have hcmem : s (φ g) * m * (s (φ g))⁻¹ ∈ V ⊓ F.ker :=
      (hV.inf (isOpenNormal_ker_of_isSmoothHom hFsm)).normal.conj_mem m hm (s (φ g))
    have hcker : s (φ g) * m * (s (φ g))⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, ← hFright, MonoidHom.mem_ker.1 hcmem.2, _root_.map_one]
    have hsplit : (⟨g * m * (s (φ (g * m)))⁻¹, hr (g * m)⟩ : ↥(φ.ker))
        = ⟨g * (s (φ g))⁻¹, hr g⟩ * ⟨s (φ g) * m * (s (φ g))⁻¹, hcker⟩ := by
      apply Subtype.ext
      show g * m * (s (φ (g * m)))⁻¹ = g * (s (φ g))⁻¹ * (s (φ g) * m * (s (φ g))⁻¹)
      rw [_root_.map_mul, hmφ, mul_one]
      group
    show layerSubMap ℓ α j (u ⟨g * m * (s (φ (g * m)))⁻¹, hr (g * m)⟩)
      = layerSubMap ℓ α j (u ⟨g * (s (φ g))⁻¹, hr g⟩)
    rw [hsplit, _root_.map_mul u,
      hVu ⟨s (φ g) * m * (s (φ g))⁻¹, hcker⟩ (Subgroup.mem_inf.1 hcmem).1, mul_one]
  · intro ν x hx hx1
    have hxk : x ∈ φ.ker := MonoidHom.mem_ker.2 hx1
    show layerSubMap ℓ α j (u ⟨x * (s (φ x))⁻¹, hr x⟩) = 1
    rw [hkerv x hxk, huD ν ⟨x, hxk⟩ hx, _root_.map_one]
  · intro μ x
    have hxk : (x : Gal(Ω/k)) ∈ φ.ker := hAker μ x.2
    show layerSubMap ℓ α j (u ⟨(x : Gal(Ω/k)) * (s (φ (x : Gal(Ω/k))))⁻¹, hr (x : Gal(Ω/k))⟩)
      = layerSubMap ℓ (α.comp β) j (a μ x)
    rw [hkerv (x : Gal(Ω/k)) hxk, hua μ x hxk, layerSubMap_comp]
    rfl
  · rintro P hPp hPbot ⟨x, hxI, hxφ, hxc⟩
    have hxk : x ∈ φ.ker := MonoidHom.mem_ker.2 hxφ
    have hu1 : u ⟨x, hxk⟩ ≠ 1 := by
      intro h1
      refine hxc ?_
      show layerSubMap ℓ α j (u ⟨x * (s (φ x))⁻¹, hr x⟩) = 1
      rw [hkerv x hxk, h1, _root_.map_one]
    have hex : ∃ y : ↥(φ.ker), (y : Gal(Ω/k)) ∈ Ideal.inertia Gal(Ω/k) P ∧ u y ≠ 1 :=
      ⟨⟨x, hxk⟩, hxI, hu1⟩
    refine (huram P hPp hPbot hex).imp id fun hcase y hy => ?_
    rw [← layerSemidirectMap_comp ℓ hβ hα (hα.comp hβ) (j + 1) (F y), hcase y hy]
    exact _root_.map_one _

end Descent

end InverseGalois.Shafarevich
