/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.CorestrictionInertia
import InverseGalois.CFT.Profinite.Trivial
import InverseGalois.Solvable.Shafarevich.LevelConfinedTwist

/-!
# The sharp prescription, bought over the field the base realization cuts out

The base realization acts trivially on the layer through its own kernel, so over the field that
kernel cuts out a cocycle is nothing but a homomorphism into the layer — the whole prescription
problem becomes one about homomorphisms of a profinite group into a finite abelian group.  A
homomorphism prescribed there is carried back down to the base field by averaging it over the
cosets of the kernel, and the average is a cocycle over the base field for free.

Averaging is faithful at the data the prescription names, provided the primes it names are
completely decomposed in that field: the representatives of the nontrivial cosets lie outside the
kernel and therefore move such a prime, so a homomorphism asked to kill the decomposition subgroups
of the primes the elements outside the kernel carry it to contributes a single term to the product,
and with the trivial coset represented by the identity that term is the value of the homomorphism
itself.  So the average reproduces the homomorphism on the whole decomposition subgroup, and both
the values prescribed along it and the cyclicity of those values survive the descent verbatim.

Only the conjugates by elements outside the kernel are asked about, and that restriction is what
makes the demand consistent with prescribing values along the decomposition subgroup at all: an
element of the kernel carries the decomposition subgroup to a conjugate of itself inside the kernel,
where a homomorphism into an abelian group repeats its values.

Ramification of the average is ramification of the homomorphism somewhere in the orbit, which is
what confines the new ramification of the average to where the homomorphism was already ramified;
and the finite family, being asked of the homomorphism at every conjugate, is killed by the
average outright.

The prescription may spend a shrinking of its own: it announces the number of letters its data is
read at and answers at the number asked for, the prescribed values being carried across by the map
of layers.  Averaging is over the cosets of the kernel and leaves that shrinking untouched.

## Main definitions

* `InverseGalois.Shafarevich.HasKernelPrescription` — **a smooth homomorphism into the layer,
  defined on the kernel of the base realization, can be prescribed along finitely many subgroups of
  decomposition subgroups at once, be trivial along the conjugates of the finite family, and ramify
  only at the named primes or at primes it is cyclic at and the given lift kills the whole
  decomposition subgroup of.**

## Main results

* `InverseGalois.Shafarevich.hasConfinedPrescription_of_hasKernelPrescription` — **averaging a
  prescribed homomorphism over the cosets of the kernel of the base realization carries the
  prescription down to the base field.**

## Tags

Shafarevich's theorem, embedding problem, corestriction, one cocycle, decomposition group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT GroupExtension MulAction NumberField groupCohomology

open scoped Pointwise

attribute [local instance] genericQuotAction

/-! ### The prescription over the larger field -/

section Kernel

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S]
  [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] (φ : Gal(Ω/k) →* U)
  [MulDistribMulAction Gal(Ω/k) ↥(layerSub ℓ (Generic U n S) j)] {t : ℕ}
  (D : Fin t → Subgroup Gal(Ω/k))

/-- **A smooth homomorphism into the layer, defined on the kernel of the base realization, can be
prescribed along finitely many subgroups of decomposition subgroups at once, be trivial along the
conjugates of the finite family, and ramify only at the named primes or at primes it is cyclic at
and the given lift kills the whole decomposition subgroup of.**

This is the prescription of the repair, made one field up: the base realization acts trivially on
the layer through its kernel, so a cocycle of the kernel is a homomorphism, and the whole demand is
one about homomorphisms into a finite abelian group.  The named primes are asked to be completely
decomposed in the field the kernel cuts out, and the homomorphism is asked to kill the
decomposition subgroups of the primes the elements the base realization moves carry them to, so that
averaging it back down to the base field reproduces it at the prescribed data; distinct named primes
lie in distinct orbits, so those demands do not collide.  Each subgroup carrying a prescription is
the whole decomposition subgroup of its prime, the one shape the repair produces.  The same is asked
at each prime the
homomorphism itself brings in, where it is asked in addition to be cyclic on the decomposition
subgroup and the given lift to kill that subgroup outright.  The lift the killing is read of is the
given one carried down along the shrinking the prescription spends, so the field the named primes
are asked to split completely in sits at the number of letters asked for however many letters the
data is read at.

The prescribed homomorphisms are asked to have cyclic image, which is what the reciprocity law
leaves room for.  The classes in the completions which name the coordinates of a prescription are
otherwise unrelated to one another, and a family of units carrying an unrelated family of classes at
a family of places is more than the reciprocity law permits: the power residue symbol of two
coordinates over all the places is trivial, and away from the named places the symbol contributes
nothing.  The relation is empty as soon as the coordinates lie on a single line, the symbol being
alternating.

No named prime is allowed to sit over the finite family: its decomposition subgroup is asked to
escape every conjugate of every subgroup of the family.  Without that the two demands would collide,
the homomorphism being asked to vanish along the family and to take a prescribed value along the
decomposition subgroup of the named prime.  It costs nothing, because a prime the given lift
ramifies at over the base realization escapes the family of itself: the lift is trivial along it, so
it is trivial along the decomposition subgroup of any prime sitting over it, and then it does not
ramify there.

The vanishing along the finite family is asked at every conjugate, which is what makes the average
vanish along the family itself.  The given lift is asked to be onto, which is what the repair the
ladder consumes supplies and what makes the field it cuts out the whole of the generic quotient one
field up.

As for the prescription below, the base realization is asked to be
smooth, its kernel open, that field being a finite extension, and the prescription may spend a
shrinking of its own: it announces the number of letters the data is read at, and answers with a
surjection onto the number asked for and a homomorphism at that number, the prescribed values being
carried across by the map of layers. -/
def HasKernelPrescription : Prop :=
  ∃ N : ℕ,
    IsOpen (φ.ker : Set Gal(Ω/k)) →
    ∀ (F : Gal(Ω/k) →* GenericQuot ℓ U N S (j + 1)) (ι : Type) [Finite ι]
        (Q : ι → Ideal (𝓞 Ω)) (A : ι → Subgroup Gal(Ω/k))
        (a : (μ : ι) → ↥(A μ) →* ↥(layerSub ℓ (Generic U N S) j)),
      Function.Surjective F → IsSmoothHom F → (∀ μ, (Q μ).IsPrime) → (∀ μ, Q μ ≠ ⊥) →
      (∀ (μ ν : ι) (ρ : Gal(Ω/k)), ρ • Q μ = Q ν → μ = ν) →
      (∀ μ, stabilizer Gal(Ω/k) (Q μ) ≤ φ.ker) →
      (∀ μ, A μ ≤ stabilizer Gal(Ω/k) (Q μ)) → (∀ μ, A μ ≤ φ.ker) →
      (∀ μ, A μ = stabilizer Gal(Ω/k) (Q μ)) →
      (∀ μ, IsSmooth₁ ((a μ : ↥(A μ) →* ↥(layerSub ℓ (Generic U N S) j)) :
        ↥(A μ) → ↥(layerSub ℓ (Generic U N S) j))) →
      (∀ μ, ∃ x₀ : ↥(A μ), ∀ x : ↥(A μ), a μ x ∈ Subgroup.zpowers (a μ x₀)) →
      (∀ (μ : ι) (ν : Fin t) (ρ : Gal(Ω/k)),
        ∃ y ∈ stabilizer Gal(Ω/k) (Q μ), ρ * y * ρ⁻¹ ∉ D ν) →
        ∃ (α : Generic U N S →* Generic U n S) (hα : IsOperatorHom α), Function.Surjective α ∧
          ∃ u : ↥(φ.ker) →* ↥(layerSub ℓ (Generic U n S) j),
            IsSmooth₁ ((u : ↥(φ.ker) →* ↥(layerSub ℓ (Generic U n S) j)) :
              ↥(φ.ker) → ↥(layerSub ℓ (Generic U n S) j)) ∧
            (∀ (ν : Fin t) (ρ : Gal(Ω/k)) (y : ↥(φ.ker)),
              ρ * (y : Gal(Ω/k)) * ρ⁻¹ ∈ D ν → u y = 1) ∧
            (∀ (μ : ι) (x : ↥(A μ)) (hx : (x : Gal(Ω/k)) ∈ φ.ker),
              u ⟨(x : Gal(Ω/k)), hx⟩ = layerSubMap ℓ α j (a μ x)) ∧
            (∀ (μ : ι) (ρ : Gal(Ω/k)), ρ ∉ φ.ker →
              ∀ y : ↥(φ.ker), (y : Gal(Ω/k)) ∈ stabilizer Gal(Ω/k) (ρ • Q μ) → u y = 1) ∧
            ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
              (∃ y : ↥(φ.ker), (y : Gal(Ω/k)) ∈ Ideal.inertia Gal(Ω/k) P ∧ u y ≠ 1) →
              (∃ (μ : ι) (ρ : Gal(Ω/k)), P = ρ • Q μ) ∨
                ((∀ x ∈ stabilizer Gal(Ω/k) P, layerSemidirectMap ℓ hα (j + 1) (F x) = 1) ∧
                  stabilizer Gal(Ω/k) P ≤ φ.ker ∧
                  (∀ ρ : Gal(Ω/k), ρ ∉ φ.ker →
                    ∀ y : ↥(φ.ker), (y : Gal(Ω/k)) ∈ stabilizer Gal(Ω/k) (ρ • P) → u y = 1) ∧
                  ∃ y₀ : ↥(φ.ker), (y₀ : Gal(Ω/k)) ∈ stabilizer Gal(Ω/k) P ∧
                    ∀ y : ↥(φ.ker), (y : Gal(Ω/k)) ∈ stabilizer Gal(Ω/k) P →
                      u y ∈ Subgroup.zpowers (u y₀))

variable {ℓ U n S j φ D}

omit [Fact ℓ.Prime] [Finite S] [NumberField k] [IsAlgClosed Ω] in
/-- **Averaging a prescribed homomorphism over the cosets of the kernel of the base realization
carries the prescription down to the base field.**

Over the field the kernel cuts out the action on the layer is trivial, so a homomorphism there is a
cocycle, and its average over the cosets is a cocycle over the base field; smoothness descends
because an open normal subgroup of the kernel contains one of the base group, the kernel being
open.

At a named prime the average reproduces the homomorphism on the whole decomposition subgroup: the
prime is completely decomposed in that field, so the representatives of the nontrivial cosets move
it, and the homomorphism was asked to kill the decomposition subgroups of the primes they move it
to.  The prescribed values therefore descend verbatim.

Where the average ramifies the homomorphism ramifies at the prime one of the representatives carries
the given one to, which is what keeps the confinement clause; and everything asked of the
homomorphism there descends along that same representative.  The given lift kills the decomposition
subgroup of the prime it is asked at, hence kills the conjugate subgroup as well; and the prime
being completely decomposed in that field the other representatives move it, so the average again
collapses to the one term, and its values on the decomposition subgroup of the given prime are the
values of the homomorphism carried across — powers of a single one of them exactly when those
were.

The number of letters the data is read at, and the shrinking the prescription spends, are passed
along unchanged: averaging is over the cosets of the kernel and does not touch the layer. -/
theorem hasConfinedPrescription_of_hasKernelPrescription
    (hactφ : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)), x • v = φ x • v)
    (hpres : HasKernelPrescription ℓ U n S j φ D) :
    HasConfinedPrescription ℓ U n S j φ D := by
  classical
  obtain ⟨N, hpres⟩ := hpres
  refine ⟨N, ?_⟩
  intro hφopen F ι _ Q A a hFsurj hFsm hQp hQbot hQorb hQker hAstab hAker hAcase hasm hacyc havoid
  obtain ⟨α, hα, hαsurj, u, husm, huD, hua, huorb, huram⟩ :=
    hpres hφopen F ι Q A a hFsurj hFsm hQp hQbot hQorb hQker hAstab hAker hAcase hasm hacyc
      havoid
  haveI : Finite (Gal(Ω/k) ⧸ φ.ker) :=
    Finite.of_injective _ (QuotientGroup.kerLift_injective φ)
  haveI : Fintype (Gal(Ω/k) ⧸ φ.ker) := Fintype.ofFinite _
  obtain ⟨σ, hσ, hσ1⟩ := exists_section_one (φ.ker)
  have htriv : ∀ (y : ↥(φ.ker)) (m : ↥(layerSub ℓ (Generic U n S) j)), y • m = m := by
    intro y m
    show (y : Gal(Ω/k)) • m = m
    rw [hactφ, MonoidHom.mem_ker.1 y.2, one_smul]
  have hcore : HasOpenNormalCore φ.ker := hasOpenNormalCore_of_isOpen φ.ker hφopen
  refine ⟨α, hα, hαsurj, corCochain₁ φ.ker σ hσ (u : ↥(φ.ker) → ↥(layerSub ℓ (Generic U n S) j)),
    isMulCocycle₁_corCochain₁ φ.ker σ hσ (isMulCocycle₁_of_hom htriv u),
    isSmooth₁_corCochain₁_of_isSmooth₁ φ.ker σ hσ hcore husm, ?_, ?_, ?_⟩
  · intro ν x hx hφx
    refine corCochain₁_eq_one_of_conj φ.ker σ hσ (MonoidHom.mem_ker.2 hφx) fun z y hy => ?_
    refine huD ν (σ z) y ?_
    rw [hy, show σ z * ((σ z)⁻¹ * x * σ z) * (σ z)⁻¹ = x from by group]
    exact hx
  · intro μ x
    have hmem : (x : Gal(Ω/k)) ∈ stabilizer Gal(Ω/k) (Q μ) := hAstab μ x.2
    rw [corCochain₁_eq_self_of_stabilizer_le φ.ker σ hσ hσ1 (hQker μ) (huorb μ) hmem]
    exact hua μ x (hQker μ hmem)
  · rintro P hPp hPbot ⟨g, hgI, hgφ, hgc⟩
    haveI := hPp
    obtain ⟨x, y, hyI, hy1⟩ := exists_mem_inertia_section_of_corCochain₁_ne_one φ.ker σ hσ
      (MonoidHom.mem_ker.2 hgφ) hgI hgc
    have hPne : (σ x)⁻¹ • P ≠ ⊥ := by
      intro hbot
      exact hPbot (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => σ x • I) hbot)
    rcases huram ((σ x)⁻¹ • P) inferInstance hPne ⟨y, hyI, hy1⟩ with ⟨μ, ρ, hρ⟩ | h
    · exact Or.inl ⟨μ, σ x * ρ, by rw [mul_smul, ← hρ, smul_inv_smul]⟩
    · obtain ⟨hF1, hker, hvan, y₀, hy₀, hgen⟩ := h
      refine Or.inr ⟨fun z hz => ?_,
        exists_forall_mem_zpowers_corCochain₁ φ.ker σ hσ x hker hvan y₀ hy₀ hgen⟩
      have hmem : (σ x)⁻¹ * z * σ x ∈ stabilizer Gal(Ω/k) ((σ x)⁻¹ • P) := by
        refine mem_stabilizer_smul_iff.2 ?_
        rw [show (σ x)⁻¹⁻¹ * ((σ x)⁻¹ * z * σ x) * (σ x)⁻¹ = z from by group]
        exact hz
      have hG1 : ∀ w ∈ stabilizer Gal(Ω/k) ((σ x)⁻¹ • P),
          ((layerSemidirectMap ℓ hα (j + 1)).comp F) w = 1 := fun w hw => hF1 w hw
      show ((layerSemidirectMap ℓ hα (j + 1)).comp F) z = 1
      rw [show z = σ x * ((σ x)⁻¹ * z * σ x) * (σ x)⁻¹ from by group, _root_.map_mul,
        _root_.map_mul, _root_.map_inv, hG1 _ hmem, mul_one, mul_inv_cancel]

end Kernel

end InverseGalois.Shafarevich
