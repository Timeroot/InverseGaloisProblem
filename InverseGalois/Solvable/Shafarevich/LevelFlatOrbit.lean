/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.ConjugationTrace
import InverseGalois.Solvable.Shafarevich.LevelFlatKernel

/-!
# The flat prescription, bought one named prime at a time

The flat prescription over the field the base realization cuts out asks for a homomorphism which is
equivariant for conjugation by the whole base group.  That is a global demand, and the arithmetic
which supplies homomorphisms — a radicand and a root of unity, read as a character of the kernel —
supplies them only with the equivariance the radicand happens to have.  A radicand living in the
field a decomposition subgroup cuts out is equivariant for that decomposition subgroup and for
nothing more.

The gap is closed by a trace.  A homomorphism equivariant for the decomposition subgroup of a named
prime is traced over the cosets of that subgroup, saturated along the base realization, and the
trace is equivariant for the whole group.  The saturation costs nothing: a homomorphism of the
kernel into an abelian group does not see conjugation by the kernel, so equivariance for the
decomposition subgroup is already equivariance for its saturation, and the saturation contains the
kernel, so its cosets are a finite family.

Tracing over the cosets and not over the whole group is what keeps the prescribed values.  A trace
over the whole group would repeat, at an element the decomposition subgroup fixes, one and the same
value as many times as the decomposition subgroup has elements, and a value of an elementary abelian
layer raised to that power is generally trivial; the trace over the cosets contributes it once.
What has to be added is that the homomorphism kills the decomposition subgroups of the primes the
representatives of the other cosets carry the named prime to — which is a demand about a prime the
arithmetic is free to choose, not about the group.

Several primes are named at once, and their decomposition subgroups are different, so one trace
cannot serve them all.  Each named prime is traced separately and the traces are multiplied.  For
the prescribed values to survive the product, each factor is asked to kill the conjugates of the
subgroups belonging to the *other* named primes, so that at a named prime the product collapses to
its own factor.

## Main definitions

* `InverseGalois.Shafarevich.HasFlatOrbitPrescription` — **for each named prime separately, a smooth
  homomorphism of the kernel into the layer, equivariant only for the decomposition subgroup of that
  prime, prescribed along the subgroup belonging to it, trivial along the finite family and along
  the subgroups belonging to the other named primes, trivial on the decomposition subgroups of the
  conjugates of its prime outside the saturation, and ramified only at the named primes or where the
  given lift carried down kills the whole decomposition subgroup.**

## Main results

* `InverseGalois.Shafarevich.hasFlatKernelPrescription_of_hasFlatOrbitPrescription` — **tracing each
  named prime's homomorphism over the cosets of the saturated decomposition subgroup and multiplying
  the traces buys the flat prescription over the larger field.**

## Tags

Shafarevich's theorem, embedding problem, transfer, decomposition group, ramification
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT GroupExtension MulAction NumberField groupCohomology

open scoped Pointwise

attribute [local instance] genericQuotAction

set_option maxHeartbeats 1600000

/-! ### The prescription, read one named prime at a time -/

section Orbit

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S]
  [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] (φ : Gal(Ω/k) →* U) {t : ℕ} (D : Fin t → Subgroup Gal(Ω/k))

/-- **For each named prime separately, a smooth homomorphism of the kernel into the layer,
equivariant only for the decomposition subgroup of that prime, prescribed along the subgroup
belonging to it, trivial along the finite family and along the subgroups belonging to the other
named primes, trivial on the decomposition subgroups of the conjugates of its prime outside the
saturation, and ramified only at the named primes or where the given lift carried down kills the
whole decomposition subgroup.**

Everything the flat prescription over the larger field asks of one homomorphism is asked here of a
family of homomorphisms, one for each named prime, and every clause is weakened in the same
direction: what was demanded of the whole group is demanded only of the decomposition subgroup of
the prime the homomorphism belongs to.

The subgroups the values are prescribed along are the parts of inertia at the named primes which the
base realization kills, and the named primes are away from the exponent, so each prescribed
homomorphism is a power of a single one of its own values.  Inertia at a named prime is killed by
the base realization outright, so the prime is unramified in the field that realization cuts out and
the whole of inertia there is already seen over the base field.  The named primes escape the finite
family: no conjugate of the decomposition subgroup of one of them lies inside a member of it.

Equivariance is the clause that matters.  A homomorphism supplied by a radicand is equivariant for
the group fixing the radicand, and a radicand can be placed in the field the decomposition subgroup
of a chosen prime cuts out.  Equivariance for the whole group would ask the radicand to be rational,
and then the prescription could not be made at a single prime.

The clause about the conjugates is read only outside the saturation of the decomposition subgroup
along the base realization, which is where the trace has a coset to spend: an element whose image is
already the image of something fixing the prime carries the prime to a conjugate the trace does not
separate, and nothing is asked there.

The clause about the other named primes is what lets the several traces be multiplied without
disturbing one another's prescribed values.

One shrinking of the operator group is spent for the whole family at once, the prescribed values
being carried across by the map of layers, exactly as over the base field. -/
def HasFlatOrbitPrescription : Prop :=
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
      (∀ (μ : ι) (ν : Fin t) (ρ : Gal(Ω/k)),
        ∃ y ∈ stabilizer Gal(Ω/k) (Q μ), ρ * y * ρ⁻¹ ∉ D ν) →
        ∃ (β : Generic U N S →* Generic U n S) (hβ : IsOperatorHom β), Function.Surjective β ∧
          ∃ u : ι → (↥(φ.ker) →* ↥(layerSub ℓ (Generic U n S) j)),
            (∃ V : Subgroup Gal(Ω/k), IsOpenNormal V ∧
              ∀ (μ : ι) (y : ↥(φ.ker)), (y : Gal(Ω/k)) ∈ V → u μ y = 1) ∧
            (∀ (μ : ι) (g : Gal(Ω/k)), g ∈ stabilizer Gal(Ω/k) (Q μ) →
              ∀ (y : ↥(φ.ker)) (hy : g * (y : Gal(Ω/k)) * g⁻¹ ∈ φ.ker),
                u μ ⟨g * (y : Gal(Ω/k)) * g⁻¹, hy⟩ = φ g • u μ y) ∧
            (∀ (μ : ι) (ν : Fin t) (ρ : Gal(Ω/k)) (y : ↥(φ.ker)),
              ρ * (y : Gal(Ω/k)) * ρ⁻¹ ∈ D ν → u μ y = 1) ∧
            (∀ (μ ν : ι), ν ≠ μ → ∀ (ρ : Gal(Ω/k)) (y : ↥(φ.ker)),
              ρ * (y : Gal(Ω/k)) * ρ⁻¹ ∈ A ν → u μ y = 1) ∧
            (∀ (μ : ι) (x : ↥(A μ)) (hx : (x : Gal(Ω/k)) ∈ φ.ker),
              u μ ⟨(x : Gal(Ω/k)), hx⟩ = layerSubMap ℓ β j (a μ x)) ∧
            (∀ (μ : ι) (ρ : Gal(Ω/k)), (∀ s ∈ stabilizer Gal(Ω/k) (Q μ), φ s ≠ φ ρ) →
              ∀ y : ↥(φ.ker), (y : Gal(Ω/k)) ∈ stabilizer Gal(Ω/k) (ρ • Q μ) → u μ y = 1) ∧
            ∀ (μ : ι) (P : Ideal (𝓞 Ω)), P.IsPrime → P ≠ ⊥ →
              (∃ y : ↥(φ.ker), (y : Gal(Ω/k)) ∈ Ideal.inertia Gal(Ω/k) P ∧ u μ y ≠ 1) →
              (∃ (ν : ι) (ρ : Gal(Ω/k)), P = ρ • Q ν) ∨
                ∀ x ∈ stabilizer Gal(Ω/k) P, layerSemidirectMap ℓ hβ (j + 1) (F x) = 1

end Orbit

/-! ### Tracing the family over the cosets -/

section Trace

variable {ℓ : ℕ} [Fact ℓ.Prime] {U : Type} [Group U] [Finite U] {n : ℕ} {S : Type} [Group S]
  [Finite S] {j : ℕ} {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] {φ : Gal(Ω/k) →* U} {t : ℕ} {D : Fin t → Subgroup Gal(Ω/k)}

omit [Fact ℓ.Prime] [Finite S] [NumberField k] [IsGalois k Ω] [IsAlgClosed Ω] in
/-- **Tracing each named prime's homomorphism over the cosets of the saturated decomposition
subgroup and multiplying the traces buys the flat prescription over the larger field.**

The trace of a homomorphism equivariant for a subgroup is equivariant for the whole group, and
equivariance for the decomposition subgroup of a prime is already equivariance for its saturation
along the base realization, a homomorphism of the kernel into an abelian group not seeing
conjugation by the kernel.  The saturation contains the kernel, so it has finitely many cosets and
the trace is a finite product.

Vanishing transfers because it was asked at every conjugate: a homomorphism killing every conjugate
of a subgroup traces to one killing that subgroup.  That is what carries the vanishing along the
finite family through, and, applied to the subgroups belonging to the other named primes, it is what
makes the product of the traces collapse at a named prime to the trace belonging to that prime.

At its own named prime the trace reproduces the homomorphism: the representatives of the other
cosets lie outside the saturation, hence carry the prime somewhere the homomorphism was asked to
kill the decomposition subgroup of, and the coset of the identity is represented by the identity.

Where the product ramifies one of the traces ramifies, and where a trace ramifies its homomorphism
ramifies at a prime one representative carries the given one to; the alternative there is that the
given lift carried down kills the whole decomposition subgroup of that conjugate, and conjugating
back kills the decomposition subgroup of the prime itself. -/
theorem hasFlatKernelPrescription_of_hasFlatOrbitPrescription
    (hpres : HasFlatOrbitPrescription ℓ U n S j φ D) :
    HasFlatKernelPrescription ℓ U n S j φ D := by
  classical
  obtain ⟨N, hN⟩ := hpres
  refine ⟨N, ?_⟩
  intro F ι _ Q A a hFsurj hFsm hFright hQp hQbot hQℓ hAstab hAker hAeq hAunr hasm haequiv hesc
  obtain ⟨β, hβ, hβsurj, u, ⟨V, hV, hVu⟩, hueq, huD, huA, hua, huvan, huram⟩ :=
    hN F ι Q A a hFsurj hFsm hFright hQp hQbot hQℓ hAstab hAker hAeq hAunr hasm haequiv hesc
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Finite (Gal(Ω/k) ⧸ φ.ker) := Finite.of_injective _ (QuotientGroup.kerLift_injective φ)
  haveI : (φ.ker).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI hfin : ∀ μ : ι, Fintype (Gal(Ω/k) ⧸ saturate φ (stabilizer Gal(Ω/k) (Q μ))) := fun μ => by
    haveI : (saturate φ (stabilizer Gal(Ω/k) (Q μ))).FiniteIndex :=
      Subgroup.finiteIndex_of_le (ker_le_saturate φ _)
    exact Fintype.ofFinite _
  choose σ hσ hσ1 using fun μ : ι =>
    exists_section_coe_one (saturate φ (stabilizer Gal(Ω/k) (Q μ)))
  have hueqsat : ∀ (μ : ι), ∀ h ∈ saturate φ (stabilizer Gal(Ω/k) (Q μ)), ∀ y : ↥(φ.ker),
      u μ (conjHom φ.ker h y) = φ h • u μ y := by
    intro μ h hh y
    refine apply_conjHom_of_mem_saturate φ _ le_rfl (fun s hs z => ?_) hh y
    have hmem : s * (z : Gal(Ω/k)) * s⁻¹ ∈ φ.ker := (conjHom φ.ker s z).2
    have hc : conjHom φ.ker s z = ⟨s * (z : Gal(Ω/k)) * s⁻¹, hmem⟩ := Subtype.ext rfl
    rw [hc, hueq μ s hs z hmem]
  refine ⟨β, hβ, hβsurj,
    ∏ μ : ι, conjTraceHom φ.ker (saturate φ (stabilizer Gal(Ω/k) (Q μ))) (σ μ) φ (u μ),
    ⟨V, hV, fun y hy => ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.finset_prod_apply]
    exact Finset.prod_eq_one fun μ _ =>
      conjTraceHom_eq_one_of_mem_normal φ.ker _ (σ μ) φ hV.normal (hVu μ) hy
  · intro g y hy
    have hy' : (⟨g * (y : Gal(Ω/k)) * g⁻¹, hy⟩ : ↥(φ.ker)) = conjHom φ.ker g y := Subtype.ext rfl
    rw [hy', MonoidHom.finset_prod_apply, MonoidHom.finset_prod_apply, Finset.smul_prod']
    exact Finset.prod_congr rfl fun μ _ =>
      conjTraceHom_conj φ.ker _ (σ μ) φ (hσ μ) (hueqsat μ) g y
  · intro ν y hyD
    rw [MonoidHom.finset_prod_apply]
    exact Finset.prod_eq_one fun μ _ =>
      conjTraceHom_eq_one_of_forall_conj φ.ker _ (σ μ) φ (fun ρ z hz => huD μ ν ρ z hz) hyD
  · intro μ x hx
    rw [MonoidHom.finset_prod_apply]
    have hcoll : ∏ ν : ι, conjTraceHom φ.ker (saturate φ (stabilizer Gal(Ω/k) (Q ν))) (σ ν) φ
          (u ν) ⟨(x : Gal(Ω/k)), hx⟩
        = conjTraceHom φ.ker (saturate φ (stabilizer Gal(Ω/k) (Q μ))) (σ μ) φ (u μ)
            ⟨(x : Gal(Ω/k)), hx⟩ :=
      Finset.prod_eq_single _
        (fun ν _ hν => conjTraceHom_eq_one_of_forall_conj φ.ker _ (σ ν) φ
          (fun ρ z hz => huA ν μ (Ne.symm hν) ρ z hz) x.2)
        fun h => absurd (Finset.mem_univ _) h
    rw [hcoll, conjTraceHom_eq_self_of_stabilizer_le φ.ker _ (σ μ) φ (hσ μ) (hσ1 μ)
      (fun ρ hρ z hz => huvan μ ρ (fun s hs hc => hρ ((mem_saturate_iff φ _).2 ⟨s, hs, hc⟩)) z hz)
      (hAstab μ x.2)]
    exact hua μ x hx
  · rintro P hPp hPbot ⟨y, hyI, hy1⟩
    haveI := hPp
    have hex : ∃ μ : ι,
        conjTraceHom φ.ker (saturate φ (stabilizer Gal(Ω/k) (Q μ))) (σ μ) φ (u μ) y ≠ 1 := by
      by_contra hc
      push_neg at hc
      refine hy1 ?_
      rw [MonoidHom.finset_prod_apply]
      exact Finset.prod_eq_one fun μ _ => hc μ
    obtain ⟨μ, hμ⟩ := hex
    obtain ⟨c, hcI, hcne⟩ := exists_mem_inertia_section_of_conjTraceHom_ne_one φ.ker
      (saturate φ (stabilizer Gal(Ω/k) (Q μ))) (σ μ) φ hyI hμ
    have hPne : (σ μ c)⁻¹ • P ≠ ⊥ := by
      intro hbot
      exact hPbot (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => σ μ c • I) hbot)
    rcases huram μ ((σ μ c)⁻¹ • P) inferInstance hPne ⟨_, hcI, hcne⟩ with ⟨ν, ρ, hρ⟩ | h
    · exact Or.inl ⟨ν, σ μ c * ρ, by rw [mul_smul, ← hρ, smul_inv_smul]⟩
    · refine Or.inr fun z hz => ?_
      have hmem : (σ μ c)⁻¹ * z * σ μ c ∈ stabilizer Gal(Ω/k) ((σ μ c)⁻¹ • P) := by
        refine mem_stabilizer_smul_iff.2 ?_
        rw [show (σ μ c)⁻¹⁻¹ * ((σ μ c)⁻¹ * z * σ μ c) * (σ μ c)⁻¹ = z from by group]
        exact hz
      have hG1 : ∀ w ∈ stabilizer Gal(Ω/k) ((σ μ c)⁻¹ • P),
          ((layerSemidirectMap ℓ hβ (j + 1)).comp F) w = 1 := fun w hw => h w hw
      show ((layerSemidirectMap ℓ hβ (j + 1)).comp F) z = 1
      rw [show z = σ μ c * ((σ μ c)⁻¹ * z * σ μ c) * (σ μ c)⁻¹ from by group, _root_.map_mul,
        _root_.map_mul, _root_.map_inv, hG1 _ hmem, mul_one, mul_inv_cancel]

end Trace

end InverseGalois.Shafarevich
