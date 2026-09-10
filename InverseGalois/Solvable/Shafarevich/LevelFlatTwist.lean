/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.LiftTwist
import InverseGalois.CFT.Units.RamifiedFamily
import InverseGalois.Solvable.Shafarevich.LevelCyclicRepair

/-!
# Flattening a lift: confining its new ramification to where the solution below already ramifies

A lift of a solution across one layer may ramify over the base realization at primes where the
solution below does not, and at such a prime the lift lands in the layer along the part of inertia
the base realization kills.  Those primes meet only finitely many orbits and one prime of each can
be named; at a named one where the solution below is unramified over the base realization, the
restriction of the lift to that part of inertia is a homomorphism into the layer, and a cocycle
prescribed to be its inverse there corrects the lift to one which is unramified there outright.

Away from the named primes the cocycle is asked only to be unramified, save at primes it introduces
itself, where the given lift is asked to kill the whole decomposition subgroup.  That is the weaker
of the two prescriptions the repair uses: nothing is demanded of the local image, only of where the
ramification sits.  It is the prescription which can be made over the base field directly, without
passing to the field the base realization cuts out, and so it is the one which does not ask the
primes it names to split completely.

The result is a lift whose new ramification over the base realization is confined: at every prime
where it ramifies, either the solution below already ramifies, or the solution below kills the whole
decomposition subgroup — and in the second case the prime is completely decomposed in the field the
solution below cuts out.  That is exactly the hypothesis under which the second, sharper
prescription may be bought over the larger field and carried down.

## Main definitions

* `InverseGalois.Shafarevich.HasFlatPrescription` — **a smooth one cocycle with values in the layer
  can be prescribed along finitely many subgroups of decomposition subgroups at once, be trivial
  along the finite family, and ramify only at the named primes or where the given lift kills the
  whole decomposition subgroup**, at the price of a shrinking of the operator group.

## Main results

* `InverseGalois.Shafarevich.exists_confinedRamifiedHom_lift_of_hasFlatPrescription` — **an
  arbitrary lift of the solution below can be corrected to one whose new ramification over the base
  realization is confined**, in exchange for one such prescription.

## Tags

Shafarevich's theorem, embedding problem, one cocycle, ramification, decomposition group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT GroupExtension MulAction NumberField groupCohomology

open scoped Pointwise

attribute [local instance] genericQuotAction

/-! ### The prescription the flattening is bought with -/

section Flat

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S]
  [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] (φ : Gal(Ω/k) →* U)
  [MulDistribMulAction Gal(Ω/k) ↥(layerSub ℓ (Generic U n S) j)] {t : ℕ}
  (D : Fin t → Subgroup Gal(Ω/k))

/-- **A smooth one cocycle with values in the layer can be prescribed along finitely many subgroups
of decomposition subgroups at once, be trivial along the finite family, and ramify only at the named
primes or where the given lift kills the whole decomposition subgroup.**

The subgroups the cocycle is prescribed along are asked to sit inside the decomposition subgroups of
finitely many named primes and inside the kernel of the base realization, which is what makes the
prescription well posed: on such a subgroup the action on the layer is trivial, so a cocycle
restricts there to a homomorphism.  Along the finite family the cocycle is asked to vanish wherever
the base realization already does.

The last clause is the one which confines the new ramification, and it asks less than the
prescription the cyclic repair is bought with: at a prime where the cocycle ramifies along the part
of inertia the base realization kills, either that prime is one of the named ones, or it is a prime
the cocycle brings in by itself, and there only the vanishing of the given lift on the whole
decomposition subgroup is demanded, nothing about the local image of the cocycle.

The prescription may spend a shrinking of its own: it announces the number of letters the data is
read at, and answers with a surjection onto the number asked for and a cocycle at that number, the
prescribed values being carried across by the map of layers. -/
def HasFlatPrescription : Prop :=
  ∃ N : ℕ,
    ∀ (F : Gal(Ω/k) →* GenericQuot ℓ U N S (j + 1)) (ι : Type) [Finite ι]
        (Q : ι → Ideal (𝓞 Ω)) (A : ι → Subgroup Gal(Ω/k))
        (a : (μ : ι) → ↥(A μ) →* ↥(layerSub ℓ (Generic U N S) j)),
      IsSmoothHom F → (∀ μ, (Q μ).IsPrime) → (∀ μ, Q μ ≠ ⊥) →
      (∀ μ, A μ ≤ stabilizer Gal(Ω/k) (Q μ)) → (∀ μ, A μ ≤ φ.ker) →
      (∀ μ, IsSmooth₁ ((a μ : ↥(A μ) →* ↥(layerSub ℓ (Generic U N S) j)) :
        ↥(A μ) → ↥(layerSub ℓ (Generic U N S) j))) →
        ∃ (α : Generic U N S →* Generic U n S) (_ : IsOperatorHom α), Function.Surjective α ∧
          ∃ c : Gal(Ω/k) → ↥(layerSub ℓ (Generic U n S) j), IsMulCocycle₁ c ∧ IsSmooth₁ c ∧
            (∀ ν : Fin t, ∀ x ∈ D ν, φ x = 1 → c x = 1) ∧
            (∀ (μ : ι) (x : ↥(A μ)), c (x : Gal(Ω/k)) = layerSubMap ℓ α j (a μ x)) ∧
            ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
              (∃ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1 ∧ c x ≠ 1) →
              (∃ (μ : ι) (ρ : Gal(Ω/k)), P = ρ • Q μ) ∨ ∀ x ∈ stabilizer Gal(Ω/k) P, F x = 1

variable {ℓ U n S j φ D}

omit [Fact ℓ.Prime] [IsAlgClosed Ω] in
/-- **An arbitrary lift of the solution below can be corrected to one whose new ramification over
the base realization is confined**, in exchange for one prescription in degree one.

The primes at which the given lift ramifies meet finitely many orbits and one prime of each is
named; the prescription is made at those of them where the solution below does not ramify over the
base realization.  At such a prime the given lift lands in the layer along the part of inertia the
base realization kills, and prescribing the cocycle to be the inverse of it there makes the
corrected lift trivial on that part, so the corrected lift does not ramify there at all.

Every other prime is answered too.  If the given lift ramifies at a prime, that prime lies in the
orbit of a named one; if the named one is one of those the prescription was made at, the corrected
lift does not ramify there, contradiction, so the solution below ramifies at it and confinement
holds.  If the given lift does not ramify at a prime but the corrected one does, the cocycle
ramifies there, and the last clause of the prescription puts that prime either in the orbit of a
named prime — impossible again, for the same reason — or at a place where the given lift, hence the
solution below, kills the whole decomposition subgroup.

The shrinking the prescription spends is passed on: the lift given is read at the number of letters
the prescription announces, and the corrected lift lives at the number asked for, over the pushed
down solution.  Confinement is still read against the solution below at the announced number, which
is what the sharper prescription is bought against. -/
theorem exists_confinedRamifiedHom_lift_of_hasFlatPrescription
    (hactφ : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)), x • v = φ x • v)
    (hpres : HasFlatPrescription ℓ U n S j φ D) :
    ∃ N : ℕ, ∀ (Φ : Gal(Ω/k) →* GenericQuot ℓ U N S j),
      (∀ x, SemidirectProduct.rightHom (Φ x) = φ x) →
      ∀ f : Gal(Ω/k) →* GenericQuot ℓ U N S (j + 1), IsSmoothHom f →
      (∀ x, (layerExtension ℓ (genericAut U N S) j).rightHom (f x) = Φ x) →
      (∀ ν : Fin t, ∀ x ∈ D ν, φ x = 1 → f x = 1) →
      ∃ (α : Generic U N S →* Generic U n S) (hα : IsOperatorHom α), Function.Surjective α ∧
        ∃ g : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1), IsSmoothHom g ∧
          (∀ x, (layerExtension ℓ (genericAut U n S) j).rightHom (g x)
            = layerSemidirectMap ℓ hα j (Φ x)) ∧
          (∀ ν : Fin t, ∀ x ∈ D ν, φ x = 1 → g x = 1) ∧ IsConfinedRamifiedHom φ Φ g := by
  obtain ⟨N, hpres⟩ := hpres
  refine ⟨N, fun Φ hΦright f hfsm hfright hfD => ?_⟩
  have hfs : IsSmooth₁ (f : Gal(Ω/k) → GenericQuot ℓ U N S (j + 1)) :=
    isSmooth₁_of_isOpenNormal_ker (isOpenNormal_ker_of_isSmoothHom hfsm)
  obtain ⟨s, Pr, hPrp, hPrbot, hfam⟩ :=
    exists_ramified_family (isOpenNormal_ker_of_isSmoothHom hfsm)
  have hstep : ∀ μ : {μ : Fin s // ¬ RamifiesAt φ Φ (Pr μ)},
      ∃ a : ↥(Ideal.inertia Gal(Ω/k) (Pr (μ : Fin s)) ⊓ φ.ker) →*
          ↥(layerSub ℓ (Generic U N S) j),
        IsSmooth₁ ((a : ↥(Ideal.inertia Gal(Ω/k) (Pr (μ : Fin s)) ⊓ φ.ker) →*
            ↥(layerSub ℓ (Generic U N S) j)) :
          ↥(Ideal.inertia Gal(Ω/k) (Pr (μ : Fin s)) ⊓ φ.ker) →
            ↥(layerSub ℓ (Generic U N S) j)) ∧
        ∀ x : ↥(Ideal.inertia Gal(Ω/k) (Pr (μ : Fin s)) ⊓ φ.ker),
          (layerExtension ℓ (genericAut U N S) j).inl (a x) * f (x : Gal(Ω/k)) = 1 := by
    rintro ⟨μ, hμ⟩
    have hΦ1 : ∀ x ∈ Ideal.inertia Gal(Ω/k) (Pr μ) ⊓ φ.ker, Φ x = 1 := by
      intro x hx
      by_contra hx1
      exact hμ ⟨x, (Subgroup.mem_inf.1 hx).1, MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).2, hx1⟩
    obtain ⟨a₀, ha₀⟩ :=
      exists_hom_inl_eq (layerExtension ℓ (genericAut U N S) j) hfright
        (Ideal.inertia Gal(Ω/k) (Pr μ) ⊓ φ.ker) hΦ1
    refine ⟨a₀⁻¹, ?_, fun x => ?_⟩
    · obtain ⟨B, hB, hBa⟩ :=
        isSmooth₁_of_inl_comp (layerExtension ℓ (genericAut U N S) j) ha₀ hfs
      refine ⟨B, hB, fun x m hm => ?_⟩
      show (a₀ (x * m))⁻¹ = (a₀ x)⁻¹
      rw [hBa x m hm]
    · show (layerExtension ℓ (genericAut U N S) j).inl ((a₀ x)⁻¹) * f (x : Gal(Ω/k)) = 1
      rw [← ha₀ x, ← _root_.map_mul, inv_mul_cancel, _root_.map_one]
  choose a hasm hakey using hstep
  obtain ⟨α, hα, hαsurj, c, hc, hcs, hcD, hca, hcram⟩ :=
    hpres f {μ : Fin s // ¬ RamifiesAt φ Φ (Pr μ)} (fun μ => Pr (μ : Fin s))
      (fun μ => Ideal.inertia Gal(Ω/k) (Pr (μ : Fin s)) ⊓ φ.ker) a hfsm (fun μ => hPrp _)
      (fun μ => hPrbot _) (fun μ => le_trans inf_le_left (Ideal.inertia_le_stabilizer _))
      (fun _ => inf_le_right) hasm
  have hΦ'right : ∀ x, SemidirectProduct.rightHom (((layerSemidirectMap ℓ hα j).comp Φ) x) = φ x :=
    fun x => hΦright x
  have hf'right : ∀ x, (layerExtension ℓ (genericAut U n S) j).rightHom
      (((layerSemidirectMap ℓ hα (j + 1)).comp f) x) = ((layerSemidirectMap ℓ hα j).comp Φ) x := by
    intro x
    rw [MonoidHom.comp_apply, rightHom_layerSemidirectMap ℓ j hα, hfright x, MonoidHom.comp_apply]
  have hf'sm : IsSmoothHom ((layerSemidirectMap ℓ hα (j + 1)).comp f) := fun M hM =>
    ⟨f.ker, isOpenNormal_ker_of_isSmoothHom hfsm, fun x hx => Subgroup.mem_comap.2 (by
      rw [MonoidHom.comp_apply, MonoidHom.mem_ker.1 hx, _root_.map_one]
      exact M.one_mem)⟩
  have hf's : IsSmooth₁ (((layerSemidirectMap ℓ hα (j + 1)).comp f) :
      Gal(Ω/k) → GenericQuot ℓ U n S (j + 1)) :=
    isSmooth₁_of_isOpenNormal_ker (isOpenNormal_ker_of_isSmoothHom hf'sm)
  have hact : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)),
      x • v = (layerExtension ℓ (genericAut U n S) j).conjActHom
        (((layerSemidirectMap ℓ hα j).comp Φ) x) v := by
    intro x v
    rw [hactφ x v, ← hΦ'right x]
    exact (genericQuotAction_smul ℓ U n n S j _ v).symm.trans
      (smul_eq_conjActHom_genericLayer ℓ U n S j _ v)
  have main : ∀ Ψ : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1),
      (∀ x, Ψ x = (layerExtension ℓ (genericAut U n S) j).inl (c x)
        * ((layerSemidirectMap ℓ hα (j + 1)).comp f) x) →
      IsConfinedRamifiedHom φ Φ Ψ := by
    intro Ψ hΨdef
    have hkey : ∀ μ : {μ : Fin s // ¬ RamifiesAt φ Φ (Pr μ)},
        ¬ RamifiesAt φ Ψ (Pr (μ : Fin s)) := by
      rintro μ ⟨x, hxI, hxφ, hxΨ⟩
      refine hxΨ ?_
      have hmem : x ∈ Ideal.inertia Gal(Ω/k) (Pr (μ : Fin s)) ⊓ φ.ker :=
        Subgroup.mem_inf.2 ⟨hxI, MonoidHom.mem_ker.2 hxφ⟩
      have h1 : c x = layerSubMap ℓ α j (a μ ⟨x, hmem⟩) := hca μ ⟨x, hmem⟩
      rw [hΨdef, h1, MonoidHom.comp_apply, ← inl_layerSemidirectMap ℓ j hα, ← _root_.map_mul,
        hakey μ ⟨x, hmem⟩, _root_.map_one]
    intro P hPp hPbot hram
    by_cases hfram : RamifiesAt φ f P
    · obtain ⟨x, hxI, -, hx1⟩ := id hfram
      obtain ⟨μ, ρ, rfl⟩ := hfam P hPp hPbot ⟨x, hxI, hx1⟩
      by_cases hΦram : RamifiesAt φ Φ (Pr μ)
      · exact Or.inl (hΦram.smul ρ)
      · exact absurd (ramifiesAt_smul_iff.1 hram) (hkey ⟨μ, hΦram⟩)
    · obtain ⟨x, hxI, hxφ, hxΨ⟩ := id hram
      have hfx : f x = 1 := by
        by_contra h
        exact hfram ⟨x, hxI, hxφ, h⟩
      have hcx : c x ≠ 1 := fun h =>
        hxΨ (by rw [hΨdef, h, _root_.map_one, one_mul, MonoidHom.comp_apply, hfx, _root_.map_one])
      rcases hcram P hPp hPbot ⟨x, hxI, hxφ, hcx⟩ with ⟨μ, ρ, rfl⟩ | hf1
      · exact absurd (ramifiesAt_smul_iff.1 hram) (hkey μ)
      · refine Or.inr fun y hy => ?_
        rw [← hfright y, hf1 y hy, _root_.map_one]
  refine ⟨α, hα, hαsurj, twistLift (layerExtension ℓ (genericAut U n S) j) hact hf'right hc,
    isSmoothHom_twistLift _ hact hf'right hc hf's hcs,
    rightHom_twistLift _ hact hf'right hc, fun ν x hx hx1 => ?_,
    main _ (twistLift_apply _ hact hf'right hc)⟩
  rw [twistLift_apply, hcD ν x hx hx1, _root_.map_one, one_mul, MonoidHom.comp_apply,
    hfD ν x hx hx1, _root_.map_one]

end Flat

end InverseGalois.Shafarevich
