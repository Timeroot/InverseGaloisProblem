/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.LiftTwist
import InverseGalois.CFT.Units.RamifiedFamily
import InverseGalois.Solvable.Shafarevich.LevelCyclicRepair

/-!
# The repair, in exchange for one prescription in degree one

Two lifts of one solution across one layer differ by a one cocycle with values in the layer, so the
repair the ladder asks for is a choice of cocycle.  What the corrected lift is asked to be is
trivial along the finite family, confined in its new ramification over the base realization — that
ramification occurring only where the solution below already ramifies or else kills the whole
decomposition subgroup — and cyclic in its local image wherever that new ramification occurs.

Only finitely many orbits of primes carry any ramification of the given lift at all, and one prime
of each can be named.  At such a prime the solution below either ramifies over the base realization,
and then the local solvability of the step supplies a local lift which is again cyclic, and the
cocycle is prescribed on the decomposition subgroup to be the discrepancy between that local lift
and the given one, so that the corrected lift agrees with it there; or it does not, and then the
given lift lands in the layer along inertia and the cocycle is prescribed to cancel it, so that the
corrected lift is unramified there outright.  Away from those primes the cocycle is asked to be
unramified, save at primes it introduces itself, where it is asked to be cyclic and the given lift
to vanish on the whole decomposition subgroup.

That is everything: at a named prime the prescription answers, at a prime the cocycle introduces
the clause it carries answers, and at any other prime neither the given lift nor the cocycle
ramifies, so neither does the corrected one.

## Main definitions

* `InverseGalois.Shafarevich.HasConfinedPrescription` — **a smooth one cocycle with values in the
  layer can be prescribed along finitely many subgroups of decomposition subgroups at once, be
  trivial along the finite family, and ramify only where it is allowed to.**

## Main results

* `InverseGalois.Shafarevich.hasSplitCyclicRepair_of_hasConfinedPrescription` — **the repair is
  bought with one such prescription**, granted the local solvability of the step at the primes where
  the solution below ramifies over the base realization.

## Tags

Shafarevich's theorem, embedding problem, one cocycle, ramification, decomposition group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT GroupExtension MulAction NumberField groupCohomology

open scoped Pointwise

attribute [local instance] genericQuotAction

/-! ### The discrepancy between two lifts along a subgroup -/

section Defect

variable {Γ N E G : Type*} [Group Γ] [TopologicalSpace Γ] [CommGroup N] [Group E] [Group G]

/-- **Two lifts of one map differ along a subgroup acting trivially on the kernel by a
homomorphism into the kernel.**

Along the subgroup the two lifts have the same image downstairs, so at each element they differ by
an element of the kernel; and the subgroup acting trivially is exactly what makes that difference
multiplicative, conjugation by the global lift fixing the kernel there.  Smoothness comes from the
smoothness of the two lifts, the two open normal subgroups on whose cosets they are constant having
an open normal intersection. -/
private theorem exists_hom_inl_mul_eq (S : GroupExtension N E G) {ρ : Γ →* G} {A : Subgroup Γ}
    (hfix : ∀ x ∈ A, ∀ v : N, S.conjActHom (ρ x) v = v) {f : Γ →* E}
    (hf : ∀ γ : Γ, S.rightHom (f γ) = ρ γ) (hfs : IsSmooth₁ (f : Γ → E)) {g : ↥A →* E}
    (hg : ∀ x : ↥A, S.rightHom (g x) = ρ (x : Γ)) (hgs : IsSmooth₁ (g : ↥A → E)) :
    ∃ a : ↥A →* N, IsSmooth₁ ((a : ↥A →* N) : ↥A → N) ∧
      ∀ x : ↥A, S.inl (a x) * f (x : Γ) = g x := by
  have hmem : ∀ x : ↥A, g x * (f (x : Γ))⁻¹ ∈ S.inl.range := by
    intro x
    rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, _root_.map_mul, _root_.map_inv, hg, hf,
      mul_inv_cancel]
  choose v hv using fun x : ↥A => MonoidHom.mem_range.1 (hmem x)
  have hconj : ∀ (x : ↥A) (w : N), f (x : Γ) * S.inl w * (f (x : Γ))⁻¹ = S.inl w := by
    intro x w
    rw [← inl_conjActHom, hf, hfix (x : Γ) x.2 w]
  have hmul : ∀ x y : ↥A, v (x * y) = v x * v y := by
    intro x y
    refine S.inl_injective ?_
    have h1 : S.inl (v (x * y)) = g x * g y * ((f (y : Γ))⁻¹ * (f (x : Γ))⁻¹) := by
      rw [hv, _root_.map_mul g, Subgroup.coe_mul, _root_.map_mul f, mul_inv_rev]
    have h2 : S.inl (v x * v y) = g x * (f (x : Γ))⁻¹ * (g y * (f (y : Γ))⁻¹) := by
      rw [_root_.map_mul, hv, hv]
    have hc : f (x : Γ) * (g y * (f (y : Γ))⁻¹) * (f (x : Γ))⁻¹ = g y * (f (y : Γ))⁻¹ := by
      rw [← hv y]
      exact hconj x (v y)
    rw [h1, h2, ← hc]
    group
  obtain ⟨B, hB, hBg⟩ := hgs
  obtain ⟨C, hC, hCf⟩ := isSmooth₁_comp (continuous_subtype A) hfs
  refine ⟨MonoidHom.mk' v hmul, ⟨B ⊓ C, hB.inf hC, fun x m hm => S.inl_injective ?_⟩, fun x => ?_⟩
  · show S.inl (v (x * m)) = S.inl (v x)
    have h1 : g (x * m) = g x := hBg x m hm.1
    have h2 : f ((x * m : ↥A) : Γ) = f (x : Γ) := hCf x m hm.2
    rw [hv, hv, h1, h2]
  · show S.inl (v x) * f (x : Γ) = g x
    rw [hv]
    group

end Defect

/-! ### The prescription the repair is bought with -/

section Prescription

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S]
  [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] (φ : Gal(Ω/k) →* U)
  [MulDistribMulAction Gal(Ω/k) ↥(layerSub ℓ (Generic U n S) j)] {t : ℕ}
  (D : Fin t → Subgroup Gal(Ω/k))

/-- **A smooth one cocycle with values in the layer can be prescribed along finitely many subgroups
of decomposition subgroups at once, be trivial along the finite family, and ramify only where it is
allowed to.**

The subgroups the cocycle is prescribed along are asked to sit inside the decomposition subgroups of
finitely many named primes and inside the kernel of the base realization, which is what makes the
prescription well posed: on such a subgroup the action on the layer is trivial, so a cocycle
restricts there to a homomorphism.  Along the finite family the cocycle is asked to vanish wherever
the base realization already does.

The last clause is the one which confines the new ramification.  At a prime where the cocycle
ramifies, either that prime is one of the named ones, or it is a prime the cocycle brings in by
itself, and there it is asked to be cyclic and the given lift to kill the whole decomposition
subgroup — which is what a prime chosen to split completely in the field the lift cuts out
supplies. -/
def HasConfinedPrescription : Prop :=
  ∀ (F : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1)) (s : ℕ) (Q : Fin s → Ideal (𝓞 Ω))
      (A : Fin s → Subgroup Gal(Ω/k))
      (a : (μ : Fin s) → ↥(A μ) →* ↥(layerSub ℓ (Generic U n S) j)),
    IsSmoothHom F → (∀ μ, (Q μ).IsPrime) → (∀ μ, Q μ ≠ ⊥) →
    (∀ μ, A μ ≤ stabilizer Gal(Ω/k) (Q μ)) → (∀ μ, A μ ≤ φ.ker) →
    (∀ μ, IsSmooth₁ ((a μ : ↥(A μ) →* ↥(layerSub ℓ (Generic U n S) j)) :
      ↥(A μ) → ↥(layerSub ℓ (Generic U n S) j))) →
      ∃ c : Gal(Ω/k) → ↥(layerSub ℓ (Generic U n S) j), IsMulCocycle₁ c ∧ IsSmooth₁ c ∧
        (∀ ν : Fin t, ∀ x ∈ D ν, φ x = 1 → c x = 1) ∧
        (∀ (μ : Fin s) (x : ↥(A μ)), c (x : Gal(Ω/k)) = a μ x) ∧
        ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → (∃ x ∈ Ideal.inertia Gal(Ω/k) P, c x ≠ 1) →
          (∃ (μ : Fin s) (ρ : Gal(Ω/k)), P = ρ • Q μ) ∨
            ((∀ x ∈ stabilizer Gal(Ω/k) P, F x = 1) ∧
              ∃ x₀ ∈ stabilizer Gal(Ω/k) P,
                ∀ x ∈ stabilizer Gal(Ω/k) P, c x ∈ Subgroup.zpowers (c x₀))

variable {ℓ U n S j φ D}

omit [Fact ℓ.Prime] [IsAlgClosed Ω] in
/-- **The repair is bought with one prescription in degree one.**

The primes at which the given lift ramifies meet finitely many orbits and one prime of each is
named.  At a named prime where the solution below ramifies over the base realization, the base
realization kills the whole decomposition subgroup, so the subgroup acts trivially on the layer and
the local lift the step supplies differs from the given lift by a homomorphism into the layer;
prescribing the cocycle to be that homomorphism makes the corrected lift agree with the local lift
there, and the local lift is cyclic.  At a named prime where the solution below does not ramify over
the base realization, the given lift lands in the layer along the part of inertia the base
realization kills, and prescribing the cocycle to be the inverse of it there makes the corrected
lift trivial on that part, so it does not ramify over the base realization at all.

At a prime which is not named, the given lift does not ramify, so any new ramification of the
corrected lift is ramification of the cocycle; and there the last clause of the prescription
supplies both the vanishing of the given lift on the whole decomposition subgroup — whence the
solution below vanishes there too, and confinement holds — and the cyclicity of the cocycle, which
is the cyclicity of the corrected lift since the given lift is trivial. -/
theorem hasSplitCyclicRepair_of_hasConfinedPrescription
    (hactφ : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)), x • v = φ x • v)
    (hram : HasSplitRamifiedLift ℓ U n S j φ)
    (hpres : HasConfinedPrescription ℓ U n S j φ D) :
    HasSplitCyclicRepair ℓ U n S j φ D := by
  intro Φ f hΦsm hΦright hΦP hfsm hfright hfD
  have hfs : IsSmooth₁ (f : Gal(Ω/k) → GenericQuot ℓ U n S (j + 1)) :=
    isSmooth₁_of_isOpenNormal_ker (isOpenNormal_ker_of_isSmoothHom hfsm)
  have hact : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)),
      x • v = (layerExtension ℓ (genericAut U n S) j).conjActHom (Φ x) v := by
    intro x v
    rw [hactφ x v, ← hΦright x]
    exact (genericQuotAction_smul ℓ U n n S j (Φ x) v).symm.trans
      (smul_eq_conjActHom_genericLayer ℓ U n S j (Φ x) v)
  obtain ⟨s, Pr, hPrp, hPrbot, hfam⟩ :=
    exists_ramified_family (isOpenNormal_ker_of_isSmoothHom hfsm)
  have hstep : ∀ μ : Fin s, ∃ (A : Subgroup Gal(Ω/k))
      (a : ↥A →* ↥(layerSub ℓ (Generic U n S) j)),
      A ≤ stabilizer Gal(Ω/k) (Pr μ) ∧ A ≤ φ.ker ∧
        IsSmooth₁ ((a : ↥A →* ↥(layerSub ℓ (Generic U n S) j)) :
          ↥A → ↥(layerSub ℓ (Generic U n S) j)) ∧
        ∀ Ψ : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1),
          (∀ x : ↥A, Ψ (x : Gal(Ω/k)) =
            (layerExtension ℓ (genericAut U n S) j).inl (a x) * f (x : Gal(Ω/k))) →
            RamifiesAt φ Ψ (Pr μ) → IsCyclicSplitAt φ Ψ (Pr μ) ∧ IsConfinedAt φ Φ (Pr μ) := by
    intro μ
    by_cases hΦram : RamifiesAt φ Φ (Pr μ)
    · obtain ⟨hsplit, htot, hcyc⟩ := hΦP (Pr μ) (hPrp μ) (hPrbot μ) hΦram
      obtain ⟨g, hgs, hgr, w, hgw⟩ :=
        hram Φ hΦsm hΦright (Pr μ) (hPrp μ) (hPrbot μ) hsplit htot hcyc
      have hfix : ∀ x ∈ stabilizer Gal(Ω/k) (Pr μ), ∀ v : ↥(layerSub ℓ (Generic U n S) j),
          (layerExtension ℓ (genericAut U n S) j).conjActHom (Φ x) v = v := by
        intro x hx v
        rw [← hact x v, hactφ x v, hsplit x hx, one_smul]
      obtain ⟨a, has, hafg⟩ :=
        exists_hom_inl_mul_eq (layerExtension ℓ (genericAut U n S) j) hfix hfright hfs hgr hgs
      have hrange : (g.range : Subgroup (GenericQuot ℓ U n S (j + 1))) ≤ Subgroup.zpowers w := by
        rintro _ ⟨x, rfl⟩
        exact hgw x
      obtain ⟨z, hzmem, hz⟩ := exists_generator_of_le_zpowers hrange
      obtain ⟨x₀, hx₀⟩ := hzmem
      refine ⟨stabilizer Gal(Ω/k) (Pr μ), a, le_rfl,
        fun x hx => MonoidHom.mem_ker.2 (hsplit x hx), has, fun Ψ hΨ _ => ⟨⟨hsplit, ?_⟩, ?_⟩⟩
      · have hΨ0 : Ψ ((x₀ : ↥(stabilizer Gal(Ω/k) (Pr μ))) : Gal(Ω/k)) = z :=
          ((hΨ x₀).trans (hafg x₀)).trans hx₀
        refine ⟨(x₀ : Gal(Ω/k)), x₀.2, fun x hx => ?_⟩
        have hΨx : Ψ x = g ⟨x, hx⟩ := (hΨ ⟨x, hx⟩).trans (hafg ⟨x, hx⟩)
        rw [hΨx, hΨ0]
        exact hz _ ⟨⟨x, hx⟩, rfl⟩
      · exact Or.inl hΦram
    · have hΦ1 : ∀ x ∈ Ideal.inertia Gal(Ω/k) (Pr μ) ⊓ φ.ker, Φ x = 1 := by
        intro x hx
        by_contra hx1
        exact hΦram ⟨x, (Subgroup.mem_inf.1 hx).1,
          MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).2, hx1⟩
      obtain ⟨a₀, ha₀⟩ :=
        exists_hom_inl_eq (layerExtension ℓ (genericAut U n S) j) hfright
          (Ideal.inertia Gal(Ω/k) (Pr μ) ⊓ φ.ker) hΦ1
      refine ⟨Ideal.inertia Gal(Ω/k) (Pr μ) ⊓ φ.ker, a₀⁻¹,
        le_trans inf_le_left (Ideal.inertia_le_stabilizer (Pr μ)), inf_le_right, ?_, ?_⟩
      · obtain ⟨B, hB, hBa⟩ :=
          isSmooth₁_of_inl_comp (layerExtension ℓ (genericAut U n S) j) ha₀ hfs
        refine ⟨B, hB, fun x m hm => ?_⟩
        show (a₀ (x * m))⁻¹ = (a₀ x)⁻¹
        rw [hBa x m hm]
      · rintro Ψ hΨ ⟨x, hxI, hxφ, hx1⟩
        refine absurd ?_ hx1
        have hmem : x ∈ Ideal.inertia Gal(Ω/k) (Pr μ) ⊓ φ.ker :=
          Subgroup.mem_inf.2 ⟨hxI, MonoidHom.mem_ker.2 hxφ⟩
        have h1 : Ψ x = (layerExtension ℓ (genericAut U n S) j).inl ((a₀ ⟨x, hmem⟩)⁻¹) * f x :=
          hΨ ⟨x, hmem⟩
        rw [h1, ← ha₀ ⟨x, hmem⟩, ← _root_.map_mul, inv_mul_cancel, _root_.map_one]
  choose A a hAstab hAker hasm hAkey using hstep
  obtain ⟨c, hc, hcs, hcD, hca, hcram⟩ :=
    hpres f s Pr A a hfsm hPrp hPrbot hAstab hAker hasm
  have main : ∀ Ψ : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1),
      (∀ x, Ψ x = (layerExtension ℓ (genericAut U n S) j).inl (c x) * f x) →
      ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → RamifiesAt φ Ψ P →
        IsCyclicSplitAt φ Ψ P ∧ IsConfinedAt φ Φ P := by
    intro Ψ hΨdef
    have hΨA : ∀ (μ : Fin s) (x : ↥(A μ)), Ψ (x : Gal(Ω/k)) =
        (layerExtension ℓ (genericAut U n S) j).inl (a μ x) * f (x : Gal(Ω/k)) :=
      fun μ x => by rw [hΨdef, hca μ x]
    intro P hPp hPbot hPram
    have horbit : (∃ (μ : Fin s) (ρ : Gal(Ω/k)), P = ρ • Pr μ) ∨
        ((∀ x ∈ stabilizer Gal(Ω/k) P, f x = 1) ∧
          ∃ x₀ ∈ stabilizer Gal(Ω/k) P,
            ∀ x ∈ stabilizer Gal(Ω/k) P, c x ∈ Subgroup.zpowers (c x₀)) := by
      obtain ⟨x, hxI, -, hxΨ⟩ := hPram
      by_cases hcx : c x = 1
      · refine Or.inl (hfam P hPp hPbot ⟨x, hxI, fun hfx => hxΨ ?_⟩)
        rw [hΨdef, hcx, _root_.map_one, one_mul, hfx]
      · exact hcram P hPp hPbot ⟨x, hxI, hcx⟩
    rcases horbit with ⟨μ, ρ, rfl⟩ | ⟨hf1, x₀, hx₀, hgen⟩
    · have h := hAkey μ Ψ (hΨA μ) (ramifiesAt_smul_iff.1 hPram)
      exact ⟨h.1.smul ρ, h.2.smul ρ⟩
    · have hΦ1 : ∀ x ∈ stabilizer Gal(Ω/k) P, Φ x = 1 := by
        intro x hx
        rw [← hfright x, hf1 x hx, _root_.map_one]
      have hφ1 : ∀ x ∈ stabilizer Gal(Ω/k) P, φ x = 1 := by
        intro x hx
        rw [← hΦright x, hΦ1 x hx, _root_.map_one]
      refine ⟨⟨hφ1, x₀, hx₀, fun x hx => ?_⟩, Or.inr hΦ1⟩
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hgen x hx)
      refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
      rw [hΨdef, hΨdef, hf1 x hx, hf1 x₀ hx₀, mul_one, mul_one, ← _root_.map_zpow, hi]
  refine ⟨twistLift (layerExtension ℓ (genericAut U n S) j) hact hfright hc,
    isSmoothHom_twistLift _ hact hfright hc hfs hcs,
    rightHom_twistLift _ hact hfright hc, fun ν x hx hx1 => ?_,
    fun P hPp hPbot h =>
      (main _ (twistLift_apply _ hact hfright hc) P hPp hPbot h).2,
    fun P hPp hPbot h =>
      (main _ (twistLift_apply _ hact hfright hc) P hPp hPbot h).1⟩
  rw [twistLift_apply, hcD ν x hx hx1, _root_.map_one, one_mul, hfD ν x hx hx1]

end Prescription

end InverseGalois.Shafarevich
