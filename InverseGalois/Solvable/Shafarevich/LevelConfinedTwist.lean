/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.LiftTwist
import InverseGalois.CFT.Units.RamifiedFamily
import InverseGalois.Solvable.Shafarevich.LevelCyclicRepair
import InverseGalois.Solvable.Shafarevich.LevelFlatTwist

/-!
# The repair, in exchange for a prescription in degree one at completely decomposed primes

Two lifts of one solution across one layer differ by a one cocycle with values in the layer, so the
repair the ladder asks for is a choice of cocycle.  What the corrected lift is asked to be is
trivial along the finite family, cyclic in its local image wherever it newly ramifies over the base
realization, and over a solution below which is totally ramified there.

The given lift is flattened first, so that its ramification over the base realization is already
confined; every prime at which it then ramifies has its whole decomposition subgroup killed by the
base realization, save those at which the solution below ramifies too, where the same is true for a
different reason.  That is what lets the sharper prescription be asked for only at primes completely
decomposed in the field the base realization cuts out.

Only finitely many orbits of primes carry any ramification of the flattened lift at all, and one
prime of each can be named.  At such a prime the solution below either ramifies over the base
realization, and then the local solvability of the step supplies a local lift which is again cyclic,
and the cocycle is prescribed on the decomposition subgroup to be the discrepancy between that local
lift and the flattened one, so that the corrected lift agrees with it there; or it does not, and
then the flattened lift lands in the layer along inertia and the cocycle is prescribed to cancel it,
so that the corrected lift is unramified there outright.  Away from those primes the cocycle is
asked to be unramified, save at primes it introduces itself, where it is asked to be cyclic and the
flattened lift to vanish on the whole decomposition subgroup.

That is everything: at a named prime the prescription answers, at a prime the cocycle introduces
the clause it carries answers, and at any other prime neither the flattened lift nor the cocycle
ramifies, so neither does the corrected one.

Both prescriptions may spend a shrinking of their own, each announcing the number of letters it
wants its data read at and answering with a surjection onto the number asked for.  The two
shrinkings compose, and the repair announces the number the flattening asks for.

## Main definitions

* `InverseGalois.Shafarevich.HasConfinedPrescription` — **a smooth one cocycle with values in the
  layer can be prescribed along finitely many subgroups of decomposition subgroups of completely
  decomposed primes at once, be trivial along the finite family, and ramify only where it is
  allowed to.**

## Main results

* `InverseGalois.Shafarevich.hasSplitCyclicRepair_of_hasConfinedPrescription` — **the repair is
  bought with one such prescription and one flat one**, granted the local solvability of the step at
  the primes where the solution below ramifies over the base realization.

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
restricts there to a homomorphism.  The named primes are asked to lie in pairwise distinct orbits,
so that no two prescriptions are made at conjugate primes.  Each such subgroup is the whole
decomposition subgroup of its prime, the one shape the repair produces: where the solution below
ramifies the local lift is prescribed there, and where it does not it kills the whole decomposition
subgroup, so the correction may be made there outright.  The named primes are themselves asked to be
completely decomposed in the field the base
realization cuts out — their whole decomposition subgroups lie in its kernel — which is what allows
the prescription to be made over that field and carried down.  Along the finite family the cocycle
is asked to vanish wherever the base realization already does.

The last clause is the one which confines the new ramification.  At a prime where the cocycle
ramifies along the part of inertia the base realization kills, either that prime is one of the
named ones, or it is a prime the cocycle brings in by itself, and there it is asked to be cyclic
and the given lift to kill the whole decomposition subgroup — which is what a prime chosen to split
completely in the field the lift cuts out supplies.

No named prime is allowed to sit over the finite family: its decomposition subgroup is asked to
escape every conjugate of every subgroup of the family, so that the prescribed values there do not
collide with the vanishing along the family.

The prescription may spend a shrinking of its own: it announces the number of letters the data is
read at, and answers with a surjection onto the number asked for and a cocycle at that number, the
prescribed values being carried across by the map of layers.

The base realization is asked to be smooth, its kernel open, that field being a finite extension. -/
def HasConfinedPrescription : Prop :=
  ∃ N : ℕ,
    IsOpen (φ.ker : Set Gal(Ω/k)) →
    ∀ (F : Gal(Ω/k) →* GenericQuot ℓ U N S (j + 1)) (ι : Type) [Finite ι]
        (Q : ι → Ideal (𝓞 Ω)) (A : ι → Subgroup Gal(Ω/k))
        (a : (μ : ι) → ↥(A μ) →* ↥(layerSub ℓ (Generic U N S) j)),
      IsSmoothHom F → (∀ μ, (Q μ).IsPrime) → (∀ μ, Q μ ≠ ⊥) →
      (∀ (μ ν : ι) (ρ : Gal(Ω/k)), ρ • Q μ = Q ν → μ = ν) →
      (∀ μ, stabilizer Gal(Ω/k) (Q μ) ≤ φ.ker) →
      (∀ μ, A μ ≤ stabilizer Gal(Ω/k) (Q μ)) → (∀ μ, A μ ≤ φ.ker) →
      (∀ μ, A μ = stabilizer Gal(Ω/k) (Q μ)) →
      (∀ μ, IsSmooth₁ ((a μ : ↥(A μ) →* ↥(layerSub ℓ (Generic U N S) j)) :
        ↥(A μ) → ↥(layerSub ℓ (Generic U N S) j))) →
      (∀ (μ : ι) (ν : Fin t) (ρ : Gal(Ω/k)),
        ∃ y ∈ stabilizer Gal(Ω/k) (Q μ), ρ * y * ρ⁻¹ ∉ D ν) →
        ∃ (α : Generic U N S →* Generic U n S) (_ : IsOperatorHom α), Function.Surjective α ∧
          ∃ c : Gal(Ω/k) → ↥(layerSub ℓ (Generic U n S) j), IsMulCocycle₁ c ∧ IsSmooth₁ c ∧
            (∀ ν : Fin t, ∀ x ∈ D ν, φ x = 1 → c x = 1) ∧
            (∀ (μ : ι) (x : ↥(A μ)), c (x : Gal(Ω/k)) = layerSubMap ℓ α j (a μ x)) ∧
            ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
              (∃ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1 ∧ c x ≠ 1) →
              (∃ (μ : ι) (ρ : Gal(Ω/k)), P = ρ • Q μ) ∨
                ((∀ x ∈ stabilizer Gal(Ω/k) P, F x = 1) ∧
                  ∃ x₀ ∈ stabilizer Gal(Ω/k) P,
                    ∀ x ∈ stabilizer Gal(Ω/k) P, c x ∈ Subgroup.zpowers (c x₀))

variable {ℓ U n S j φ D}

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in
omit [Fact ℓ.Prime] [IsAlgClosed Ω] in
/-- **The repair is bought with two prescriptions in degree one.**

The given lift is first flattened: the weaker prescription corrects it to a lift whose new
ramification over the base realization occurs only where the solution below already ramifies, or
else at primes the solution below kills the whole decomposition subgroup of — which are exactly the
primes completely decomposed in the field it cuts out.  That is what makes the second prescription
admissible, its named primes being asked to be of that kind.

The primes at which the flattened lift ramifies meet finitely many orbits and one prime of each is
named.  At a named prime where the solution below ramifies over the base realization, the base
realization kills the whole decomposition subgroup, so the subgroup acts trivially on the layer and
the local lift the step supplies differs from the flattened lift by a homomorphism into the layer;
prescribing the cocycle to be that homomorphism makes the corrected lift agree with the local lift
there, and the local lift is cyclic.  The clauses the step is read against are those of the solution
below, carried across the shrinking the flattening spends: the values can only be identified, and
the order of the generator of the local image only drop to a divisor.  At a named prime where the
solution below does not ramify over the base realization, the confinement of the flattened lift says
the solution below takes no value at all on the decomposition subgroup, so the flattened lift lands
in the layer along the whole of it, and prescribing the cocycle to be the inverse of it there makes
the corrected lift trivial there, so it does not ramify over the base realization at all.

Either way the subgroup carrying the prescription is the whole decomposition subgroup, which is what
lets the sharper prescription be asked for along decomposition subgroups alone.

None of the named primes sits over the finite family, and nothing has to be arranged for that: the
flattened lift is trivial along the family, hence along the decomposition subgroup of any prime
sitting over it, and a named prime is one it ramifies at.

At a prime which is not named, the flattened lift does not ramify, so any new ramification of the
corrected lift is ramification of the cocycle; and there the last clause of the prescription
supplies both the vanishing of the flattened lift on the whole decomposition subgroup — whence the
solution below vanishes there too, and is totally ramified for want of any value at all — and the
cyclicity of the cocycle, which is the cyclicity of the corrected lift since the flattened lift is
trivial.

Each prescription is read at the number of letters it announces and answers at the number asked
for; the two shrinkings compose, and the solution below is carried down along their composite.  The
local solvability of the step is therefore asked for at every number of letters, as is the flat
prescription. -/
theorem hasSplitCyclicRepair_of_hasConfinedPrescription
    (hactφ : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)), x • v = φ x • v)
    (hram : ∀ m : ℕ, HasSplitRamifiedLift ℓ U m S j φ)
    (hflat : ∀ m : ℕ,
      letI := galLayerAction ℓ U m S j φ
      HasFlatPrescription ℓ U m S j φ D)
    (hpres : HasConfinedPrescription ℓ U n S j φ D) :
    HasSplitCyclicRepair ℓ U n S j φ D := by
  obtain ⟨N₂, hpres⟩ := hpres
  letI := galLayerAction ℓ U N₂ S j φ
  obtain ⟨N₁, hflat'⟩ :=
    exists_confinedRamifiedHom_lift_of_hasFlatPrescription (n := N₂) (fun _ _ => rfl) (hflat N₂)
  refine ⟨N₁, fun Φ f₀ hΦsm hΦright hΦP hf₀sm hf₀right hf₀D => ?_⟩
  have hφopen : IsOpen (φ.ker : Set Gal(Ω/k)) := by
    refine Subgroup.isOpen_mono (H₁ := Φ.ker) (fun x hx => MonoidHom.mem_ker.2 ?_)
      (isOpenNormal_ker_of_isSmoothHom hΦsm).isOpen
    rw [← hΦright x, MonoidHom.mem_ker.1 hx, _root_.map_one]
  obtain ⟨α₁, hα₁, hα₁surj, f, hfsm, hfright₀, hfD, hfconf⟩ :=
    hflat' Φ hΦright f₀ hf₀sm hf₀right hf₀D
  obtain ⟨Φ₁, hcompapp, hΦ₁sm, hΦ₁right⟩ :
      ∃ Φ₁ : Gal(Ω/k) →* GenericQuot ℓ U N₂ S j,
        (∀ y, Φ₁ y = layerSemidirectMap ℓ hα₁ j (Φ y)) ∧ IsSmoothHom Φ₁ ∧
          ∀ x, SemidirectProduct.rightHom (Φ₁ x) = φ x :=
    ⟨(layerSemidirectMap ℓ hα₁ j).comp Φ, fun _ => rfl,
      (fun M hM => ⟨Φ.ker, isOpenNormal_ker_of_isSmoothHom hΦsm, fun x hx =>
        Subgroup.mem_comap.2 (by
          rw [MonoidHom.comp_apply, MonoidHom.mem_ker.1 hx, _root_.map_one]
          exact M.one_mem)⟩),
      fun x => hΦright x⟩
  have hfright : ∀ x, (layerExtension ℓ (genericAut U N₂ S) j).rightHom (f x) = Φ₁ x := by
    intro x
    rw [hcompapp x]
    exact hfright₀ x
  have hfs : IsSmooth₁ (f : Gal(Ω/k) → GenericQuot ℓ U N₂ S (j + 1)) :=
    isSmooth₁_of_isOpenNormal_ker (isOpenNormal_ker_of_isSmoothHom hfsm)
  have hactΦ₁ : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U N₂ S) j)),
      x • v = (layerExtension ℓ (genericAut U N₂ S) j).conjActHom (Φ₁ x) v := by
    intro x v
    show φ x • v = _
    rw [← hΦ₁right x]
    exact (genericQuotAction_smul ℓ U N₂ N₂ S j (Φ₁ x) v).symm.trans
      (smul_eq_conjActHom_genericLayer ℓ U N₂ S j (Φ₁ x) v)
  obtain ⟨s, Pr, hPrp, hPrbot, hfam⟩ :=
    exists_ramified_family (isOpenNormal_ker_of_isSmoothHom hfsm)
  have hQker : ∀ μ : {μ : Fin s // RamifiesAt φ f (Pr μ)},
      stabilizer Gal(Ω/k) (Pr (μ : Fin s)) ≤ φ.ker := by
    rintro ⟨μ, hμ⟩ x hx
    rcases hfconf (Pr μ) (hPrp μ) (hPrbot μ) hμ with hΦram | hΦ1
    · exact MonoidHom.mem_ker.2 ((hΦP (Pr μ) (hPrp μ) (hPrbot μ) hΦram).1 x hx)
    · exact MonoidHom.mem_ker.2 (by rw [← hΦright x, hΦ1 x hx, _root_.map_one])
  have hstep : ∀ μ : {μ : Fin s // RamifiesAt φ f (Pr μ)}, ∃ (A : Subgroup Gal(Ω/k))
      (a : ↥A →* ↥(layerSub ℓ (Generic U N₂ S) j)),
      A ≤ stabilizer Gal(Ω/k) (Pr (μ : Fin s)) ∧ A ≤ φ.ker ∧
        A = stabilizer Gal(Ω/k) (Pr (μ : Fin s)) ∧
        IsSmooth₁ ((a : ↥A →* ↥(layerSub ℓ (Generic U N₂ S) j)) :
          ↥A → ↥(layerSub ℓ (Generic U N₂ S) j)) ∧
        ∀ (β : Generic U N₂ S →* Generic U n S) (hβ : IsOperatorHom β)
            (Ψ : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1)),
          (∀ x : ↥A, Ψ (x : Gal(Ω/k)) = (layerExtension ℓ (genericAut U n S) j).inl
            (layerSubMap ℓ β j (a x)) * layerSemidirectMap ℓ hβ (j + 1) (f (x : Gal(Ω/k)))) →
            RamifiesAt φ Ψ (Pr (μ : Fin s)) →
              IsCyclicSplitAt φ Ψ (Pr (μ : Fin s)) ∧ IsTotallyRamifiedAt Φ₁ (Pr (μ : Fin s)) := by
    rintro ⟨μ, hμ⟩
    by_cases hΦram : RamifiesAt φ Φ (Pr μ)
    · obtain ⟨hsplit, htot₀, c₀, hc₀, hζ₀⟩ := hΦP (Pr μ) (hPrp μ) (hPrbot μ) hΦram
      have htot : ∀ x ∈ stabilizer Gal(Ω/k) (Pr μ),
          ∃ y ∈ Ideal.inertia Gal(Ω/k) (Pr μ), Φ₁ x = Φ₁ y := by
        intro x hx
        obtain ⟨y, hyI, hy⟩ := htot₀ x hx
        exact ⟨y, hyI, by rw [hcompapp, hcompapp, hy]⟩
      have hcyc : ∃ c, (∀ x ∈ stabilizer Gal(Ω/k) (Pr μ), Φ₁ x ∈ Subgroup.zpowers c) ∧
          ∀ ζ : Ωˣ, ζ ^ (ℓ * orderOf c) = 1 → ∀ x ∈ stabilizer Gal(Ω/k) (Pr μ), x • ζ = ζ := by
        refine ⟨layerSemidirectMap ℓ hα₁ j c₀, fun x hx => ?_, fun ζ hζ x hx => ?_⟩
        · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hc₀ x hx)
          exact Subgroup.mem_zpowers_iff.2 ⟨i, by rw [← _root_.map_zpow, hi, hcompapp]⟩
        · obtain ⟨q, hq⟩ :=
            mul_dvd_mul_left ℓ (orderOf_map_dvd (layerSemidirectMap ℓ hα₁ j) c₀)
          exact hζ₀ ζ (by rw [hq, pow_mul, hζ, one_pow]) x hx
      obtain ⟨g, hgs, hgr, w, hgw⟩ :=
        hram N₂ Φ₁ hΦ₁sm hΦ₁right (Pr μ) (hPrp μ) (hPrbot μ) hsplit htot hcyc
      have hfix : ∀ x ∈ stabilizer Gal(Ω/k) (Pr μ),
          ∀ v : ↥(layerSub ℓ (Generic U N₂ S) j),
          (layerExtension ℓ (genericAut U N₂ S) j).conjActHom (Φ₁ x) v = v := by
        intro x hx v
        rw [← hactΦ₁ x v]
        show φ x • v = v
        rw [hsplit x hx, one_smul]
      obtain ⟨a, has, hafg⟩ :=
        exists_hom_inl_mul_eq (layerExtension ℓ (genericAut U N₂ S) j) hfix hfright hfs hgr hgs
      have hrange : (g.range : Subgroup (GenericQuot ℓ U N₂ S (j + 1)))
          ≤ Subgroup.zpowers w := by
        rintro _ ⟨x, rfl⟩
        exact hgw x
      obtain ⟨z, hzmem, hz⟩ := exists_generator_of_le_zpowers hrange
      obtain ⟨x₀, hx₀⟩ := hzmem
      refine ⟨stabilizer Gal(Ω/k) (Pr μ), a, le_rfl,
        fun x hx => MonoidHom.mem_ker.2 (hsplit x hx), rfl, has,
        fun β hβ Ψ hΨ _ => ⟨⟨hsplit, ?_⟩, htot⟩⟩
      have hΨmap : ∀ x : ↥(stabilizer Gal(Ω/k) (Pr μ)),
          Ψ (x : Gal(Ω/k)) = layerSemidirectMap ℓ hβ (j + 1) (g x) := by
        intro x
        rw [hΨ x, ← inl_layerSemidirectMap ℓ j hβ, ← _root_.map_mul, hafg x]
      refine ⟨(x₀ : Gal(Ω/k)), x₀.2, fun x hx => ?_⟩
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hz _ ⟨⟨x, hx⟩, rfl⟩)
      refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
      have hΨx : Ψ x = layerSemidirectMap ℓ hβ (j + 1) (g ⟨x, hx⟩) := hΨmap ⟨x, hx⟩
      have hΨ0 : Ψ (x₀ : Gal(Ω/k)) = layerSemidirectMap ℓ hβ (j + 1) z := by
        rw [hΨmap x₀, hx₀]
      rw [hΨx, hΨ0, ← _root_.map_zpow, hi]
    · have hΦ1 : ∀ x ∈ stabilizer Gal(Ω/k) (Pr μ), Φ₁ x = 1 := by
        rcases hfconf (Pr μ) (hPrp μ) (hPrbot μ) hμ with h | h
        · exact absurd h hΦram
        · intro x hx
          rw [hcompapp, h x hx, _root_.map_one]
      obtain ⟨a₀, ha₀⟩ :=
        exists_hom_inl_eq (layerExtension ℓ (genericAut U N₂ S) j) hfright
          (stabilizer Gal(Ω/k) (Pr μ)) hΦ1
      refine ⟨stabilizer Gal(Ω/k) (Pr μ), a₀⁻¹, le_rfl, hQker ⟨μ, hμ⟩, rfl, ?_, ?_⟩
      · obtain ⟨B, hB, hBa⟩ :=
          isSmooth₁_of_inl_comp (layerExtension ℓ (genericAut U N₂ S) j) ha₀ hfs
        refine ⟨B, hB, fun x m hm => ?_⟩
        show (a₀ (x * m))⁻¹ = (a₀ x)⁻¹
        rw [hBa x m hm]
      · rintro β hβ Ψ hΨ ⟨x, hxI, hxφ, hx1⟩
        refine absurd ?_ hx1
        have hmem : x ∈ stabilizer Gal(Ω/k) (Pr μ) := Ideal.inertia_le_stabilizer (Pr μ) hxI
        have h1 : Ψ x = (layerExtension ℓ (genericAut U n S) j).inl
            (layerSubMap ℓ β j ((a₀ ⟨x, hmem⟩)⁻¹)) *
            layerSemidirectMap ℓ hβ (j + 1) (f x) := hΨ ⟨x, hmem⟩
        have h2 : (layerExtension ℓ (genericAut U N₂ S) j).inl ((a₀ ⟨x, hmem⟩)⁻¹) * f x = 1 := by
          rw [← ha₀ ⟨x, hmem⟩, ← _root_.map_mul, inv_mul_cancel, _root_.map_one]
        rw [h1, ← inl_layerSemidirectMap ℓ j hβ, ← _root_.map_mul, h2, _root_.map_one]
  choose A a hAstab hAker hAcase hasm hAkey using hstep
  have hmin : ∀ μ : Fin s, RamifiesAt φ f (Pr μ) →
      ∃ μ' : Fin s, (RamifiesAt φ f (Pr μ') ∧
        ∀ ν, ν < μ' → ¬∃ ρ : Gal(Ω/k), Pr μ' = ρ • Pr ν) ∧
        ∃ τ : Gal(Ω/k), Pr μ = τ • Pr μ' := by
    classical
    intro μ hμ
    set Trep : Finset (Fin s) :=
      Finset.univ.filter (fun ν => ∃ ρ : Gal(Ω/k), Pr μ = ρ • Pr ν) with hTrep
    have hmemT : ∀ ν, ν ∈ Trep ↔ ∃ ρ : Gal(Ω/k), Pr μ = ρ • Pr ν := by
      intro ν
      rw [hTrep, Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
    have hne : Trep.Nonempty := ⟨μ, (hmemT μ).2 ⟨1, (one_smul Gal(Ω/k) (Pr μ)).symm⟩⟩
    obtain ⟨τ, hτ⟩ := (hmemT _).1 (Trep.min'_mem hne)
    refine ⟨Trep.min' hne, ⟨?_, ?_⟩, τ, hτ⟩
    · refine (ramifiesAt_smul_iff (ρ := τ)).1 ?_
      rwa [← hτ]
    · rintro ν hν ⟨ρ, hρ⟩
      refine absurd (Trep.min'_le ν ((hmemT ν).2 ⟨τ * ρ, ?_⟩)) (not_le.2 hν)
      rw [hτ, hρ, mul_smul τ ρ (Pr ν)]
  have hQorb : ∀ (μ ν : {μ : Fin s // RamifiesAt φ f (Pr μ) ∧
        ∀ ν, ν < μ → ¬∃ ρ : Gal(Ω/k), Pr μ = ρ • Pr ν}) (ρ : Gal(Ω/k)),
      ρ • Pr (μ : Fin s) = Pr (ν : Fin s) → μ = ν := by
    rintro ⟨μ, _, hμmin⟩ ⟨ν, _, hνmin⟩ ρ hρ
    refine Subtype.ext ?_
    rcases lt_trichotomy μ ν with h | h | h
    · exact absurd ⟨ρ, hρ.symm⟩ (hνmin μ h)
    · exact h
    · refine absurd ⟨ρ⁻¹, ?_⟩ (hμmin ν h)
      rw [← hρ]
      exact (inv_smul_smul ρ (Pr μ)).symm
  have havoid : ∀ (μ : {μ : Fin s // RamifiesAt φ f (Pr μ) ∧
        ∀ ν, ν < μ → ¬∃ ρ : Gal(Ω/k), Pr μ = ρ • Pr ν}) (ν : Fin t) (ρ : Gal(Ω/k)),
      ∃ y ∈ stabilizer Gal(Ω/k) (Pr (μ : Fin s)), ρ * y * ρ⁻¹ ∉ D ν := by
    rintro ⟨μ, hμ, -⟩ ν ρ
    obtain ⟨x, hxI, hxφ, hx1⟩ := id hμ
    refine ⟨x, Ideal.inertia_le_stabilizer (Pr μ) hxI, fun hmem => hx1 ?_⟩
    have hφc : φ (ρ * x * ρ⁻¹) = 1 := by
      rw [_root_.map_mul, _root_.map_mul, _root_.map_inv, hxφ, mul_one, mul_inv_cancel]
    have hconj : f (ρ * x * ρ⁻¹) = 1 := hfD ν _ hmem hφc
    rw [_root_.map_mul, _root_.map_mul, _root_.map_inv] at hconj
    simpa using hconj
  obtain ⟨α₂, hα₂, hα₂surj, c, hc, hcs, hcD, hca, hcram⟩ :=
    hpres hφopen f {μ : Fin s // RamifiesAt φ f (Pr μ) ∧
        ∀ ν, ν < μ → ¬∃ ρ : Gal(Ω/k), Pr μ = ρ • Pr ν} (fun μ => Pr (μ : Fin s))
      (fun μ => A ⟨μ.1, μ.2.1⟩) (fun μ => a ⟨μ.1, μ.2.1⟩) hfsm
      (fun μ => hPrp _) (fun μ => hPrbot _) hQorb (fun μ => hQker ⟨μ.1, μ.2.1⟩)
      (fun μ => hAstab ⟨μ.1, μ.2.1⟩) (fun μ => hAker ⟨μ.1, μ.2.1⟩)
      (fun μ => hAcase ⟨μ.1, μ.2.1⟩) (fun μ => hasm ⟨μ.1, μ.2.1⟩) havoid
  have hΦ₂right : ∀ x, SemidirectProduct.rightHom
      (((layerSemidirectMap ℓ hα₂ j).comp Φ₁) x) = φ x := fun x => hΦ₁right x
  have hf₂right : ∀ x, (layerExtension ℓ (genericAut U n S) j).rightHom
      (((layerSemidirectMap ℓ hα₂ (j + 1)).comp f) x)
      = ((layerSemidirectMap ℓ hα₂ j).comp Φ₁) x := by
    intro x
    rw [MonoidHom.comp_apply, rightHom_layerSemidirectMap ℓ j hα₂, hfright x, MonoidHom.comp_apply]
  have hf₂sm : IsSmoothHom ((layerSemidirectMap ℓ hα₂ (j + 1)).comp f) := fun M hM =>
    ⟨f.ker, isOpenNormal_ker_of_isSmoothHom hfsm, fun x hx => Subgroup.mem_comap.2 (by
      rw [MonoidHom.comp_apply, MonoidHom.mem_ker.1 hx, _root_.map_one]
      exact M.one_mem)⟩
  have hf₂s : IsSmooth₁ (((layerSemidirectMap ℓ hα₂ (j + 1)).comp f) :
      Gal(Ω/k) → GenericQuot ℓ U n S (j + 1)) :=
    isSmooth₁_of_isOpenNormal_ker (isOpenNormal_ker_of_isSmoothHom hf₂sm)
  have hact : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)),
      x • v = (layerExtension ℓ (genericAut U n S) j).conjActHom
        (((layerSemidirectMap ℓ hα₂ j).comp Φ₁) x) v := by
    intro x v
    rw [hactφ x v, ← hΦ₂right x]
    exact (genericQuotAction_smul ℓ U n n S j _ v).symm.trans
      (smul_eq_conjActHom_genericLayer ℓ U n S j _ v)
  have main : ∀ Ψ : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1),
      (∀ x, Ψ x = (layerExtension ℓ (genericAut U n S) j).inl (c x)
        * ((layerSemidirectMap ℓ hα₂ (j + 1)).comp f) x) →
      ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → RamifiesAt φ Ψ P →
        IsCyclicSplitAt φ Ψ P ∧ IsTotallyRamifiedAt Φ₁ P := by
    intro Ψ hΨdef
    have hΨA : ∀ (μ : {μ : Fin s // RamifiesAt φ f (Pr μ) ∧
        ∀ ν, ν < μ → ¬∃ ρ : Gal(Ω/k), Pr μ = ρ • Pr ν}) (x : ↥(A ⟨μ.1, μ.2.1⟩)),
        Ψ (x : Gal(Ω/k)) = (layerExtension ℓ (genericAut U n S) j).inl
          (layerSubMap ℓ α₂ j (a ⟨μ.1, μ.2.1⟩ x)) *
          ((layerSemidirectMap ℓ hα₂ (j + 1)).comp f) (x : Gal(Ω/k)) :=
      fun μ x => by rw [hΨdef, hca μ x]
    intro P hPp hPbot hPram
    by_cases hfram : RamifiesAt φ f P
    · obtain ⟨x, hxI, -, hx1⟩ := id hfram
      obtain ⟨μ, ρ, rfl⟩ := hfam P hPp hPbot ⟨x, hxI, hx1⟩
      have hμ : RamifiesAt φ f (Pr μ) := ramifiesAt_smul_iff.1 hfram
      obtain ⟨μ', hμ', τ, hτ⟩ := hmin μ hμ
      have hPeq : ρ • Pr μ = (ρ * τ) • Pr μ' := by rw [hτ, mul_smul ρ τ (Pr μ')]
      have hPram' : RamifiesAt φ Ψ (Pr μ') :=
        (ramifiesAt_smul_iff (ρ := ρ * τ)).1 (by rwa [← hPeq])
      have h := hAkey ⟨μ', hμ'.1⟩ α₂ hα₂ Ψ (hΨA ⟨μ', hμ'⟩) hPram'
      rw [hPeq]
      exact ⟨h.1.smul (ρ * τ), h.2.smul (ρ * τ)⟩
    · obtain ⟨x, hxI, hxφ, hxΨ⟩ := id hPram
      have hfx : f x = 1 := by
        by_contra h
        exact hfram ⟨x, hxI, hxφ, h⟩
      have hcx : c x ≠ 1 := fun h =>
        hxΨ (by rw [hΨdef, h, _root_.map_one, one_mul, MonoidHom.comp_apply, hfx, _root_.map_one])
      rcases hcram P hPp hPbot ⟨x, hxI, hxφ, hcx⟩ with ⟨μ, ρ, rfl⟩ | ⟨hf1, x₀, hx₀, hgen⟩
      · exact absurd (μ.2.1.smul ρ) hfram
      · have hΦ₁1 : ∀ x ∈ stabilizer Gal(Ω/k) P, Φ₁ x = 1 := by
          intro x hx
          rw [← hfright x, hf1 x hx, _root_.map_one]
        have hφ1 : ∀ x ∈ stabilizer Gal(Ω/k) P, φ x = 1 := by
          intro x hx
          rw [← hΦ₁right x, hΦ₁1 x hx, _root_.map_one]
        refine ⟨⟨hφ1, x₀, hx₀, fun y hy => ?_⟩, isTotallyRamifiedAt_of_forall_eq_one hΦ₁1⟩
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hgen y hy)
        refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
        rw [hΨdef, hΨdef, MonoidHom.comp_apply, MonoidHom.comp_apply, hf1 y hy, hf1 x₀ hx₀,
          _root_.map_one, mul_one, mul_one, ← _root_.map_zpow, hi]
  have hαsurj : Function.Surjective ((α₂.comp α₁ : Generic U N₁ S →* Generic U n S) :
      Generic U N₁ S → Generic U n S) := hα₂surj.comp hα₁surj
  have hcong : ∀ x, ((layerSemidirectMap ℓ hα₂ j).comp Φ₁) x
      = ((layerSemidirectMap ℓ (hα₂.comp hα₁) j).comp Φ) x := by
    intro x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hcompapp x]
    exact layerSemidirectMap_comp ℓ hα₁ hα₂ (hα₂.comp hα₁) j (Φ x)
  have h6 : ∀ x, (layerExtension ℓ (genericAut U n S) j).rightHom
      (twistLift (layerExtension ℓ (genericAut U n S) j) hact hf₂right hc x)
      = layerSemidirectMap ℓ (hα₂.comp hα₁) j (Φ x) := by
    intro x
    rw [rightHom_twistLift _ hact hf₂right hc x, hcong x, MonoidHom.comp_apply]
  refine ⟨α₂.comp α₁, hα₂.comp hα₁, hαsurj,
    twistLift (layerExtension ℓ (genericAut U n S) j) hact hf₂right hc,
    isSmoothHom_twistLift _ hact hf₂right hc hf₂s hcs, h6, fun ν x hx hx1 => ?_,
    fun P hPp hPbot h =>
      ((main _ (twistLift_apply _ hact hf₂right hc) P hPp hPbot h).2.comp
        (layerSemidirectMap ℓ hα₂ j)).congr hcong,
    fun P hPp hPbot h =>
      (main _ (twistLift_apply _ hact hf₂right hc) P hPp hPbot h).1⟩
  rw [twistLift_apply, hcD ν x hx hx1, _root_.map_one, one_mul, MonoidHom.comp_apply,
    hfD ν x hx hx1, _root_.map_one]

end Prescription

end InverseGalois.Shafarevich
