/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.ExtensionMap

/-!
# Pulling an extension back along a homomorphism, and the obstruction to a lift

An embedding problem is a homomorphism `ρ : Γ →* G` together with an extension
`1 → N → E → G → 1`, and to solve it is to lift `ρ` to a homomorphism `Γ →* E`.  Pulling the
extension back along `ρ` turns the question into one about a single extension: the fibre product
of `E` and `Γ` over `G` is an extension of `Γ` by `N`, and a lift of `ρ` is exactly a splitting of
it.

When the kernel is abelian the splittings are counted by the cohomology class of the extension, so
the embedding problem is solvable precisely when the class of the pullback vanishes; and since the
projection of the fibre product onto `E` is a morphism of extensions over `ρ`, that class is the
class of the original extension pulled back along `ρ`.

## Main definitions

* `GroupExtension.pullbackSubgroup`: the fibre product of the middle term of an extension with a
  group over the quotient.
* `GroupExtension.pullback`: that fibre product as an extension of the given group by the same
  kernel.

## Main results

* `GroupExtension.pullback_conjActHom`: the action of the pullback on the kernel is the original
  action read through the given homomorphism.
* `GroupExtension.exists_factorSet_pullback_eq`: the factor set of the pullback is the factor set
  of the original extension composed with the given homomorphism, up to a coboundary.
* `GroupExtension.nonempty_splitting_pullback_iff`: **the pullback splits exactly when the given
  homomorphism lifts to the middle term.**
* `GroupExtension.exists_lift_iff_cohomologyClass_pullback_eq_zero`: **an embedding problem with
  abelian kernel is solvable exactly when the class of the pullback vanishes.**

## Tags

group extension, embedding problem, fibre product, obstruction, two-cocycle
-/

open groupCohomology

namespace GroupExtension

section Pullback

variable {N E G Γ : Type*} [Group N] [Group E] [Group G] [Group Γ]

/-- The fibre product of the middle term of an extension with a group over the quotient. -/
def pullbackSubgroup (S : GroupExtension N E G) (ρ : Γ →* G) : Subgroup (E × Γ) where
  carrier := {x | S.rightHom x.1 = ρ x.2}
  one_mem' := by simp
  mul_mem' hx hy := by
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at hx hy ⊢
    rw [hx, hy]
  inv_mem' hx := by
    simp only [Set.mem_setOf_eq, Prod.fst_inv, Prod.snd_inv, map_inv] at hx ⊢
    rw [hx]

@[simp]
theorem mem_pullbackSubgroup {S : GroupExtension N E G} {ρ : Γ →* G} {x : E × Γ} :
    x ∈ S.pullbackSubgroup ρ ↔ S.rightHom x.1 = ρ x.2 := Iff.rfl

/-- The projection of the fibre product onto the middle term of the original extension. -/
def pullbackFst (S : GroupExtension N E G) (ρ : Γ →* G) : S.pullbackSubgroup ρ →* E :=
  (MonoidHom.fst E Γ).comp (S.pullbackSubgroup ρ).subtype

@[simp]
theorem pullbackFst_apply (S : GroupExtension N E G) (ρ : Γ →* G) (x : S.pullbackSubgroup ρ) :
    S.pullbackFst ρ x = (x : E × Γ).1 := rfl

/-- **The pullback of an extension along a homomorphism into its quotient**: the fibre product of
the middle term with the given group, as an extension of that group by the same kernel. -/
def pullback (S : GroupExtension N E G) (ρ : Γ →* G) :
    GroupExtension N (S.pullbackSubgroup ρ) Γ where
  inl := (S.inl.prod 1).codRestrict (S.pullbackSubgroup ρ) fun n ↦ by simp
  rightHom := (MonoidHom.snd E Γ).comp (S.pullbackSubgroup ρ).subtype
  inl_injective a b hab := S.inl_injective (congrArg (fun x : S.pullbackSubgroup ρ ↦
    (x : E × Γ).1) hab)
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      rfl
    · intro hx
      have hx2 : (x : E × Γ).2 = 1 := hx
      have hker : (x : E × Γ).1 ∈ S.inl.range := by
        rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, x.2, hx2, map_one]
      obtain ⟨n, hn⟩ := hker
      exact ⟨n, Subtype.ext (Prod.ext hn hx2.symm)⟩
  rightHom_surjective γ := by
    obtain ⟨e, he⟩ := S.rightHom_surjective (ρ γ)
    exact ⟨⟨(e, γ), he⟩, rfl⟩

@[simp]
theorem coe_pullback_inl (S : GroupExtension N E G) (ρ : Γ →* G) (n : N) :
    (((S.pullback ρ).inl n : S.pullbackSubgroup ρ) : E × Γ) = (S.inl n, 1) := rfl

@[simp]
theorem pullback_rightHom_apply (S : GroupExtension N E G) (ρ : Γ →* G)
    (x : S.pullbackSubgroup ρ) : (S.pullback ρ).rightHom x = (x : E × Γ).2 := rfl

/-- The projection onto the middle term is a morphism of extensions from the pullback to the
original extension, over the given homomorphism. -/
theorem rightHom_pullbackFst (S : GroupExtension N E G) (ρ : Γ →* G) (x : S.pullbackSubgroup ρ) :
    S.rightHom (S.pullbackFst ρ x) = ρ ((S.pullback ρ).rightHom x) := x.2

/-! ### Lifts and splittings -/

/-- A homomorphism to the middle term lifting the given homomorphism splits the pullback. -/
def pullbackSplitting (S : GroupExtension N E G) (ρ : Γ →* G) (f : Γ →* E)
    (hf : ∀ γ, S.rightHom (f γ) = ρ γ) : (S.pullback ρ).Splitting where
  __ := MonoidHom.mk' (fun γ ↦ (⟨(f γ, γ), hf γ⟩ : S.pullbackSubgroup ρ))
    fun g h ↦ Subtype.ext (Prod.ext (map_mul f g h) rfl)
  rightInverse_rightHom _ := rfl

/-- A splitting of the pullback gives a homomorphism to the middle term lifting the given
homomorphism. -/
theorem exists_lift_of_splitting_pullback (S : GroupExtension N E G) (ρ : Γ →* G)
    (s : (S.pullback ρ).Splitting) :
    ∃ f : Γ →* E, ∀ γ, S.rightHom (f γ) = ρ γ := by
  refine ⟨(S.pullbackFst ρ).comp s.toMonoidHom, fun γ ↦ ?_⟩
  rw [MonoidHom.comp_apply, rightHom_pullbackFst]
  exact congrArg ρ (s.rightInverse_rightHom γ)

/-- **The pullback splits exactly when the given homomorphism lifts to the middle term.** -/
theorem nonempty_splitting_pullback_iff (S : GroupExtension N E G) (ρ : Γ →* G) :
    Nonempty (S.pullback ρ).Splitting ↔ ∃ f : Γ →* E, ∀ γ, S.rightHom (f γ) = ρ γ :=
  ⟨fun ⟨s⟩ ↦ exists_lift_of_splitting_pullback S ρ s,
    fun ⟨f, hf⟩ ↦ ⟨pullbackSplitting S ρ f hf⟩⟩

end Pullback

/-! ### The class of the pullback -/

section AbelianKernel

variable {N E G Γ : Type*} [CommGroup N] [Group E] [Group G] [Group Γ]

/-- The action of the pullback on the kernel is the original action read through the given
homomorphism. -/
theorem pullback_conjActHom (S : GroupExtension N E G) (ρ : Γ →* G) (γ : Γ) (n : N) :
    (S.pullback ρ).conjActHom γ n = S.conjActHom (ρ γ) n :=
  map_conjActHom (α := MonoidHom.id N) (ψ := S.pullbackFst ρ) (φ := ρ)
    (fun _ ↦ rfl) (rightHom_pullbackFst S ρ) γ n

/-- **The factor set of the pullback is the factor set of the original extension composed with the
given homomorphism**, up to a coboundary. -/
theorem exists_factorSet_pullback_eq (S : GroupExtension N E G) (ρ : Γ →* G)
    (σ : (S.pullback ρ).Section) (τ : S.Section) :
    ∃ c : Γ → N, ∀ g h : Γ,
      (S.pullback ρ).factorSet σ (g, h)
        = S.conjActHom (ρ g) (c h) / c (g * h) * c g * S.factorSet τ (ρ g, ρ h) := by
  simpa using exists_map_factorSet_eq (α := MonoidHom.id N) (ψ := S.pullbackFst ρ) (φ := ρ)
    (fun _ ↦ rfl) (rightHom_pullbackFst S ρ) σ τ

end AbelianKernel

section Obstruction

variable {N Γ : Type} {E G : Type*} [CommGroup N] [Group E] [Group G] [Group Γ]

/-- **An embedding problem with abelian kernel is solvable exactly when the cohomology class of
the pullback vanishes.** -/
theorem exists_lift_iff_cohomologyClass_pullback_eq_zero (S : GroupExtension N E G) (ρ : Γ →* G) :
    (letI := (S.pullback ρ).mulDistribMulAction; (S.pullback ρ).cohomologyClass = 0)
      ↔ ∃ f : Γ →* E, ∀ γ, S.rightHom (f γ) = ρ γ :=
  ((S.pullback ρ).cohomologyClass_eq_zero_iff).trans (nonempty_splitting_pullback_iff S ρ)

end Obstruction

end GroupExtension
