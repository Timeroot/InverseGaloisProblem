/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.EmbeddingObstruction
import InverseGalois.CFT.Profinite.FixingSubgroup
import InverseGalois.CFT.Profinite.Hilbert90
import InverseGalois.CFT.Profinite.KummerLocal

/-!
# Extracting a root of a character of a closed subgroup

A closed subgroup of the Galois group of an extension is the group fixing its own fixed field, and
the extension is Galois over that field as well, so everything proved for a Galois group holds for
the subgroup once the correspondence is transported across.  The transport is smooth in both
directions, which is exactly what a statement about smooth cochains needs, so **Hilbert's theorem
ninety holds for a closed subgroup**: a smooth one cocycle of it with values in the units of the
extension is the coboundary of a single unit.

What that buys is the extraction of roots of characters.  Let a closed subgroup carry a smooth
character with values in the units, killed by one number, and suppose the extension has an
algebraically closed field of coefficients and that the roots of unity of a multiple of that number
are fixed by the subgroup.  The character is then a one cocycle, because its values are fixed, so
it is the coboundary of a unit; a root of that unit of the complementary order is available because
the field is algebraically closed, and the coboundary of the root is a character whose power of
that order is the character one started with.  The root character is smooth for a reason owing
nothing to the character it came from: its kernel contains the automorphisms fixing the field the
root generates, which is finite over the base, so the kernel is open.

The number the character is killed by never enters the construction alone — what is needed is that
the roots of unity of the product are fixed, which over a number field carrying them is a condition
on the base field and not on the subgroup.  **So a character of prime-power order lifts as far as
the base field carries roots of unity**, and no local class field theory is spent on the way.

## Main definitions

* `InverseGalois.CFT.closedSubgroupEquiv` — the Galois group over the fixed field of a closed
  subgroup, read as the subgroup.

## Main results

* `InverseGalois.CFT.isMulCoboundary₁_of_isMulCocycle₁_smooth_subgroup` — **Hilbert's theorem
  ninety for a closed subgroup of a Galois group.**
* `InverseGalois.CFT.exists_smoothHom_pow_eq` — **a smooth character of a closed subgroup has a
  smooth root of any order**, as soon as the roots of unity of the product of the two orders are
  fixed by the subgroup.

## Tags

infinite Galois theory, Krull topology, Hilbert's theorem 90, Kummer theory, character, root of
unity
-/

namespace InverseGalois.CFT

open IntermediateField groupCohomology

/-! ### Hilbert's theorem ninety for a closed subgroup -/

section Hilbert90Sub

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- The Galois group over the fixed field of a closed subgroup, read as the subgroup. -/
noncomputable def closedSubgroupEquiv {A : Subgroup Gal(Ω/k)}
    (hA : IsClosed (A : Set Gal(Ω/k))) : Gal(Ω/↥(IntermediateField.fixedField A)) ≃* ↥A :=
  (fixingSubgroupEquiv (IntermediateField.fixedField A)).symm.trans
    (MulEquiv.subgroupCongr (fixingSubgroup_fixedField_of_isClosed hA))

/-- Reading an automorphism over the fixed field as one of the subgroup does not change it. -/
theorem coe_closedSubgroupEquiv {A : Subgroup Gal(Ω/k)} (hA : IsClosed (A : Set Gal(Ω/k)))
    (τ : Gal(Ω/↥(IntermediateField.fixedField A))) (x : Ω) :
    ((closedSubgroupEquiv hA τ : Gal(Ω/k))) x = τ x := rfl

/-- **The correspondence between a closed subgroup and the Galois group over its fixed field is
continuous.** -/
theorem continuous_closedSubgroupEquiv {A : Subgroup Gal(Ω/k)}
    (hA : IsClosed (A : Set Gal(Ω/k))) : Continuous (closedSubgroupEquiv hA) :=
  (continuous_galSubHom (IntermediateField.fixedField A)).subtype_mk _

/-- **Hilbert's theorem ninety for a closed subgroup of a Galois group**: a smooth one cocycle of a
closed subgroup, with values in the units of the extension, is the coboundary of a single unit.

The subgroup is the group fixing its own fixed field, over which the extension is again Galois, and
the correspondence carrying one to the other is continuous, so a smooth cocycle of the subgroup is
a smooth cocycle of that Galois group. -/
theorem isMulCoboundary₁_of_isMulCocycle₁_smooth_subgroup {A : Subgroup Gal(Ω/k)}
    (hA : IsClosed (A : Set Gal(Ω/k))) {u : ↥A → Ωˣ} (hu : IsMulCocycle₁ u)
    (hs : IsSmooth₁ u) : IsMulCoboundary₁ u := by
  set F := IntermediateField.fixedField A with hFdef
  haveI : IsGalois ↥F Ω := IsGalois.tower_top_of_isGalois k ↥F Ω
  set ψ := closedSubgroupEquiv hA with hψdef
  have hsmul : ∀ (τ : Gal(Ω/↥F)) (w : Ωˣ), (ψ τ) • w = τ • w := fun τ w =>
    Units.ext (coe_closedSubgroupEquiv hA τ (w : Ω))
  have hv : IsMulCocycle₁ fun τ : Gal(Ω/↥F) => u (ψ τ) := by
    intro σ τ
    have h := hu (ψ σ) (ψ τ)
    rw [← _root_.map_mul ψ σ τ] at h
    show u (ψ (σ * τ)) = σ • u (ψ τ) * u (ψ σ)
    rw [h, hsmul]
  have hvs : IsSmooth₁ fun τ : Gal(Ω/↥F) => u (ψ τ) :=
    isSmooth₁_comp (f := ψ.toMonoidHom) (continuous_closedSubgroupEquiv hA) hs
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_smooth hv hvs
  refine ⟨β, fun σ => ?_⟩
  have h := hβ (ψ.symm σ)
  rw [← hsmul (ψ.symm σ) β] at h
  simpa using h

end Hilbert90Sub

/-! ### Roots of a character -/

section CharacterRoot

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] [IsAlgClosed Ω]

/-- **A smooth character of a closed subgroup has a smooth root of any order**, as soon as the
roots of unity of the product of the two orders are fixed by the subgroup.

The values of the character are roots of unity of the product, hence fixed, so the character is a
one cocycle and Hilbert's theorem ninety makes it the coboundary of a unit.  A root of that unit of
the wanted order exists because the field is algebraically closed, and the coboundary of the root
is the character wanted: its values are again roots of unity of the product, because the power of
the unit by the order of the original character is fixed by the subgroup, so the coboundary of the
root is a homomorphism, and it is smooth because its kernel contains the automorphisms fixing the
field the root generates over the base, a finite extension. -/
theorem exists_smoothHom_pow_eq {A : Subgroup Gal(Ω/k)} (hA : IsClosed (A : Set Gal(Ω/k)))
    {n d : ℕ} (hd : 0 < d) (χ : ↥A →* Ωˣ) (hχs : IsSmooth₁ (χ : ↥A → Ωˣ))
    (hχn : ∀ σ, χ σ ^ n = 1)
    (hμ : ∀ ζ : Ωˣ, ζ ^ (n * d) = 1 → ∀ σ : ↥A, σ • ζ = ζ) :
    ∃ χ' : ↥A →* Ωˣ, IsSmooth₁ (χ' : ↥A → Ωˣ) ∧ (∀ σ, χ' σ ^ d = χ σ) ∧
      ∀ σ, χ' σ ^ (n * d) = 1 := by
  have hfix : ∀ σ τ : ↥A, σ • χ τ = χ τ := fun σ τ =>
    hμ (χ τ) (by rw [pow_mul, hχn, one_pow]) σ
  have hcoc : IsMulCocycle₁ (χ : ↥A → Ωˣ) := fun σ τ => by
    rw [_root_.map_mul, hfix, mul_comm]
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_smooth_subgroup hA hcoc hχs
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (β : Ω) hd
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne'] at hy
    exact β.ne_zero hy.symm
  set γ : Ωˣ := Units.mk0 y hy0 with hγ
  have hγd : γ ^ d = β := Units.ext (by simpa [hγ] using hy)
  have hβn : ∀ σ : ↥A, σ • β ^ n = β ^ n := by
    intro σ
    have h := hβ σ
    rw [div_eq_iff_eq_mul] at h
    rw [smul_pow', h, mul_pow, hχn, one_mul]
  have hval : ∀ σ : ↥A, (σ • γ / γ) ^ (n * d) = 1 := by
    intro σ
    rw [div_pow, ← smul_pow', mul_comm n d, pow_mul, hγd, hβn σ, div_self']
  have hhom : ∀ σ τ : ↥A, (σ * τ) • γ / γ = (σ • γ / γ) * (τ • γ / γ) := by
    intro σ τ
    have hfixτ : σ • (τ • γ / γ) = τ • γ / γ := hμ _ (hval τ) σ
    rw [smul_div'] at hfixτ
    rw [mul_smul]
    calc σ • τ • γ / γ = (σ • τ • γ / σ • γ) * (σ • γ / γ) := by
          rw [div_mul_div_cancel]
      _ = (τ • γ / γ) * (σ • γ / γ) := by rw [hfixτ]
      _ = (σ • γ / γ) * (τ • γ / γ) := mul_comm _ _
  set χ' : ↥A →* Ωˣ := MonoidHom.mk' (fun σ => σ • γ / γ) hhom with hχ'
  have hχ'apply : ∀ σ : ↥A, χ' σ = σ • γ / γ := fun _ => rfl
  refine ⟨χ', ?_, fun σ => ?_, fun σ => by rw [hχ'apply]; exact hval σ⟩
  · refine isSmooth₁_of_isOpenNormal_ker ⟨inferInstance, ?_⟩
    haveI : FiniteDimensional k ↥k⟮y⟯ :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
    have hop : IsOpen (((k⟮y⟯ : IntermediateField k Ω).fixingSubgroup).subgroupOf A : Set ↥A) := by
      rw [Subgroup.coe_subgroupOf]
      exact (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val
    refine Subgroup.isOpen_mono (fun σ hσ => ?_) hop
    rw [MonoidHom.mem_ker, hχ'apply, div_eq_one]
    refine Units.ext ?_
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_subgroupOf.1 hσ) y
      (IntermediateField.mem_adjoin_simple_self k y)
  · rw [hχ'apply, div_pow, ← smul_pow', hγd, hβ σ]

end CharacterRoot

end InverseGalois.CFT
