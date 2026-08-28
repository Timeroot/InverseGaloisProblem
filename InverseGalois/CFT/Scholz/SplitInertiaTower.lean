/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.InertiaFixedField
import InverseGalois.CFT.InertiaSurjective
import InverseGalois.CFT.Scholz.SplitInertiaAt

/-!
# Residue degree one along a tower

Residue degree one at a prime is a condition on a single field, but the Scholz–Reichardt
construction meets it in a tower: a solution of a central step lives over a field already known to
satisfy it, and the field the solution generates is a compositum.  Two transport principles carry
the condition through such a tower.

The first is the easy direction.  Residue degree is multiplicative in a tower, so a prime with
residue degree one upstairs has residue degree one in every subfield.  Conversely, when the field
below has residue degree one at the prime, the decomposition group upstairs is already contained in
the inertia subgroup together with the subgroup fixing the field below; so if the prime is totally
ramified in the top layer the condition is inherited upwards.

The second is the compositum.  A prime can have residue degree one in each of two fields and fail
to have it in their compositum, so nothing is available for free; what is true is that the failure
is measured in one factor at a time.  If a prime has residue degree one below and the inertia
subgroup of the compositum over the field below is already contained in one of the two factors,
then the residue degree of the compositum is the residue degree of the *other* factor.  This is the
form in which the Scholz–Reichardt residue correction reads the obstruction of a prime off the
quadratic layer that introduced it.

## Main results

* `InverseGalois.CFT.IsSplitInertiaAt.under` and `InverseGalois.CFT.IsSplitInertiaAt.mono`:
  **residue degree one passes to subfields.**
* `InverseGalois.CFT.stabilizer_le_inertia_sup_ker`: **over a field with residue degree one at a
  prime, the decomposition group is the inertia subgroup together with the subgroup fixing that
  field.**
* `InverseGalois.CFT.isSplitInertiaAt_of_ker_le_inertia`: **a prime totally ramified in the top
  layer of a tower has residue degree one upstairs as soon as it has it below.**
* `InverseGalois.CFT.isSplitInertiaAt_of_disjoint`: **the compositum transport**, in the form the
  residue correction uses it.
* `InverseGalois.CFT.ker_galRestrictLE_inf_ker_galRestrictLE`: an automorphism of a compositum
  fixing both factors is the identity.

## Tags

Scholz–Reichardt, residue degree, inertia subgroup, decomposition group, compositum, tower
-/

open NumberField InverseGalois.NumberTheory

open scoped Pointwise

set_option synthInstance.maxHeartbeats 1000000

set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

/-! ### A group-theoretic criterion -/

/-- **A subgroup caught between the inertia subgroup and two independent normal subgroups is the
inertia subgroup.**  Writing an element two ways, once modulo the first normal subgroup and once
modulo the second, the two remainders differ by an element of the inertia subgroup lying in the
product of the two normal subgroups, hence in the second one; so the first remainder is trivial. -/
theorem le_of_le_sup_of_le_sup {G : Type*} [Group G] {D I N₁ N₂ : Subgroup G} [N₁.Normal]
    [N₂.Normal] (hd : N₁ ⊓ N₂ = ⊥) (h₁ : D ≤ I ⊔ N₁) (h₂ : D ≤ I ⊔ N₂)
    (hI : I ⊓ (N₁ ⊔ N₂) ≤ N₂) :
    D ≤ I := by
  intro σ hσ
  have hmem₁ : σ ∈ (I : Set G) * (N₁ : Set G) := by
    rw [← Subgroup.mul_normal I N₁]
    exact h₁ hσ
  have hmem₂ : σ ∈ (I : Set G) * (N₂ : Set G) := by
    rw [← Subgroup.mul_normal I N₂]
    exact h₂ hσ
  obtain ⟨a, ha, b, hb, hab⟩ := hmem₁
  obtain ⟨c, hc, e, he, hce⟩ := hmem₂
  replace hab : a * b = σ := hab
  replace hce : c * e = σ := hce
  have hkey : c⁻¹ * a = e * b⁻¹ := by
    have hcab : c⁻¹ * (a * b) = e := by rw [hab, ← hce, inv_mul_cancel_left]
    rw [eq_mul_inv_iff_mul_eq, mul_assoc]
    exact hcab
  have hmemI : e * b⁻¹ ∈ I := hkey ▸ Subgroup.mul_mem I (Subgroup.inv_mem I hc) ha
  have hmemN : e * b⁻¹ ∈ N₁ ⊔ N₂ :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right he) (Subgroup.mem_sup_left (Subgroup.inv_mem _ hb))
  have hb₂ : b ∈ N₂ := by
    have h := hI ⟨hmemI, hmemN⟩
    have : b⁻¹ ∈ N₂ := by
      have := Subgroup.mul_mem N₂ (Subgroup.inv_mem N₂ he) h
      rwa [inv_mul_cancel_left] at this
    simpa using Subgroup.inv_mem N₂ this
  have hb1 : b = 1 := by
    have : b ∈ N₁ ⊓ N₂ := ⟨hb, hb₂⟩
    rw [hd] at this
    simpa using this
  rw [← hab, hb1, mul_one]
  exact ha

/-! ### Residue degree one passes to subfields -/

/-- **Residue degree one passes to a subfield.**  The residue degree of a prime is the product of
the residue degrees of the two layers of a tower, so it is one in the lower layer as soon as it is
one at the top. -/
theorem IsSplitInertiaAt.under {N : Type*} [Field N] [NumberField N] (F : IntermediateField ℚ N)
    [NumberField ↥F] {q : ℕ} (hq : q.Prime) (h : IsSplitInertiaAt N q) :
    IsSplitInertiaAt ↥F q := by
  intro Q hQprime hQover
  haveI : Fact q.Prime := ⟨hq⟩
  haveI := hQprime
  haveI := hQover
  obtain ⟨⟨P, hPp, hPo⟩⟩ := Q.nonempty_primesOver (S := 𝓞 N)
  haveI := hPp
  haveI := hPo
  have hQeq : Q = P.under (𝓞 ↥F) := hPo.over
  have hunder : (P.under (𝓞 ↥F)).under ℤ = Ideal.span {(q : ℤ)} := by
    rw [← hQeq]
    exact hQover.over.symm
  haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := ⟨by rw [← hunder, Ideal.under_under]⟩
  have hPbot : P ≠ ⊥ := ne_bot_of_liesOver_natCast hq inferInstance
  haveI : P.IsMaximal := isMaximal_of_ne_bot P hPbot
  have hUbot : P.under (𝓞 ↥F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 ↥F) hPbot
  haveI : (P.under (𝓞 ↥F)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hUbot
  have htower : (Ideal.span {(q : ℤ)}).inertiaDeg P =
      (Ideal.span {(q : ℤ)}).inertiaDeg (P.under (𝓞 ↥F)) * (P.under (𝓞 ↥F)).inertiaDeg P :=
    Ideal.inertiaDeg_algebra_tower (Ideal.span {(q : ℤ)}) (P.under (𝓞 ↥F)) P
  have h1 : (Ideal.span {(q : ℤ)}).inertiaDeg P = 1 := h P inferInstance inferInstance
  rw [hQeq]
  refine Nat.dvd_one.mp ⟨(P.under (𝓞 ↥F)).inertiaDeg P, ?_⟩
  rw [← htower, h1]

section Tower

variable {A B L : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A] [IsGalois ℚ ↥A]
  [NumberField ↥B] [IsGalois ℚ ↥B] [NumberField ↥L] [IsGalois ℚ ↥L] {q : ℕ}

omit [IsGalois ℚ ↥A] [IsGalois ℚ ↥L] in
/-- **Residue degree one passes to a smaller intermediate field.** -/
theorem IsSplitInertiaAt.mono (hAL : A ≤ L) (hq : q.Prime) (h : IsSplitInertiaAt ↥L q) :
    IsSplitInertiaAt ↥A q := by
  haveI : NumberField ↥(IntermediateField.restrict hAL) := ⟨⟩
  exact IsSplitInertiaAt.of_ringEquiv hq
    (IntermediateField.restrict_algEquiv hAL).symm.toRingEquiv
    (IsSplitInertiaAt.under (IntermediateField.restrict hAL) hq h)

/-- **Over a field with residue degree one at a prime, the decomposition group of a prime above it
is the inertia subgroup together with the subgroup fixing that field.**  Restriction carries the
decomposition group into the decomposition group below and the inertia subgroup *onto* the inertia
subgroup below, and the two coincide below. -/
theorem stabilizer_le_inertia_sup_ker (hAL : A ≤ L) (hq : q.Prime) (h : IsSplitInertiaAt ↥A q)
    (P : Ideal (𝓞 ↥L)) [P.IsPrime] [P.LiesOver (Ideal.span {(q : ℤ)})] :
    MulAction.stabilizer Gal(↥L/ℚ) P ≤
      Ideal.inertia Gal(↥L/ℚ) P ⊔ (galRestrictLE hAL).ker := by
  haveI : NumberField ↥(IntermediateField.restrict hAL) := ⟨⟩
  haveI : IsGalois ℚ ↥(IntermediateField.restrict hAL) := ⟨⟩
  haveI := liesOver_under_intermediateField (p := q) (IntermediateField.restrict hAL) P
  refine le_sup_ker_of_map_le ?_
  have hmapeq : ∀ X : Subgroup Gal(↥L/ℚ), X.map (galRestrictLE hAL) =
      (X.map (AlgEquiv.restrictNormalHom ↥(IntermediateField.restrict hAL))).map
        (AlgEquiv.autCongr
          (IntermediateField.restrict_algEquiv hAL)).symm.toMonoidHom := fun X => by
    rw [Subgroup.map_map]
    rfl
  rw [hmapeq, hmapeq]
  refine Subgroup.map_mono ?_
  rw [map_inertia_eq_inertia (IntermediateField.restrict hAL) hq P]
  have hsplitF : IsSplitInertiaAt ↥(IntermediateField.restrict hAL) q :=
    IsSplitInertiaAt.of_ringEquiv hq (IntermediateField.restrict_algEquiv hAL).toRingEquiv h
  rw [(inertiaDeg_eq_one_iff_inertia_eq_stabilizer (K := ↥(IntermediateField.restrict hAL)) hq
    (P.under (𝓞 ↥(IntermediateField.restrict hAL)))).mp (hsplitF _ inferInstance inferInstance)]
  rintro - ⟨σ, hσ, rfl⟩
  exact restrictNormal_mem_stabilizer (IntermediateField.restrict hAL) P hσ

/-- **A prime totally ramified in the top layer of a tower has residue degree one upstairs as soon
as it has it below.**  The decomposition group is the inertia subgroup together with the subgroup
fixing the field below, and the latter is already inside the inertia subgroup. -/
theorem isSplitInertiaAt_of_ker_le_inertia (hAL : A ≤ L) (hq : q.Prime)
    (h : IsSplitInertiaAt ↥A q) (P : Ideal (𝓞 ↥L)) [P.IsPrime]
    [hPo : P.LiesOver (Ideal.span {(q : ℤ)})]
    (hker : (galRestrictLE hAL).ker ≤ Ideal.inertia Gal(↥L/ℚ) P) :
    IsSplitInertiaAt ↥L q :=
  isSplitInertiaAt_of_stabilizer_le hq P hPo
    ((stabilizer_le_inertia_sup_ker hAL hq h P).trans (sup_le le_rfl hker))

/-- **The compositum transport.**  A prime with residue degree one in each of two fields whose
compositum is the whole top field has residue degree one there, provided the inertia subgroup meets
the subgroup fixing the two fields only inside the second of them: the two ways of writing a
decomposition-group element then differ by an element that is forced to be trivial. -/
theorem isSplitInertiaAt_of_disjoint (hA : A ≤ L) (hB : B ≤ L) (hq : q.Prime)
    (hsA : IsSplitInertiaAt ↥A q) (hsB : IsSplitInertiaAt ↥B q) (P : Ideal (𝓞 ↥L)) [P.IsPrime]
    [hPo : P.LiesOver (Ideal.span {(q : ℤ)})]
    (hdisj : (galRestrictLE hA).ker ⊓ (galRestrictLE hB).ker = ⊥)
    (hinf : Ideal.inertia Gal(↥L/ℚ) P ⊓ ((galRestrictLE hA).ker ⊔ (galRestrictLE hB).ker) ≤
      (galRestrictLE hB).ker) :
    IsSplitInertiaAt ↥L q :=
  isSplitInertiaAt_of_stabilizer_le hq P hPo
    (le_of_le_sup_of_le_sup hdisj (stabilizer_le_inertia_sup_ker hA hq hsA P)
      (stabilizer_le_inertia_sup_ker hB hq hsB P) hinf)

end Tower

/-! ### An automorphism of a compositum fixing both factors -/

/-- **An automorphism of a compositum restricting trivially to both factors is the identity.** -/
theorem ker_galRestrictLE_inf_ker_galRestrictLE {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A B : IntermediateField F E) [Normal F ↥A] [Normal F ↥B] :
    (galRestrictLE (le_sup_left : A ≤ A ⊔ B)).ker ⊓
      (galRestrictLE (le_sup_right : B ≤ A ⊔ B)).ker = ⊥ := by
  refine eq_bot_iff.mpr fun σ hσ => ?_
  have h : galRestrictProd A B σ = 1 :=
    Prod.ext (MonoidHom.mem_ker.mp hσ.1) (MonoidHom.mem_ker.mp hσ.2)
  simpa using galRestrictProd_injective A B (by simpa using h)

end InverseGalois.CFT
