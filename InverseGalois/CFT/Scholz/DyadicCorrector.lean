/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.DyadicInertiaChar
import InverseGalois.CFT.Kummer.QuadraticChar
import InverseGalois.CFT.Kummer.QuadraticGenerator
import InverseGalois.CFT.Scholz.DecompositionLift
import InverseGalois.CFT.Scholz.FixedFieldRamification
import InverseGalois.CFT.Scholz.FrattiniInertia
import InverseGalois.CFT.Scholz.FrattiniInertiaSmall
import InverseGalois.CFT.Scholz.RamificationControl

/-!
# The correcting character at two

A solution of a central embedding problem with kernel of order two which is unramified at two takes
values in the kernel on the inertia subgroup at a prime above two.  If the residue degree there is
divisible by the order of the group, that restriction extends to a character of the whole
decomposition group with values in the kernel, and over the fixed field of the decomposition group
a character with two values is cut out by a square root.

The prime below that fixed field is unramified of residue degree one over two, because the
decomposition group is the whole subgroup being fixed.  So if the eighth roots of unity are
available the square root agrees, on the inertia subgroup, with a square root of one of
`1, -1, 2, -2`; the quadratic character of that rational square root is ramified only at two, and it
cancels the solution on the inertia subgroup at two.  That is exactly the correcting character the
twisting step of the Scholz–Reichardt construction consumes at the prime two.

## Main results

* `InverseGalois.CFT.exists_ne_one_of_card_eq_two`: a subgroup of order two has a unique nontrivial
  element, and that element is an involution.
* `InverseGalois.CFT.hasCorrectingCharAt_two`: **a solution of a central embedding problem with
  kernel of order two is corrected at two by the quadratic character of a rational square root**, as
  soon as the residue degree at a prime above two is divisible by the order of the group and the
  field contains the eighth roots of unity.

## Tags

embedding problem, correcting character, quadratic character, inertia, dyadic place, square class,
Scholz-Reichardt
-/

namespace InverseGalois.CFT

open IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

/-! ### A subgroup of order two -/

/-- **A subgroup of order two has a unique nontrivial element, and that element is an
involution.** -/
theorem exists_ne_one_of_card_eq_two {G : Type*} [Group G] {K : Subgroup G}
    (hK : Nat.card ↥K = 2) :
    ∃ z, z ∈ K ∧ z ≠ 1 ∧ z ^ 2 = 1 ∧ ∀ x ∈ K, x ≠ 1 → x = z := by
  obtain ⟨w, hwne, hw⟩ := (Nat.card_eq_two_iff' (1 : ↥K)).mp hK
  have huniq : ∀ x ∈ K, x ≠ 1 → x = (w : G) := fun x hx hx1 =>
    congrArg Subtype.val (hw ⟨x, hx⟩ fun h => hx1 (congrArg Subtype.val h))
  have hzne : (w : G) ≠ 1 := fun h => hwne (Subtype.ext h)
  have hinv : ((w : G))⁻¹ = (w : G) :=
    huniq _ (inv_mem w.2) fun h => hzne (by rw [← inv_inv (w : G), h, inv_one])
  refine ⟨(w : G), w.2, hzne, ?_, huniq⟩
  rw [sq]
  exact mul_eq_one_iff_inv_eq.mpr hinv

/-! ### The correcting character -/

variable {M : Type} [Field M] [NumberField M] [IsGalois ℚ M]
variable {G H : Type*} [Group G] [Finite G] [Group H]

set_option maxHeartbeats 400000 in
/-- **A solution of a central embedding problem with kernel of order two is corrected at two by the
quadratic character of a rational square root.**  The solution extends from the inertia subgroup at
a prime above two to the whole decomposition group, because the residue degree there is large; over
the fixed field of the decomposition group the extension is cut out by a square root, and the place
below is unramified of residue degree one, so that square root agrees on inertia with a square root
of one of `1, -1, 2, -2`.  The quadratic character of the latter is ramified only at two and
cancels the solution there. -/
theorem hasCorrectingCharAt_two {f : G →* H} (hZ : f.ker ≤ Subgroup.center G)
    (hcard : Nat.card ↥f.ker = 2) (hi : ∃ i : M, i ^ 2 = -1) (hr : ∃ r : M, r ^ 2 = 2)
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver (Ideal.span {((2 : ℕ) : ℤ)})]
    (hdvd : Nat.card G ∣ (Ideal.span {((2 : ℕ) : ℤ)}).inertiaDeg P)
    {θ : Gal(M/ℚ) →* G} (hI : ∀ σ ∈ Ideal.inertia Gal(M/ℚ) P, θ σ ∈ f.ker) :
    HasCorrectingCharAt M f 2 θ := by
  classical
  obtain ⟨z, hzK, hz1, hz2, huniq⟩ := exists_ne_one_of_card_eq_two hcard
  -- the solution extends from the inertia subgroup to the decomposition group
  obtain ⟨μ, hμrange, hμeq⟩ :=
    exists_monoidHom_stabilizer_eqOn_inertia Nat.prime_two P hZ hI
      (by rw [card_quotient_inertia_eq_inertiaDeg Nat.prime_two P]; exact hdvd)
  haveI : NumberField ↥(fixedField (stabilizer Gal(M/ℚ) P)) := ⟨⟩
  haveI : IsGalois ↥(fixedField (stabilizer Gal(M/ℚ) P)) M :=
    IsGalois.tower_top_of_isGalois ℚ _ M
  -- the extension, read as a character over the fixed field of the decomposition group
  obtain ⟨ν, hνdef⟩ : ∃ ν : Gal(M/↥(fixedField (stabilizer Gal(M/ℚ) P))) →* G,
      ∀ σ', ν σ' = μ ((subgroupEquivAlgEquiv (stabilizer Gal(M/ℚ) P)).symm σ') :=
    ⟨μ.comp (subgroupEquivAlgEquiv (stabilizer Gal(M/ℚ) P)).symm.toMonoidHom, fun _ => rfl⟩
  have hνker : ∀ σ', ν σ' ∈ f.ker := fun σ' => by rw [hνdef]; exact hμrange ⟨_, rfl⟩
  have hfh : ∀ (σ : Gal(M/ℚ)) (hσD : σ ∈ stabilizer Gal(M/ℚ) P),
      fixedFieldHom (stabilizer Gal(M/ℚ) P)
        (subgroupEquivAlgEquiv (stabilizer Gal(M/ℚ) P) ⟨σ, hσD⟩) = σ := by
    intro σ hσD
    show ((subgroupEquivAlgEquiv (stabilizer Gal(M/ℚ) P)).symm
      (subgroupEquivAlgEquiv (stabilizer Gal(M/ℚ) P) ⟨σ, hσD⟩) : Gal(M/ℚ)) = σ
    rw [MulEquiv.symm_apply_apply]
  have hact : ∀ (σ : Gal(M/ℚ)) (hσD : σ ∈ stabilizer Gal(M/ℚ) P) (x : M),
      subgroupEquivAlgEquiv (stabilizer Gal(M/ℚ) P) ⟨σ, hσD⟩ x = σ x := by
    intro σ hσD x
    rw [← fixedFieldHom_apply (stabilizer Gal(M/ℚ) P)
      (subgroupEquivAlgEquiv (stabilizer Gal(M/ℚ) P) ⟨σ, hσD⟩) x, hfh]
  have hinert : ∀ (σ : Gal(M/ℚ)) (hσD : σ ∈ stabilizer Gal(M/ℚ) P),
      σ ∈ Ideal.inertia Gal(M/ℚ) P →
        subgroupEquivAlgEquiv (stabilizer Gal(M/ℚ) P) ⟨σ, hσD⟩ ∈
          Ideal.inertia Gal(M/↥(fixedField (stabilizer Gal(M/ℚ) P))) P := by
    intro σ hσD hσ
    refine mem_inertia_fixedFieldHom (stabilizer Gal(M/ℚ) P) P ?_
    rw [hfh]
    exact hσ
  have hνθ : ∀ (σ : Gal(M/ℚ)) (hσD : σ ∈ stabilizer Gal(M/ℚ) P),
      σ ∈ Ideal.inertia Gal(M/ℚ) P →
        ν (subgroupEquivAlgEquiv (stabilizer Gal(M/ℚ) P) ⟨σ, hσD⟩) = θ σ := by
    intro σ hσD hσ
    rw [hνdef, MulEquiv.symm_apply_apply]
    exact hμeq ⟨σ, hσD⟩ hσ
  by_cases htriv : ∀ σ', ν σ' = 1
  · -- the solution is already trivial on the inertia subgroup at two
    have hθ1 : ∀ σ ∈ Ideal.inertia Gal(M/ℚ) P, θ σ = 1 := by
      intro σ hσ
      rw [← hνθ σ (Ideal.inertia_le_stabilizer P hσ) hσ]
      exact htriv _
    refine ⟨1, P, inferInstance, inferInstance, ?_, ?_, 0, ?_⟩
    · rintro _ ⟨σ, rfl⟩
      exact Subgroup.one_mem _
    · intro q _ _ Q _ _ σ _
      rfl
    · intro σ hσ
      rw [hθ1 σ hσ, zpow_zero, one_mul]
  -- the character is nontrivial, so it is cut out by a square root
  push_neg at htriv
  obtain ⟨τ, hτ⟩ := htriv
  have h2val : ∀ σ', ν σ' = 1 ∨ ν σ' = ν τ := by
    intro σ'
    by_cases h : ν σ' = 1
    · exact Or.inl h
    · exact Or.inr ((huniq _ (hνker σ') h).trans (huniq _ (hνker τ) hτ).symm)
  obtain ⟨y, hy0, ⟨β, hβ⟩, hyfix⟩ := exists_sq_algebraMap_eq_iff_mem_ker hτ h2val
  -- the square root of a rational number agreeing with it on the inertia subgroup at two
  have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_natCast Nat.prime_two inferInstance
  obtain ⟨W, hWa⟩ : ∃ W : HeightOneSpectrum (𝓞 M), W.asIdeal = P :=
    ⟨⟨P, inferInstance, hP0⟩, rfl⟩
  haveI : ((primeUnder (𝓞 ↥(fixedField (stabilizer Gal(M/ℚ) P))) W).asIdeal).LiesOver
      (Ideal.span {((2 : ℕ) : ℤ)}) := by
    rw [primeUnder_asIdeal, hWa]
    exact liesOver_under_intermediateField (p := 2) (fixedField (stabilizer Gal(M/ℚ) P)) P
  obtain ⟨he1, hf1⟩ :=
    ramificationIdx_eq_one_of_stabilizer_le (stabilizer Gal(M/ℚ) P) Nat.prime_two P le_rfl
  obtain ⟨δ, hδ0, hδsq, hδeq⟩ :=
    exists_sq_intCast_eqOn_inertia (Z := ↥(fixedField (stabilizer Gal(M/ℚ) P))) W
      (by rw [primeUnder_asIdeal, hWa]; exact he1) (by rw [primeUnder_asIdeal, hWa]; exact hf1)
      hi hr hy0 hβ
  rw [hWa] at hδeq
  obtain ⟨d, hd, hδd⟩ : ∃ d : ℤ, (d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2) ∧ δ ^ 2 = (d : M) := by
    rcases hδsq with h | h | h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
    · exact ⟨-1, Or.inr (Or.inl rfl), by rw [h]; norm_num⟩
    · exact ⟨2, Or.inr (Or.inr (Or.inl rfl)), by rw [h]; norm_num⟩
    · exact ⟨-2, Or.inr (Or.inr (Or.inr rfl)), by rw [h]; norm_num⟩
  have hsqδ : ∀ σ : Gal(M/ℚ), σ δ = δ ∨ σ δ = -δ := eq_or_eq_neg_of_sq_intCast hδd
  have hnegδ : -δ ≠ δ := by
    intro h
    have h2 : (2 : M) * δ = 0 := by linear_combination -h
    exact hδ0 ((mul_eq_zero.mp h2).resolve_left two_ne_zero)
  refine ⟨sqrtChar δ hz2 hsqδ hδ0, P, inferInstance, inferInstance,
    sqrtChar_range_le hz2 hsqδ hδ0 hzK, ?_, -1, ?_⟩
  · -- the character is trivial on the inertia subgroup at every other prime
    intro q hq hq2 Q hQp hQo σ hσ
    haveI := hQp
    haveI := hQo
    have hQ0 : Q ≠ ⊥ := ne_bot_of_liesOver_natCast hq hQo
    have h2Q : (2 : 𝓞 M) ∉ Q := by
      intro hmem
      have hcomap : ((2 : ℤ)) ∈ Q.under ℤ := by
        show algebraMap ℤ (𝓞 M) (2 : ℤ) ∈ Q
        simpa using hmem
      have hover : Ideal.span {((q : ℕ) : ℤ)} = Q.under ℤ := Ideal.LiesOver.over
      rw [← hover, Ideal.mem_span_singleton] at hcomap
      have hqd : q ∣ 2 := by exact_mod_cast hcomap
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hqd)
    exact sqrtChar_eq_one_of_mem_inertia hz2 hsqδ hδ0 hd hδd (w := ⟨Q, hQp, hQ0⟩) h2Q hσ
  · -- the character cancels the solution on the inertia subgroup at two
    intro σ hσ
    have hσD : σ ∈ stabilizer Gal(M/ℚ) P := Ideal.inertia_le_stabilizer P hσ
    obtain ⟨σ', hσ'ν, hσ'act, hσ'inert⟩ :
        ∃ σ' : Gal(M/↥(fixedField (stabilizer Gal(M/ℚ) P))), ν σ' = θ σ ∧
          (∀ x : M, σ' x = σ x) ∧
            σ' ∈ Ideal.inertia Gal(M/↥(fixedField (stabilizer Gal(M/ℚ) P))) P :=
      ⟨subgroupEquivAlgEquiv (stabilizer Gal(M/ℚ) P) ⟨σ, hσD⟩, hνθ σ hσD hσ, hact σ hσD,
        hinert σ hσD hσ⟩
    have hkey : θ σ = sqrtChar δ hz2 hsqδ hδ0 σ := by
      have hyd : σ y * δ = y * σ δ :=
        (congrArg (· * δ) (hσ'act y)).symm.trans
          ((hδeq σ' hσ'inert).trans (congrArg (y * ·) (hσ'act δ)))
      rcases hsqδ σ with hfix | hfix
      · have hyy : σ y = y := mul_right_cancel₀ hδ0 (hyd.trans (congrArg (y * ·) hfix))
        have hν1 : ν σ' = 1 := MonoidHom.mem_ker.mp ((hyfix σ').mp ((hσ'act y).trans hyy))
        exact hσ'ν.symm.trans (hν1.trans (sqrtChar_eq_one hz2 hsqδ hδ0 hfix).symm)
      · have hyd2 : σ y * δ = y * -δ := hyd.trans (congrArg (y * ·) hfix)
        have hyy : σ y ≠ y := by
          intro h
          rw [h] at hyd2
          have h2 : (2 : M) * (y * δ) = 0 := by linear_combination hyd2
          rcases mul_eq_zero.mp h2 with h3 | h3
          · exact two_ne_zero h3
          · rcases mul_eq_zero.mp h3 with h4 | h4
            · exact hy0 h4
            · exact hδ0 h4
        have hν1 : ν σ' ≠ 1 := fun h =>
          hyy ((hσ'act y).symm.trans ((hyfix σ').mpr (MonoidHom.mem_ker.mpr h)))
        have hne : ¬ σ δ = δ := by rw [hfix]; exact hnegδ
        exact hσ'ν.symm.trans ((huniq _ (hνker σ') hν1).trans
          ((sqrtChar_apply hz2 hsqδ hδ0 σ).trans (if_neg hne)).symm)
    rw [hkey, zpow_neg_one, mul_inv_cancel]

end InverseGalois.CFT
