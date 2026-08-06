/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The centerless extension lemma — the group-theoretic heart of the descent

This file proves, **axiom-free**, the purely group-theoretic core of the branch-cycle rationality
descent (`RET.Descent`): *"field of moduli = field of definition for centerless groups."*

Concretely: let `N ⊴ E` be a normal subgroup, `φ : N ↠ G` a surjection onto a **centerless**
group `G`, and suppose that for every `e : E` the automorphism of `N` given by conjugation by `e`,
transported through `φ`, is an **inner** automorphism of `G` (there is a `c : G` with
`φ(e n e⁻¹) = c · φ(n) · c⁻¹` for all `n ∈ N`).  Then `φ` extends to a surjection `ψ : E ↠ G`.

In the descent, `E = π₁^{arith}` (`Gal(Ω/ℚ(T))`), `N = π₁^{geom}` (`Gal(Ω/ℚ̄(T))`),
`φ : N ↠ G` is the geometric monodromy, and the inner-automorphism hypothesis is what
rationality + rigidity provide (via the branch-cycle formula and
`Rigidity.rigid_card_iff_single_orbit`).  The output `ψ : E ↠ G`, restricting to `φ` on `N`, is
the arithmetic monodromy whose fixed field is the regular `ℚ(T)`-extension.

## The mechanism

Centerlessness makes the twisting element `c` **unique** for each `e` (any two differ by a central
element, which is trivial).  Uniqueness then forces the assignment `e ↦ c` to be a homomorphism:
the twisting element for `e₁ · e₂` must be `c₁ · c₂` because that element witnesses the composite
conjugation.  This sidesteps all of the (absent-from-Mathlib) `H¹/H²` cohomology machinery: no
cocycle computation is needed, only the uniqueness that centerlessness buys.

## Main results

* `Rigidity.RET.extend_surjective_of_inner` — the centerless extension lemma.
-/

open scoped Pointwise

namespace Rigidity.RET

variable {E G : Type*} [Group E] [Group G]

/-- Conjugation of a normal subgroup element, packaged as an element of the subgroup: `n ↦ e n e⁻¹`.
This is the automorphism of `N` induced by conjugation by `e ∈ E`; it is the map whose transport
through the monodromy `φ` the extension lemma requires to be inner. -/
def conjN (N : Subgroup E) [N.Normal] (e : E) (n : N) : N :=
  ⟨e * (n : E) * e⁻¹, (inferInstance : N.Normal).conj_mem (n : E) n.2 e⟩

@[simp] lemma conjN_coe (N : Subgroup E) [N.Normal] (e : E) (n : N) :
    ((conjN N e n : N) : E) = e * (n : E) * e⁻¹ := rfl

/-- **Centerless extension lemma.**  Let `N ⊴ E`, let `φ : N ↠ G` be a surjection onto a
centerless group `G`, and suppose that for every `e : E` the automorphism of `N` given by
conjugation by `e`, transported through `φ`, is an *inner* automorphism of `G` (there is a `c : G`
with `φ(e n e⁻¹) = c · φ(n) · c⁻¹` for all `n ∈ N`).  Then `φ` extends to a surjection `ψ : E ↠ G`.

This is the group-theoretic heart of "field of moduli = field of definition for centerless
groups": centerless-ness makes the twisting element `c` unique for each `e`, and the resulting
assignment `e ↦ c` is automatically a homomorphism. -/
theorem extend_surjective_of_inner
    (N : Subgroup E) [N.Normal]
    (φ : N →* G) (hφ : Function.Surjective φ)
    (hZ : Subgroup.center G = ⊥)
    (hinner : ∀ e : E, ∃ c : G, ∀ n : N, φ (conjN N e n) = c * φ n * c⁻¹) :
    ∃ ψ : E →* G, Function.Surjective ψ ∧ ∀ n : N, ψ (n : E) = φ n := by
  -- Uniqueness of the twisting element, from centerlessness.
  have huniq : ∀ (e : E) (c c' : G),
      (∀ n : N, φ (conjN N e n) = c * φ n * c⁻¹) →
      (∀ n : N, φ (conjN N e n) = c' * φ n * c'⁻¹) → c = c' := by
    intro e c c' hc hc'
    -- `c'⁻¹ * c` commutes with every `φ n`, hence with all of `G` (φ surjective), hence central.
    have hcomm : ∀ n : N, (c'⁻¹ * c) * φ n = φ n * (c'⁻¹ * c) := by
      intro n
      have h := (hc n).symm.trans (hc' n)  -- c * φn * c⁻¹ = c' * φn * c'⁻¹
      have : c'⁻¹ * (c * φ n * c⁻¹) * c = c'⁻¹ * (c' * φ n * c'⁻¹) * c := by rw [h]
      simpa [mul_assoc] using this
    have hcenter : (c'⁻¹ * c) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨n, rfl⟩ := hφ g
      exact (hcomm n).symm
    rw [hZ, Subgroup.mem_bot] at hcenter
    exact (inv_mul_eq_one.mp hcenter).symm
  -- Choose the twisting element for each `e`.
  choose ψf hψf using hinner
  -- Characterisation: `ψf e` is THE element with the twisting property.
  have hchar : ∀ (e : E) (c : G),
      (∀ n : N, φ (conjN N e n) = c * φ n * c⁻¹) → c = ψf e :=
    fun e c hc => huniq e c (ψf e) hc (hψf e)
  -- `conjN` respects multiplication in `E`.
  have hconj_mul : ∀ (e₁ e₂ : E) (n : N), conjN N (e₁ * e₂) n = conjN N e₁ (conjN N e₂ n) := by
    intro e₁ e₂ n
    apply Subtype.ext
    simp only [conjN_coe]
    group
  -- `ψf` is multiplicative.
  have hmul : ∀ e₁ e₂ : E, ψf (e₁ * e₂) = ψf e₁ * ψf e₂ := by
    intro e₁ e₂
    refine (hchar (e₁ * e₂) (ψf e₁ * ψf e₂) ?_).symm
    intro n
    rw [hconj_mul, hψf e₁ (conjN N e₂ n), hψf e₂ n]
    group
  let ψ : E →* G := MonoidHom.mk' ψf hmul
  refine ⟨ψ, ?_, ?_⟩
  · -- surjective: `ψ` restricted to `N` is `φ`, which is surjective.
    intro g
    obtain ⟨n, rfl⟩ := hφ g
    refine ⟨(n : E), ?_⟩
    show ψf (n : E) = φ n
    refine (hchar (n : E) (φ n) ?_).symm
    intro m
    have : conjN N (n : E) m = n * m * n⁻¹ := by apply Subtype.ext; simp [conjN_coe]
    rw [this]
    simp [mul_assoc]
  · -- extends φ
    intro n
    show ψf (n : E) = φ n
    refine (hchar (n : E) (φ n) ?_).symm
    intro m
    have : conjN N (n : E) m = n * m * n⁻¹ := by apply Subtype.ext; simp [conjN_coe]
    rw [this]
    simp [mul_assoc]

end Rigidity.RET
