/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Ramification of the inertia generators

This module develops the ramification-theoretic facts about the inertia groups of a Galois extension
of Dedekind domains that are used by the branch-cycle inertia data: an element of the inertia group
at a prime `P` has order dividing the ramification index at `P`, hence (when that index divides a
common modulus `M`) dividing `M`.

The setting is an `AKLB`-style Galois action: a group `G` acting on a Dedekind domain `S` that is a
finite extension of a Dedekind domain `R`, with `G` the Galois group (`IsGaloisGroup G R S`).  For a
prime `P` of `S` over a nonzero prime `p` of `R` with separable residue extension, the inertia group
`P.inertia G` has cardinality equal to the ramification index `ramificationIdxIn p S`
(`Ideal.card_inertia_eq_ramificationIdxIn`).  Any inertia element therefore has order dividing that
index by Lagrange's theorem.

## Main results

* `mem_inertia_smul_iff` — the inertia group of `g • P` is the conjugate by `g` of the inertia
  group of `P`.
* `orderOf_dvd_ramificationIdxIn_of_mem_inertia` — an element of `P.inertia G` has order dividing
  `ramificationIdxIn p S`.
* `orderOf_dvd_of_mem_inertia_of_ramificationIdxIn_dvd` — if moreover the ramification index divides
  a modulus `M`, the inertia element's order divides `M`.
-/

namespace Rigidity.RET

open Ideal

section Transport

open Pointwise

variable {S G : Type*} [CommRing S] [Group G] [MulSemiringAction G S]

/-- Transport of the inertia subgroup under the pointwise Galois action on ideals: an element
`σ` lies in the inertia group of `g • P` iff its conjugate `g⁻¹ * σ * g` lies in the inertia
group of `P`.  Equivalently, `(g • P).inertia G` is the conjugate of `P.inertia G` by `g`. -/
theorem mem_inertia_smul_iff (g σ : G) (P : Ideal S) :
    σ ∈ (g • P).inertia G ↔ g⁻¹ * σ * g ∈ P.inertia G := by
  simp only [AddSubgroup.mem_inertia, Submodule.mem_toAddSubgroup]
  constructor
  · intro h z
    have := h (g • z)
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at this
    simpa [mul_smul, smul_sub] using this
  · intro h x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have := h (g⁻¹ • x)
    simpa [mul_smul, smul_sub] using this

end Transport

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [Module.IsTorsionFree R S]

/-- An element of the inertia group at `P` has order dividing the ramification index at `P`.

The inertia group `P.inertia G` has cardinality `ramificationIdxIn p S`
(`Ideal.card_inertia_eq_ramificationIdxIn`); the element's order divides the group's cardinality by
Lagrange's theorem. -/
theorem orderOf_dvd_ramificationIdxIn_of_mem_inertia
    (p : Ideal R) (hp : p ≠ ⊥) (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] {g : G} (hg : g ∈ P.inertia G) :
    orderOf g ∣ Ideal.ramificationIdxIn p S := by
  have h1 : orderOf g = orderOf (⟨g, hg⟩ : P.inertia G) := Subgroup.orderOf_coe ⟨g, hg⟩
  rw [h1, ← Ideal.card_inertia_eq_ramificationIdxIn (G := G) p hp P]
  exact orderOf_dvd_natCard _

/-- If an element lies in the inertia group at `P` and the ramification index at `P` divides a
modulus `M`, then the element's order divides `M`. -/
theorem orderOf_dvd_of_mem_inertia_of_ramificationIdxIn_dvd
    (p : Ideal R) (hp : p ≠ ⊥) (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] {g : G} (hg : g ∈ P.inertia G)
    {M : ℕ} (hM : Ideal.ramificationIdxIn p S ∣ M) :
    orderOf g ∣ M :=
  (orderOf_dvd_ramificationIdxIn_of_mem_inertia p hp P hg).trans hM

end Rigidity.RET
