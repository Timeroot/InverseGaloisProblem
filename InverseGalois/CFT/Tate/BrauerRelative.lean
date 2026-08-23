/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.GaloisH0
import InverseGalois.CFT.Brauer.CyclicNorm

/-!
# The relative Brauer group of a cyclic extension is a Tate group

For a finite cyclic Galois extension `L / K` the two towers built so far describe the same
subquotient of the units of the base field.

On the Brauer side, the cyclic algebra construction is a homomorphism from `Kˣ` onto the relative
Brauer group whose kernel is the group of norms.  On the cohomological side, the zeroth Tate group
of `Lˣ` is the units of the base field modulo the norms.  Both are therefore `Kˣ / N Lˣ`, and
comparing them identifies `Br(L / K)` with `Ĥ⁰(Lˣ)`.

Counting, the order of the relative Brauer group is the norm index `[Kˣ : N Lˣ]`, and since
Hilbert's theorem 90 makes the lower Tate group trivial, the Herbrand quotient of the unit group
of a cyclic extension is the order of its relative Brauer group.

## Main definitions

* `InverseGalois.CFT.brauerRelativeTateEquiv`: the isomorphism between the relative Brauer group
  and the zeroth Tate group of the unit group.

## Main results

* `InverseGalois.CFT.card_brauerRelative_eq_index_normSubgroup`: **the order of `Br(L / K)` is the
  norm index.**
* `InverseGalois.CFT.herbrand_units_eq_card_brauerRelative`: **the Herbrand quotient of the unit
  group is the order of the relative Brauer group.**

## Tags

Brauer group, cyclic algebra, Tate cohomology, norm index
-/

namespace InverseGalois.CFT

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {σ₀ : L ≃ₐ[K] L} (hσ₀ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ₀)

/-! ### The order of the relative Brauer group -/

include hσ₀ in
/-- **The order of the relative Brauer group of a cyclic extension is the norm index.** -/
theorem card_brauerRelative_eq_index_normSubgroup :
    Nat.card ↥(BrauerGroup.relative K L) = (normSubgroup K L).index := by
  rw [Subgroup.index_eq_card]
  exact (Nat.card_congr (cyclicBrauerEquiv hσ₀).toEquiv).symm

/-! ### Comparison with the Tate group -/

theorem toAdditive_cyclicBrauerHomRelative_surjective :
    Function.Surjective (MonoidHom.toAdditive (cyclicBrauerHomRelative hσ₀)) := by
  intro y
  obtain ⟨a, ha⟩ := cyclicBrauerHomRelative_surjective hσ₀ (Additive.toMul y)
  exact ⟨Additive.ofMul a, ha⟩

/-- The two descriptions of `Kˣ / N Lˣ` have the same kernel. -/
theorem ker_toAdditive_cyclicBrauerHomRelative :
    (MonoidHom.toAdditive (cyclicBrauerHomRelative hσ₀)).ker = (tateH0Units σ₀).ker := by
  ext u
  constructor
  · intro h
    have h1 : cyclicBrauerHomRelative hσ₀ (Additive.toMul u) = 1 :=
      Additive.ofMul.injective (AddMonoidHom.mem_ker.mp h)
    refine AddMonoidHom.mem_ker.mpr
      ((tateH0Units_eq_zero_iff σ₀ hσ₀ (Additive.toMul u)).mpr ?_)
    exact (mem_normSubgroup_iff _).mpr ((mem_ker_cyclicBrauerHom_iff hσ₀ _).mp
      (MonoidHom.mem_ker.mpr (Subtype.ext_iff.mp h1)))
  · intro h
    have h1 : Additive.toMul u ∈ normSubgroup K L :=
      (tateH0Units_eq_zero_iff σ₀ hσ₀ (Additive.toMul u)).mp (AddMonoidHom.mem_ker.mp h)
    refine AddMonoidHom.mem_ker.mpr ?_
    exact Subtype.ext (MonoidHom.mem_ker.mp
      ((mem_ker_cyclicBrauerHom_iff hσ₀ _).mpr ((mem_normSubgroup_iff _).mp h1)))

/-- **The relative Brauer group of a cyclic extension is the zeroth Tate group of its unit
group.** -/
noncomputable def brauerRelativeTateEquiv :
    Additive ↥(BrauerGroup.relative K L)
      ≃+ tateH0 (addAut (unitsAut σ₀)) (Nat.card (L ≃ₐ[K] L)) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective
      (MonoidHom.toAdditive (cyclicBrauerHomRelative hσ₀))
      (toAdditive_cyclicBrauerHomRelative_surjective hσ₀)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq
      (ker_toAdditive_cyclicBrauerHomRelative hσ₀)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective _ (tateH0Units_surjective σ₀ hσ₀)))

include hσ₀ in
/-- The order of the zeroth Tate group of the unit group is the order of the relative Brauer
group. -/
theorem card_tateH0_units_eq_card_brauerRelative :
    Nat.card (tateH0 (addAut (unitsAut σ₀)) (Nat.card (L ≃ₐ[K] L)))
      = Nat.card ↥(BrauerGroup.relative K L) := by
  rw [card_tateH0_units σ₀ hσ₀, card_brauerRelative_eq_index_normSubgroup hσ₀]

include hσ₀ in
/-- **The Herbrand quotient of the unit group of a cyclic extension is the order of its relative
Brauer group.**  The lower Tate group is trivial by Hilbert's theorem 90, and the upper one is the
relative Brauer group. -/
theorem herbrand_units_eq_card_brauerRelative :
    herbrand (addAut (unitsAut σ₀)) (Nat.card (L ≃ₐ[K] L))
      = Nat.card ↥(BrauerGroup.relative K L) := by
  rw [herbrand_units σ₀ hσ₀, card_brauerRelative_eq_index_normSubgroup hσ₀]

end InverseGalois.CFT
