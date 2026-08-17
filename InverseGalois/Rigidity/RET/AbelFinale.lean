/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.AbelRegular
import InverseGalois.Rigidity.RET.RegularQuotient

/-!
# Every finite abelian group is a regular inverse Galois group

The multi-radical layer of `Rigidity.RET.Abel` realizes `(ℤ/n)ᵏ` regularly over `ℚ`: its Galois
group is the group of `k`-tuples of `n`-th roots of unity, and the group of `n`-th roots of unity
in the multi-radical extension is cyclic of order exactly `n`.

An arbitrary finite abelian group `A` is a product `∏ ℤ/mᵢ`.  Taking `n` to be the product of the
`mᵢ` and `k` the number of factors, the projections `ℤ/n ↠ ℤ/mᵢ` assemble into a surjection of
`(ℤ/n)ᵏ` onto `A`, and a quotient of a regular inverse Galois group is one.

## Main results

* `Rigidity.RET.Abel.isRegularInverseGalois_pow` — `(ℤ/n)ᵏ` is a regular inverse Galois group.
* `Rigidity.RET.IsRegularInverseGalois.of_commGroup` — every finite abelian group is a regular
  inverse Galois group over `ℚ`.
-/

open Polynomial

namespace Rigidity.RET.Abel

noncomputable section

attribute [local instance] Polynomial.algebra

open scoped RatFunc IntermediateField

open Rigidity.RET.Cyclic

variable (n : ℕ) [hn : Fact (1 < n)] (k : ℕ)

/-! ### The roots of unity of the multi-radical extension -/

instance hasEnoughRootsOfUnity_MA : HasEnoughRootsOfUnity (MA n k) n :=
  ⟨⟨_, zetaMA_isPrimitiveRoot n k⟩, rootsOfUnity.isCyclic (MA n k) n⟩

theorem card_rootsOfUnity_MA :
    Nat.card (rootsOfUnity n (MA n k)) = Nat.card (Multiplicative (ZMod n)) := by
  rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity (MA n k) n]
  exact (Nat.card_zmod n).symm

/-- **The `n`-th roots of unity of the multi-radical extension form a cyclic group of order
`n`.** -/
def rootsEquivZMod : rootsOfUnity n (MA n k) ≃* Multiplicative (ZMod n) :=
  mulEquivOfCyclicCardEq (card_rootsOfUnity_MA n k)

/-! ### The regular realization of `(ℤ/n)ᵏ` -/

/-- **`(ℤ/n)ᵏ` is a regular inverse Galois group over `ℚ`.** -/
theorem isRegularInverseGalois_pow :
    IsRegularInverseGalois (Fin k → Multiplicative (ZMod n)) :=
  (isRegularInverseGalois_autA n k).of_mulEquiv
    ((galLAEquivRoots n k).trans (MulEquiv.piCongrRight fun _ => rootsEquivZMod n k))

end

end Rigidity.RET.Abel

namespace Rigidity.RET.IsRegularInverseGalois

/-- **Every finite abelian group is a regular inverse Galois group over `ℚ`.**  Write the group as
a product of cyclic groups `ℤ/mᵢ`, let `n` be the product of the `mᵢ` and `k` the number of
factors; then `(ℤ/n)ᵏ` surjects onto it, and `(ℤ/n)ᵏ` is realized by the multi-radical layer. -/
theorem of_commGroup (A : Type*) [CommGroup A] [Finite A] : IsRegularInverseGalois A := by
  classical
  obtain ⟨ι, hιfin, m, hm1, ⟨eA⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI : Subsingleton A := eA.subsingleton
    exact _root_.IsRegularInverseGalois.of_subsingleton
  · set N : ℕ := ∏ i, m i with hNdef
    have hNpos : 0 < N := Finset.prod_pos fun i _ => lt_trans one_pos (hm1 i)
    have hdvd : ∀ i, m i ∣ N := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨i₀⟩ := hι
    have hN : 1 < N := lt_of_lt_of_le (hm1 i₀) (Nat.le_of_dvd hNpos (hdvd i₀))
    haveI : Fact (1 < N) := ⟨hN⟩
    set k : ℕ := Fintype.card ι with hkdef
    set e : ι ≃ Fin k := Fintype.equivFin ι with hedef
    -- the projections `ℤ/N ↠ ℤ/mᵢ`
    set ψ : ∀ i, Multiplicative (ZMod N) →* Multiplicative (ZMod (m i)) := fun i =>
      AddMonoidHom.toMultiplicative (ZMod.castHom (hdvd i) (ZMod (m i))).toAddMonoidHom with hψdef
    have hψ : ∀ i, Function.Surjective (ψ i) := fun i t => by
      obtain ⟨x, hx⟩ := ZMod.castHom_surjective (hdvd i) (Multiplicative.toAdd t)
      exact ⟨Multiplicative.ofAdd x, congrArg Multiplicative.ofAdd hx⟩
    -- assembled into a surjection of `(ℤ/N)ᵏ` onto the product
    set Φ : (Fin k → Multiplicative (ZMod N)) →* (∀ i, Multiplicative (ZMod (m i))) :=
      { toFun := fun w i => ψ i (w (e i))
        map_one' := by funext i; simp
        map_mul' := fun w w' => by funext i; simp } with hΦdef
    have hΦ : Function.Surjective Φ := fun t => by
      choose g hg using fun i => hψ i (t i)
      refine ⟨fun j => g (e.symm j), funext fun i => ?_⟩
      simpa [hΦdef, Equiv.symm_apply_apply] using hg i
    exact _root_.IsRegularInverseGalois.of_surjective
      (Rigidity.RET.Abel.isRegularInverseGalois_pow N k) (eA.symm.toMonoidHom.comp Φ)
      (eA.symm.surjective.comp hΦ)

end Rigidity.RET.IsRegularInverseGalois
