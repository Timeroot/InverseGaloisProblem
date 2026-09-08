/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LevelTwist

/-!
# The whole ladder, in exchange for one package of arithmetic

The group theory of the descending `ℓ`-central series has been spent: a solution at one level of
the series, taken with enough letters, lifts to a smooth surjection at the next level over the base
realization, and the one clause that does not come for free is bought with a prescription of
restrictions in degree one.  What is asked of the arithmetic is therefore a short and fixed list,
and it is collected here into a single named condition so that the whole ladder follows from it.

The list has four entries.  A finite family of subgroups and a wider family against which local
triviality is measured are chosen once from the base realization; then the first rung is asked for
outright, since the layer there is the Frattini layer and a lift over it need not be onto; and at
every later rung three things are asked, for every number of letters: that the step be locally
solvable along the members of the wider family the finite one does not name, that every everywhere
locally trivial class of the layer be inflated from the operator group, and that restrictions of a
smooth one cocycle with values in the layer be prescribable along the finite family.

Granted that package, one rung follows from the previous one, and hence, by the ladder already
built, every split embedding problem with a kernel of prime power order.

## Main definitions

* `InverseGalois.Shafarevich.HasRungData` — **everything the arithmetic has to supply for the whole
  ladder**, gathered into one condition.

## Main results

* `InverseGalois.Shafarevich.levelSolution_succ_of_hasRungData` — one rung of the ladder from that
  package.
* `Shafarevich.genericLevelStepEP_of_hasRungData` — **and hence the step of the ladder itself.**

## Tags

Shafarevich's theorem, embedding problem, p-central series, local conditions, Shafarevich group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

/-! ### The arithmetic the ladder consumes -/

/-- **Everything the arithmetic has to supply for the whole ladder.**

A finite family of subgroups and a wider family against which local triviality is measured are
fixed in advance; in the arithmetic the first is the family of decomposition subgroups at the
places which ramify in the field the base realization cuts out, at the places above `ℓ` and at the
infinite places, and the second is the family of all decomposition subgroups.

The first rung is asked for outright, because the layer there is the Frattini layer of the group
and a lift across it carries no guarantee of being onto.  At every later rung three things are
asked, for every number of letters: that the step be locally solvable along the members of the
wider family which the finite one does not name, that every everywhere locally trivial class of the
layer be inflated from the operator group, and that the restrictions of a smooth one cocycle with
values in the layer be prescribable along the finite family. -/
def HasRungData (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] [TopologicalSpace U]
    [DiscreteTopology U] (S : Type) [Group S] [Finite S] {k Ω : Type*} [Field k] [Field Ω]
    [Algebra k Ω] (φ : Gal(Ω/k) →* U) {t : ℕ} (D : Fin t → Subgroup Gal(Ω/k))
    (T : Set (Subgroup Gal(Ω/k))) : Prop :=
  (∀ n : ℕ, LevelSolution ℓ U S φ (Set.range D) n 1) ∧
    ∀ n j : ℕ, 1 ≤ j → HasLocalLift ℓ U n S j φ D T ∧ HasInflatedSha ℓ U n S j φ T ∧
      @HasCocyclePrescription Gal(Ω/k) _ _ ↥(layerSub ℓ (Generic U n S) j) _
        (galLayerAction ℓ U n S j φ) t fun ν => D ν ⊓ φ.ker

/-! ### One rung -/

/-- **One rung of the ladder, from the arithmetic.**  At the bottom the package supplies the rung
itself; past it the three conditions of the package are exactly the three the rung consumes, the
locally trivial classes being carried away by a second shrinking. -/
theorem levelSolution_succ_of_hasRungData (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U]
    [TopologicalSpace U] [DiscreteTopology U] (S : Type) [Group S] [Finite S] (hS : IsPGroup ℓ S)
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (φ : Gal(Ω/k) →* U) (hsmφ : IsSmoothHom φ)
    {t : ℕ} (D : Fin t → Subgroup Gal(Ω/k)) (T : Set (Subgroup Gal(Ω/k)))
    (hdata : HasRungData ℓ U S φ D T) (j : ℕ)
    (h : ∀ m : ℕ, LevelSolution ℓ U S φ (Set.range D) m j) (n : ℕ) :
    LevelSolution ℓ U S φ (Set.range D) n (j + 1) := by
  cases j with
  | zero => exact hdata.1 n
  | succ j =>
    have hj : 1 ≤ j + 1 := Nat.le_add_left 1 j
    letI := galLayerAction ℓ U n S (j + 1) φ
    exact levelSolution_succ_of_hasInflatedSha ℓ U n S hS hj φ hsmφ (fun _ _ => rfl) D T
      (fun m => (hdata.2 m (j + 1) hj).1) (fun m => (hdata.2 m (j + 1) hj).2.1)
      (hdata.2 n (j + 1) hj).2.2 h

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich

/-! ### The step of the ladder -/

/-- **The step of the ladder of the descending `ℓ`-central series, from the arithmetic.**  A base
realization is given a finite family of subgroups and a wider family against which local triviality
is measured, together with the four conditions the rungs consume, and the step follows. -/
theorem genericLevelStepEP_of_hasRungData (ℓ : ℕ) [Fact ℓ.Prime]
    (h : ∀ (S U : Type) [Group S] [Finite S] [Group U] [Finite U] [TopologicalSpace U]
        [DiscreteTopology U] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω]
        (φ : Gal(Ω/ℚ) →* U), IsPGroup ℓ S → Function.Surjective φ → IsSmoothHom φ →
      ∃ (t : ℕ) (D : Fin t → Subgroup Gal(Ω/ℚ)) (T : Set (Subgroup Gal(Ω/ℚ))),
        HasRungData ℓ U S φ D T) :
    GenericLevelStepEP ℓ := by
  intro S U _ _ _ _ _ _ Ω _ _ _ _ φ hS hsurj hsm
  obtain ⟨t, D, T, hdata⟩ := h S U Ω φ hS hsurj hsm
  exact ⟨Set.range D,
    fun j hj n => levelSolution_succ_of_hasRungData ℓ U S hS φ hsm D T hdata j hj n⟩

end Shafarevich
