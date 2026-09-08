/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LayerSplit
import InverseGalois.Solvable.Shafarevich.PrimePower

/-!
# The descending `p`-central series as a ladder for the generic embedding problem

The generic split embedding problem asks for a semidirect product of a Galois group with a
relatively free operator group over a finite `p`-group to be a Galois group again.  The kernel is
then a finite `p`-group, so its descending `p`-central series starts at the whole group and reaches
the trivial subgroup after finitely many steps, and dividing by the terms of that series presents
the semidirect product as the top of a finite tower whose bottom is the operator group alone and
whose every step adjoins one layer.

Both ends of that tower are free.  At the bottom the zeroth term is the whole kernel, so the
semidirect product with the quotient by it is the operator group itself, which is a Galois group by
hypothesis.  At the top some term is trivial, so the quotient by it is the kernel itself and the
semidirect product with it is the group asked for.  What is left is the step from one layer to the
next, and this file isolates exactly that as a single named statement.

The statement is arranged so that the step may shrink the group it works with: solving at one layer
is allowed to use the solution at the previous layer for *every* number of letters, not only for the
one in hand.  That is what the count which makes the class of an extension die on prescribed
subgroups consumes, since it produces the number of letters it needs and only afterwards receives
the data it has to kill.

## Main definitions

* `Shafarevich.GenericLayerStepEP` — **one step of the tower**: solving the generic problem at every
  number of letters for one term of the series solves it for the next.

## Main results

* `InverseGalois.Shafarevich.pCentralZeroEquiv` — the bottom of the tower is the operator group.
* `InverseGalois.Shafarevich.pCentralBotSemidirectHom_surjective` — the top of the tower covers the
  semidirect product asked for.
* `Shafarevich.genericSplitEP_of_genericLayerStepEP` — **climbing the tower one layer at a time
  solves the generic split embedding problem.**
* `Shafarevich.splitPrimePowerEP_of_genericLayerStepEP` — **and hence every split embedding problem
  with a kernel of prime power order.**

## Tags

Shafarevich's theorem, embedding problem, p-central series, semidirect product, induction
-/

namespace InverseGalois.Shafarevich

/-! ### The two ends of the filtration -/

/-- The zeroth term of the descending `p`-central series is the whole group, so the quotient by it
is trivial. -/
instance subsingleton_quotient_pCentral_zero {p : ℕ} {P : Type*} [Group P] :
    Subsingleton (P ⧸ pCentral p P 0) :=
  QuotientGroup.subsingleton_quotient_top

/-- **At the bottom of the filtration the semidirect product is the operator group itself.** -/
def pCentralZeroEquiv (p : ℕ) {P U : Type*} [Group P] [Group U] (χ : U →* MulAut P) :
    (P ⧸ pCentral p P 0) ⋊[pCentralAut p χ 0] U ≃* U :=
  _root_.Shafarevich.rightEquivOfSubsingleton _

/-- When a term of the descending `p`-central series is trivial, the quotient by it is the group
itself. -/
def pCentralBotHom {p : ℕ} {P : Type*} [Group P] {j : ℕ} (hj : pCentral p P j = ⊥) :
    P ⧸ pCentral p P j →* P :=
  QuotientGroup.lift _ (MonoidHom.id P) fun _ hx => Subgroup.mem_bot.1 (hj ▸ hx)

@[simp]
theorem pCentralBotHom_mk {p : ℕ} {P : Type*} [Group P] {j : ℕ} (hj : pCentral p P j = ⊥) (x : P) :
    pCentralBotHom hj (QuotientGroup.mk x) = x := rfl

/-- **At the top of the filtration the semidirect product with a quotient of the series maps onto
the semidirect product with the group itself.** -/
def pCentralBotSemidirectHom {p : ℕ} {P U : Type*} [Group P] [Group U] (χ : U →* MulAut P) {j : ℕ}
    (hj : pCentral p P j = ⊥) : (P ⧸ pCentral p P j) ⋊[pCentralAut p χ j] U →* P ⋊[χ] U :=
  SemidirectProduct.map (pCentralBotHom hj) (MonoidHom.id U) fun _ =>
    MonoidHom.ext fun y => by
      induction y using QuotientGroup.induction_on with
      | _ x => rfl

/-- **The top of the tower covers the semidirect product asked for.** -/
theorem pCentralBotSemidirectHom_surjective {p : ℕ} {P U : Type*} [Group P] [Group U]
    (χ : U →* MulAut P) {j : ℕ} (hj : pCentral p P j = ⊥) :
    Function.Surjective (pCentralBotSemidirectHom χ hj) :=
  fun x => ⟨⟨QuotientGroup.mk x.left, x.right⟩, rfl⟩

/-! ### The two ends of the tower for the generic operator groups -/

/-- **At the bottom of the filtration the generic operator group contributes nothing**, so the
group there is the operator group itself. -/
theorem isInverseGalois_genericQuot_zero (ℓ : ℕ) (U : Type) [Group U] (m : ℕ) (S : Type) [Group S]
    (hU : IsInverseGalois U) : IsInverseGalois (GenericQuot ℓ U m S 0) :=
  hU.of_mulEquiv (pCentralZeroEquiv ℓ (genericAut U m S)).symm

/-- **At the top of the filtration the generic split embedding problem is solved.** -/
theorem isInverseGalois_generic_semidirect_of_genericQuot (ℓ : ℕ) (U : Type) [Group U] (n : ℕ)
    (S : Type) [Group S] (j : ℕ) (hj : pCentral ℓ (Generic U n S) j = ⊥)
    (h : IsInverseGalois (GenericQuot ℓ U n S j)) :
    IsInverseGalois (Generic U n S ⋊[genericAut U n S] U) :=
  h.of_surjective _ (pCentralBotSemidirectHom_surjective (genericAut U n S) hj)

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.Shafarevich

/-- **One step of the tower of the descending `ℓ`-central series.**  Whenever `U` is a Galois group
over `ℚ`, `S` is a finite `ℓ`-group and the generic operator group over `S`, divided by one term of
its descending `ℓ`-central series and carrying its operators alongside, is a Galois group over `ℚ`
for every number of letters, the same holds one term further along the series.

The solution at the previous term is required for every number of letters because the step is
allowed to shrink: making the class of the extension die on prescribed subgroups costs letters, and
how many it costs is settled only once those subgroups are known. -/
def GenericLayerStepEP (ℓ : ℕ) : Prop :=
  ∀ (S U : Type) [Group S] [Finite S] [Group U] [Finite U], IsPGroup ℓ S → IsInverseGalois U →
    ∀ j : ℕ, (∀ m : ℕ, IsInverseGalois (GenericQuot ℓ U m S j)) →
      ∀ n : ℕ, IsInverseGalois (GenericQuot ℓ U n S (j + 1))

/-- **Climbing the tower**: one step at a time solves the generic problem at every term of the
descending `ℓ`-central series. -/
theorem forall_isInverseGalois_genericQuot {ℓ : ℕ} (h : GenericLayerStepEP ℓ) (S U : Type)
    [Group S] [Finite S] [Group U] [Finite U] (hS : IsPGroup ℓ S) (hU : IsInverseGalois U) (j : ℕ) :
    ∀ m : ℕ, IsInverseGalois (GenericQuot ℓ U m S j) := by
  induction j with
  | zero => exact fun m => isInverseGalois_genericQuot_zero ℓ U m S hU
  | succ j ih => exact fun n => h S U hS hU j ih n

/-- **One layer at a time solves the generic split embedding problem.**  The descending
`ℓ`-central series of the kernel reaches the trivial subgroup, and the group there is the one the
problem asks for. -/
theorem genericSplitEP_of_genericLayerStepEP {ℓ : ℕ} [Fact ℓ.Prime] (h : GenericLayerStepEP ℓ) :
    GenericSplitEP ℓ := by
  intro S U _ _ _ _ n hS hU
  obtain ⟨j, hj⟩ := exists_pCentral_eq_bot ℓ (isPGroup_generic U n S hS)
  exact isInverseGalois_generic_semidirect_of_genericQuot ℓ U n S j hj
    (forall_isInverseGalois_genericQuot h S U hS hU j n)

/-- **One layer at a time solves every split embedding problem with a kernel of prime power
order.** -/
theorem splitPrimePowerEP_of_genericLayerStepEP
    (h : ∀ ℓ : ℕ, ℓ.Prime → GenericLayerStepEP ℓ) : SplitPrimePowerEP := by
  intro H U _ _ _ _ p hp hH φ hU
  exact isInverseGalois_semidirectProduct_of_generic φ
    (genericSplitEP_of_genericLayerStepEP (h p hp.out) H U (Nat.card H) hH hU)

end Shafarevich
