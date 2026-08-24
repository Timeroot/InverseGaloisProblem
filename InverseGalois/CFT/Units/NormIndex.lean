/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.CyclicTrivial
import InverseGalois.CFT.Units.IdeleClassFixed
import InverseGalois.CFT.Units.IdeleNorm

/-!
# A cyclic extension whose norms exhaust the ideles is trivial

If every idele of the base field is the sum of a principal idele and a norm from a cyclic extension,
then that extension is trivial.  This is the form in which the first inequality is applied: a
candidate extension is shown to have all of its local conditions satisfied by norms, and then it
must be the trivial extension.

The proof is short, given the first inequality.  An idele class of the extension fixed by the Galois
group is the class of a fixed idele, and a fixed idele is an idele of the base field; writing that
idele as a principal idele plus a norm and passing to classes kills the principal part, so the class
is a norm.  Every fixed class being a norm, the zeroth Tate group of the idele class group is
trivial, and the first inequality bounds the degree by its order.

Nothing here needs a topology on the ideles: the hypothesis is an exact equality of subgroups, not a
density statement, and that is all the argument consumes.

## Main results

* `InverseGalois.CFT.card_le_one_of_ideleDiag_sup_ideleNorm_eq_top`: **a cyclic extension whose
  norms together with the principal ideles exhaust the ideles of the base field has degree at most
  one.**
* `InverseGalois.CFT.subsingleton_gal_of_ideleDiag_sup_ideleNorm_eq_top`: the same, read as the
  triviality of the Galois group.

## Tags

number field, idele, norm, first inequality, cyclic extension
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section NormIndex

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {σ : Gal(K/k)} {n : ℕ} (hn : Nat.card Gal(K/k) = n) [NeZero n]
  (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) (hσ : σ ^ n = 1)

include hn hgen hσ

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **A cyclic extension of number fields whose norms together with the principal ideles exhaust the
ideles of the base field has degree at most one.**  A fixed idele class is the class of an idele of
the base field, and writing that idele as a principal idele plus a norm exhibits the class as a
norm; the first inequality then bounds the degree. -/
theorem card_le_one_of_ideleDiag_sup_ideleNorm_eq_top
    (htop : (ideleDiag k).range ⊔ (ideleNorm k K hgen hσ).range = ⊤) : n ≤ 1 := by
  refine card_le_one_of_forall_normHom_ideleClassAut σ hn hgen fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := exists_fixed_ideleClass hgen hn hσ hx
  obtain ⟨b, rfl⟩ := (mem_range_ideleComap_iff_of_zpowers k K hgen a).mpr ha
  obtain ⟨-, ⟨c, rfl⟩, -, ⟨d, rfl⟩, rfl⟩ :=
    AddSubgroup.mem_sup.mp (htop ▸ AddSubgroup.mem_top b)
  refine ⟨QuotientAddGroup.mk d, ?_⟩
  have hmk : ((normHom (ideleAut (k := k) σ) n d : ↥(idele K)) :
        ↥(idele K) ⧸ (ideleDiag K).range)
      = normHom (ideleClassAut (k := k) σ) n
        ((d : ↥(idele K)) : ↥(idele K) ⧸ (ideleDiag K).range) :=
    map_normHom (σA := ideleAut (k := k) σ) (σB := ideleClassAut (k := k) σ)
      (QuotientAddGroup.mk' ((ideleDiag K).range)) (fun _ => rfl) n d
  rw [← hmk, map_add, ideleComap_ideleDiag, ideleComap_ideleNorm, QuotientAddGroup.mk_add,
    (QuotientAddGroup.eq_zero_iff _).mpr
      (AddMonoidHom.mem_range.mpr ⟨globalUnitsComap k K c, rfl⟩)]
  exact (zero_add ((normHom (ideleAut (k := k) σ) n d : ↥(idele K)) :
    ↥(idele K) ⧸ (ideleDiag K).range)).symm

/-- **A cyclic extension of number fields whose norms together with the principal ideles exhaust the
ideles of the base field is trivial.** -/
theorem subsingleton_gal_of_ideleDiag_sup_ideleNorm_eq_top
    (htop : (ideleDiag k).range ⊔ (ideleNorm k K hgen hσ).range = ⊤) :
    Subsingleton Gal(K/k) := by
  haveI : Finite Gal(K/k) := inferInstance
  refine Finite.card_le_one_iff_subsingleton.mp ?_
  rw [hn]
  exact card_le_one_of_ideleDiag_sup_ideleNorm_eq_top hn hgen hσ htop

end NormIndex

end InverseGalois.CFT
