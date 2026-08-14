/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.FreeAbelianCover
import InverseGalois.Rigidity.RET.ExistenceCyclic
import InverseGalois.Rigidity.RET.SubUnramified

/-!
# Covers of the line with a prescribed abelian deck group and prescribed branch cycles

`RET/FreeAbelianCover.lean` builds, over any `s + 1` points of the line, a cover whose deck group is
the free abelian group `(ℤ/n)^s` of exponent `n`, with the coordinate vectors as the distinguished
inertia generators at the first `s` points and the inverse of their product at the last one.  Every
finite abelian group with a prescribed system of branch cycles is a quotient of that group by a
subgroup, so it is realized by the corresponding Galois subcover.

## Main results

* `Rigidity.RET.descentEquiv` — the deck group of the subcover fixed by `ker f` is the target of
  `f`.
* `Rigidity.RET.exists_cover_of_commGroup` — every finite abelian group, together with a
  product-one generating tuple of `r` elements, is the deck group of a cover of the line branched
  at `r` prescribed points, unramified elsewhere and at infinity, with the tuple as its
  distinguished branch cycles.
-/

open Polynomial IntermediateField

noncomputable section


namespace Rigidity.RET

open GeomAKLB

/-! ### Descending a cover along a surjection of its deck group -/

section Descent

variable {L : LineCover} {H : Type} [Group H]

/-- **The deck group of the subcover fixed by `ker f` is the target of `f`.** -/
def descentEquiv (f : L.deck →* H) (hf : Function.Surjective f) :
    (L.sub (fixedField f.ker)).deck ≃* H :=
  (IsGalois.normalAutEquivQuotient (L := L.M) f.ker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The identification of the deck group of the subcover is compatible with restriction of
automorphisms. -/
theorem descentEquiv_apply (f : L.deck →* H) (hf : Function.Surjective f) (σ : L.deck) :
    descentEquiv f hf (L.subHom (fixedField f.ker) σ) = f σ := by
  have h1 : IsGalois.normalAutEquivQuotient (L := L.M) f.ker (σ : L.deck ⧸ f.ker)
      = L.subHom (fixedField f.ker) σ := rfl
  have h2 : (IsGalois.normalAutEquivQuotient (L := L.M) f.ker).symm
      (L.subHom (fixedField f.ker) σ) = (σ : L.deck ⧸ f.ker) :=
    (MulEquiv.symm_apply_eq _).mpr h1.symm
  have h3 : descentEquiv f hf (L.subHom (fixedField f.ker) σ)
      = QuotientGroup.quotientKerEquivOfSurjective f hf
          ((IsGalois.normalAutEquivQuotient (L := L.M) f.ker).symm
            (L.subHom (fixedField f.ker) σ)) := rfl
  rw [h3, h2]
  exact QuotientGroup.kerLift_mk f σ

end Descent

/-! ### The abelian existence theorem -/

section Abelian

variable {H : Type} [CommGroup H] [Finite H]

omit [Finite H] in
/-- A tuple all of whose entries are trivial generates only the trivial group. -/
theorem subsingleton_of_forall_eq_one {r : ℕ} {h : Fin r → H} (hall : ∀ i, h i = 1)
    (htop : Subgroup.closure (Set.range h) = ⊤) : Subsingleton H := by
  have hle : Subgroup.closure (Set.range h) ≤ ⊥ :=
    (Subgroup.closure_le _).mpr (by rintro x ⟨i, rfl⟩; simp [hall i])
  rw [htop] at hle
  refine ⟨fun a b => ?_⟩
  have ha := Subgroup.mem_bot.mp (hle (Subgroup.mem_top a))
  have hb := Subgroup.mem_bot.mp (hle (Subgroup.mem_top b))
  rw [ha, hb]

/-- **Every finite abelian group is the deck group of a cover of the line with prescribed branch
points and prescribed branch cycles.** -/
theorem exists_cover_of_commGroup {r : ℕ} (t : Fin r → k) (ht : Function.Injective t)
    (h : Fin r → H) (hprod : (List.ofFn h).prod = 1)
    (htop : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (L : LineCover) (e : L.deck ≃* H),
      L.IsUnramifiedOutside (Set.range t) ∧ L.IsUnramifiedAtInfinity ∧
      ∀ i, L.IsInertiaGenAt (t i) (e.symm (h i)) := by
  classical
  have hprodF : ∏ i, h i = 1 := by rw [← List.prod_ofFn]; exact hprod
  -- the trivial group is cyclic, so few branch points are handled by the cyclic case
  have htriv : ∀ _ : Subsingleton H, ∃ (L : LineCover) (e : L.deck ≃* H),
      L.IsUnramifiedOutside (Set.range t) ∧ L.IsUnramifiedAtInfinity ∧
      ∀ i, L.IsInertiaGenAt (t i) (e.symm (h i)) := by
    intro hsub
    haveI := hsub
    haveI : IsCyclic H := ⟨⟨1, fun x => by rw [Subsingleton.elim x 1]; exact Subgroup.mem_zpowers 1⟩⟩
    exact exists_cover_of_isCyclic t ht h hprod htop
  rcases (show r ≤ 1 ∨ ∃ s, r = s + 2 by
      match r with
      | 0 => exact Or.inl (by omega)
      | 1 => exact Or.inl (by omega)
      | (s + 2) => exact Or.inr ⟨s, rfl⟩) with hr | ⟨s, rfl⟩
  · -- at most one branch point: the tuple is trivial, and so is the group
    haveI : Subsingleton (Fin r) := Fin.subsingleton_iff_le_one.mpr hr
    refine htriv (subsingleton_of_forall_eq_one (fun i => ?_) htop)
    rw [← hprodF]
    exact (Finset.prod_eq_single_of_mem i (Finset.mem_univ i)
      (fun j _ hj => absurd (Subsingleton.elim j i) hj)).symm
  -- the exponent of the free cover
  set n := Nat.card H with hn
  haveI : NeZero n := ⟨Nat.card_pos.ne'⟩
  have hpow : ∀ x : H, x ^ n = 1 := fun x => pow_card_eq_one'
  -- the surjection of the free abelian group onto `H` determined by the branch cycles
  let π : (Fin (s + 1) → Multiplicative (ZMod n)) →* H :=
    { toFun := fun m => ∏ l, zmodPowHom (hpow (h l.castSucc)) (m l)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib] }
  have hπapply : ∀ m : Fin (s + 1) → Multiplicative (ZMod n),
      π m = ∏ l : Fin (s + 1), zmodPowHom (hpow (h l.castSucc)) (m l) := fun _ => rfl
  have hπsingle : ∀ j : Fin (s + 1),
      π (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod n))) = h j.castSucc := by
    intro j
    rw [hπapply, Finset.prod_eq_single j]
    · rw [Pi.mulSingle_eq_same, zmodPowHom_ofAdd_one]
    · intro l _ hl
      rw [Pi.mulSingle_eq_of_ne hl, map_one]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hπdiag : π (fun _ => Multiplicative.ofAdd (1 : ZMod n))⁻¹ = h (Fin.last (s + 1)) := by
    have hval : π (fun _ => Multiplicative.ofAdd (1 : ZMod n))
        = ∏ l : Fin (s + 1), h l.castSucc := by
      rw [hπapply]
      exact Finset.prod_congr rfl fun l _ => zmodPowHom_ofAdd_one _
    rw [map_inv, hval]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← Fin.prod_univ_castSucc]
    exact hprodF
  have hπsurj : Function.Surjective π := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← htop, Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    refine Fin.lastCases ⟨_, hπdiag⟩ (fun j => ⟨_, hπsingle j⟩) i
  -- the free abelian cover, and the subcover cut out by the kernel
  obtain ⟨L, e, -, hout, hinf, hgen, hlast⟩ := exists_cover_free n t ht
  let f : L.deck →* H := π.comp e.toMonoidHom
  have hfsurj : Function.Surjective f := hπsurj.comp e.surjective
  have hkey : ∀ x : Fin (s + 1) → Multiplicative (ZMod n),
      (descentEquiv f hfsurj).symm (π x) = L.subHom (fixedField f.ker) (e.symm x) := by
    intro x
    rw [MulEquiv.symm_apply_eq, descentEquiv_apply]
    show π x = π (e (e.symm x))
    rw [e.apply_symm_apply]
  refine ⟨L.sub (fixedField f.ker), descentEquiv f hfsurj, hout.sub _, hinf.sub _, ?_⟩
  refine Fin.lastCases ?_ ?_
  · rw [← hπdiag, hkey]
    exact LineCover.IsInertiaGenAt.restrict L (hlast (Nat.succ_pos s))
  · intro j
    rw [← hπsingle j, hkey]
    exact LineCover.IsInertiaGenAt.restrict L (hgen j)

end Abelian

end Rigidity.RET
