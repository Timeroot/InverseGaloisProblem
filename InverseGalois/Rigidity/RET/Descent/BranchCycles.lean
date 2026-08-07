/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Descent.CompositumBranch
import InverseGalois.Rigidity.RET.Descent.Matching
import InverseGalois.Rigidity.RET.GeomRET
import InverseGalois.Rigidity.RET.InertiaSub

/-!
# The branch cycles of a certificate on an arithmetic compositum

The geometric existence theorem (`Rigidity.RET.geomRET`) realizes a certificate's rigid tuple as the
deck transformations of a cover of the line over `ℚ̄`, branched over a prescribed finite set of
points.  Taking those points **rational** — the integers `0, 1, …, r-1` — the cover descends to a
`ℚ(T)`-model whose compositum with `ℚ̄(T)` is again a cover of the line with the same branch locus
(`Descent.CompositumBranch`), and the geometric theorem reads the branch cycles off the compositum
directly.

The two tuples — the certificate's tuple, realized on the original cover, and the branch cycles of
the compositum — are related by restriction: the compositum's branch cycle at a point restricts to
an inertia generator of the sub-cover at that point, and inertia generators at one point over a
common base are conjugate, hence generate conjugate cyclic groups.  Rationality of the certificate's
classes turns "conjugate cyclic groups" into "same class", which is what the descent consumes.

## Main results

* `Rigidity.RET.Descent.geomCompositum_branchCycles_exists` — a certificate's classes are realized
  by the branch cycles of a compositum branched over rational points.

The branch cycles are transported along a group isomorphism when the compositum's Galois group is
identified with the geometric part of an arithmetic Galois group; the three elementary transport
lemmas (`closure_range_mulEquiv`, `prod_ofFn_mulEquiv`, `orderOf_dvd_mulEquiv`) are recorded here.
-/

open Polynomial

namespace Rigidity.RET.Descent

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-- A group isomorphism carries a generating family to a generating family. -/
theorem closure_range_mulEquiv {A B : Type*} [Group A] [Group B] (Φ : A ≃* B) {ι : Type*}
    (g : ι → A) (h : Subgroup.closure (Set.range g) = ⊤) :
    Subgroup.closure (Set.range fun i => Φ (g i)) = ⊤ := by
  have hrange : (Set.range fun i => Φ (g i)) = (Φ : A →* B) '' Set.range g := Set.range_comp _ _
  have hmap : Subgroup.closure ((Φ : A →* B) '' (Set.range g))
      = (Subgroup.closure (Set.range g)).map (Φ : A →* B) :=
    (MonoidHom.map_closure (Φ : A →* B) (Set.range g)).symm
  rw [hrange, hmap, h, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
  exact Φ.surjective

/-- A group isomorphism carries a product-one tuple to a product-one tuple. -/
theorem prod_ofFn_mulEquiv {A B : Type*} [Group A] [Group B] (Φ : A ≃* B) {n : ℕ}
    (g : Fin n → A) (h : (List.ofFn g).prod = 1) : (List.ofFn fun i => Φ (g i)).prod = 1 := by
  calc (List.ofFn fun i => Φ (g i)).prod
      = ((List.ofFn g).map (Φ : A →* B)).prod := by rw [List.map_ofFn]; rfl
    _ = (Φ : A →* B) (List.ofFn g).prod := (map_list_prod (Φ : A →* B) _).symm
    _ = 1 := by rw [h, map_one]

/-- A group isomorphism preserves the orders of elements, hence their divisors. -/
theorem orderOf_dvd_mulEquiv {A B : Type*} [Group A] [Group B] (Φ : A ≃* B) (a : A) (n : ℕ)
    (h : orderOf a ∣ n) : orderOf (Φ a) ∣ n := by
  rw [orderOf_dvd_iff_pow_eq_one] at h ⊢
  rw [← map_pow, h, map_one]

/-- **The branch cycles of a certificate, realized on an arithmetic compositum.**

For a rigidity certificate there are `r` distinct *rational* branch points, an arithmetic compositum
`Ωbar = Ω · ℚ̄(T)` branched over them, and branch cycles `g` of that compositum whose images under
the compositum's deck-group map lie in the certificate's prescribed classes.

The geometric input is `Rigidity.RET.geomRET`, applied twice: once to produce a cover with the
prescribed monodromy, and once to read the branch cycles off the compositum built from it.  The
comparison of the two tuples is inertia conjugacy (`LineCover.IsInertiaGenAt.exists_conj`) plus
rationality of the certificate's classes. -/
theorem geomCompositum_branchCycles_exists {G : Type} [Group G] [Finite G]
    (cert : RigidityCertificate G) :
    ∃ (branch : Fin cert.r → ℚ) (c : GeomCompositum G) (g : Fin cert.r → c.cover.deck),
      Function.Injective branch ∧
      c.cover.IsBranchCycleGenSystem (fun i => algebraMap ℚ GeomAKLB.k (branch i)) g ∧
      ∀ i, ConjClasses.mk (c.toG (g i)) = cert.C i := by
  classical
  obtain ⟨base, hbase_class, hbase_prod, hbase_top⟩ := cert.gen
  -- The branch points: the rational points `0, 1, …, r-1` of the line.
  obtain ⟨branch, hbr⟩ : ∃ b : Fin cert.r → ℚ, Function.Injective b :=
    ⟨fun i => ((i : ℕ) : ℚ), fun i j h => Fin.ext (Nat.cast_injective h)⟩
  set t : Fin cert.r → GeomAKLB.k := fun i => algebraMap ℚ GeomAKLB.k (branch i) with htdef
  have ht : Function.Injective t := fun i j hij =>
    hbr ((algebraMap ℚ GeomAKLB.k).injective hij)
  -- The geometric cover with the prescribed monodromy.
  obtain ⟨L, eG, hLunram, hLinf, hgen⟩ :=
    (Rigidity.RET.geomRET t ht).exists_cover base hbase_prod hbase_top
  have hS : Set.range t ⊆ Set.range (algebraMap ℚ GeomAKLB.k) := by
    rintro x ⟨i, rfl⟩
    exact ⟨branch i, rfl⟩
  have hcov0 : (Rigidity.RET.LineCover.of L.M).IsUnramifiedOutside (Set.range t) :=
    Rigidity.RET.LineCover.IsUnramifiedOutside.transport (L := L)
      (L' := Rigidity.RET.LineCover.of L.M) (AlgEquiv.refl) hLunram
  have hcovinf0 : (Rigidity.RET.LineCover.of L.M).IsUnramifiedAtInfinity :=
    Rigidity.RET.LineCover.IsUnramifiedAtInfinity.transport (L := L)
      (L' := Rigidity.RET.LineCover.of L.M) (AlgEquiv.refl) hLinf
  -- Its arithmetic compositum, branched over the same rational points.
  obtain ⟨c, e, hgal, hcov, hcovinf⟩ :=
    geomCompositum_exists_of_cover_unramified L.M eG hS hcov0 hcovinf0
  -- The branch cycles of the compositum.
  obtain ⟨g, hgcyc⟩ := (Rigidity.RET.geomRET t ht).exists_cycles c.cover hcov hcovinf
  refine ⟨branch, c, g, hbr, hgcyc, ?_⟩
  intro i
  -- Both tuples are inertia generators of the sub-cover at the `i`-th branch point, hence conjugate.
  have h1 : (c.cover.sub c.Lsub).IsInertiaGenAt (t i) (c.cover.subHom c.Lsub (g i)) :=
    Rigidity.RET.LineCover.IsInertiaGenAt.restrict c.cover (hgcyc.inertia i)
  have h2 : (c.cover.sub c.Lsub).IsInertiaGenAt (t i)
      (AlgEquiv.autCongr e (eG.symm (base i))) :=
    Rigidity.RET.LineCover.IsInertiaGenAt.transport (L := L)
      (L' := c.cover.sub c.Lsub) e (hgen i)
  obtain ⟨d, hd⟩ := h1.exists_conj h2
  have hzp : ∀ x : c.Lsub ≃ₐ[RatFunc GeomAKLB.k] c.Lsub,
      Subgroup.zpowers (c.galLsub x) = (Subgroup.zpowers x).map c.galLsub.toMonoidHom :=
    fun x => (MonoidHom.map_zpowers c.galLsub.toMonoidHom x).symm
  have key : Subgroup.zpowers (c.galLsub (AlgEquiv.autCongr e (eG.symm (base i))))
      = Subgroup.zpowers (c.galLsub (d * c.cover.subHom c.Lsub (g i) * d⁻¹)) := by
    rw [hzp, hzp, hd]
  rw [hgal, eG.apply_symm_apply, map_mul, map_mul, map_inv] at key
  -- Rationality upgrades "conjugate cyclic groups" to "same class".
  have hmk := (cert.rational i).mk_eq_of_zpowers_eq (hbase_class i) key.symm
  rw [← hmk]
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨c.galLsub d, rfl⟩)

end Rigidity.RET.Descent
