/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GrunwaldWang
import InverseGalois.CFT.Tate.TorsionRep
import InverseGalois.CFT.Units.IdeleClassSES

/-!
# The elements killed by a prime of the units, the ideles and the idele classes

The units of a number field, its ideles and its idele classes form a short exact sequence, and
passing to the elements killed by a fixed integer preserves the injectivity of the first map and the
exactness in the middle, since both are read off from the same equations.  What it does not
automatically preserve is the surjectivity of the second map: an idele class killed by the integer
is represented by an idele whose power is a principal idele, not by an idele whose power is trivial.

The obstruction is exactly the Hasse principle for powers.  If the power of an idele is the
principal idele of a unit of the field, then that unit is a power in the completion at every place,
so for a prime exponent Wang's theorem makes it a power in the field itself; subtracting the
principal idele of a root moves the representative to one killed by the exponent without changing
its class.  So for a prime exponent the sequence stays short exact, and the elements of the idele
class group killed by that prime are the elements of the idele group killed by it, modulo the roots
of unity of the field.

## Main definitions

* `InverseGalois.CFT.globalUnitsToIdeleTorsion`, `InverseGalois.CFT.ideleToIdeleClassTorsion`: the
  two maps, restricted to the elements killed by an integer.
* `InverseGalois.CFT.ideleClassTorsionShortComplex`: the three representations, assembled into a
  short complex.

## Main results

* `InverseGalois.CFT.exists_zsmul_eq_of_ideleDiag_eq_zsmul`: **a unit of the field whose principal
  idele is a power in the ideles is itself a power in the field**, by the Hasse principle for
  powers.
* `InverseGalois.CFT.exists_torsion_idele_mk_eq`: **an idele class killed by a prime is the class of
  an idele killed by that prime.**
* `InverseGalois.CFT.ideleClassTorsionShortComplex_shortExact`: **the elements killed by a prime of
  the units, of the ideles and of the idele classes form a short exact sequence of representations
  of the Galois group.**

## Tags

number field, idele, idele class group, root of unity, Hasse principle, short exact sequence
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open CategoryTheory IsDedekindDomain NumberField

namespace InverseGalois.CFT

section Torsion

variable (k K : Type) [Field k] [Field K] [NumberField K] [Algebra k K] (m : ℤ)

/-- The principal ideles, restricted to the elements killed by an integer. -/
noncomputable def globalUnitsToIdeleTorsion :
    torsionRep (globalUnitsAut (k := k) (K := K)) m ⟶ torsionRep (ideleAutHom k K) m :=
  torsionMap m (ideleDiag K) fun g a => (ideleAut_ideleDiag g a).symm

/-- The passage to idele classes, restricted to the elements killed by an integer. -/
noncomputable def ideleToIdeleClassTorsion :
    torsionRep (ideleAutHom k K) m ⟶ torsionRep (ideleClassAutHom k K) m :=
  torsionMap m (QuotientAddGroup.mk' (ideleDiag K).range) fun _ _ => rfl

/-- The elements killed by an integer of the units, of the ideles and of the idele classes,
assembled into a short complex of representations of the Galois group. -/
noncomputable def ideleClassTorsionShortComplex : ShortComplex (Rep ℤ Gal(K/k)) where
  X₁ := torsionRep (globalUnitsAut (k := k) (K := K)) m
  X₂ := torsionRep (ideleAutHom k K) m
  X₃ := torsionRep (ideleClassAutHom k K) m
  f := globalUnitsToIdeleTorsion k K m
  g := ideleToIdeleClassTorsion k K m
  zero := by
    ext a
    exact Subtype.ext ((QuotientAddGroup.eq_zero_iff _).2 ⟨a.1, rfl⟩)

end Torsion

/-! ### The Hasse principle moves the representative -/

section Hasse

variable {K : Type} [Field K] [NumberField K]

/-- **A unit of the field whose principal idele is a power in the ideles is itself a power in the
field.**  Reading the equation at a finite place makes the unit a power in that completion, and for
a prime exponent Wang's theorem then makes it a power in the field. -/
theorem exists_zsmul_eq_of_ideleDiag_eq_zsmul {p : ℕ} (hp : p.Prime) (u : Additive Kˣ)
    (z : ↥(idele K)) (hu : ideleDiag K u = (p : ℤ) • z) :
    ∃ y : Additive Kˣ, (p : ℤ) • y = u := by
  -- the unit is a `p`-th power at every finite place
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ (∅ : Set (HeightOneSpectrum (𝓞 K))) →
      ∃ c : v.adicCompletion K,
        c ^ p = algebraMap K (v.adicCompletion K) ((Additive.toMul u : Kˣ) : K) := by
    intro v _
    refine ⟨((Additive.toMul ((z : FullIdele K).2 v) : (v.adicCompletion K)ˣ) :
      v.adicCompletion K), ?_⟩
    have h2 : Additive.ofMul (adicUnitHom v (Additive.toMul u))
        = ((p : ℤ) • (z : FullIdele K)).2 v :=
      congrFun (congrArg Prod.snd (congrArg Subtype.val hu)) v
    have h3 : adicUnitHom v (Additive.toMul u)
        = Additive.toMul ((z : FullIdele K).2 v) ^ p := by
      have h4 : adicUnitHom v (Additive.toMul u)
          = Additive.toMul (((p : ℤ) • (z : FullIdele K)).2 v) := congrArg Additive.toMul h2
      rw [h4]
      show Additive.toMul ((p : ℤ) • (z : FullIdele K).2 v) = _
      rw [toMul_zsmul, zpow_natCast]
    rw [← Units.val_pow_eq_pow_val, ← h3]
    exact coe_adicUnitHom v _
  obtain ⟨y, hy⟩ := exists_pow_eq_of_forall_localPow_outside_of_prime hp Set.finite_empty hloc
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hy
    exact (Additive.toMul u : Kˣ).ne_zero hy.symm
  refine ⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩
  refine Additive.toMul.injective ?_
  rw [toMul_zsmul, zpow_natCast]
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val]
  exact hy

/-- **An idele class killed by a prime is the class of an idele killed by that prime.**  A
representative has its power equal to the principal idele of a unit of the field, so that unit is a
power in the field; subtracting the principal idele of a root leaves the class unchanged and kills
the power. -/
theorem exists_torsion_idele_mk_eq {p : ℕ} (hp : p.Prime) (c : IdeleClass K)
    (hc : (p : ℤ) • c = 0) :
    ∃ x : ↥(idele K), (p : ℤ) • x = 0 ∧ QuotientAddGroup.mk' (ideleDiag K).range x = c := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨u, hu⟩ := (QuotientAddGroup.eq_zero_iff _).1 hc
  have hu' : ideleDiag K u = (p : ℤ) • z := hu
  obtain ⟨y, hy⟩ := exists_zsmul_eq_of_ideleDiag_eq_zsmul hp u z hu'
  refine ⟨z - ideleDiag K y, ?_, ?_⟩
  · rw [zsmul_sub, ← hu', ← map_zsmul, hy, sub_self]
  · have hz : QuotientAddGroup.mk' (ideleDiag K).range (ideleDiag K y) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 ⟨_, rfl⟩
    rw [map_sub, hz, sub_zero]
    rfl

end Hasse

/-! ### The short exact sequence -/

section SES

variable (k K : Type) [Field k] [Field K] [NumberField K] [Algebra k K]
  {p : ℕ} (hp : p.Prime)

include hp in
/-- **The passage to idele classes is surjective on the elements killed by a prime.** -/
theorem epi_ideleToIdeleClassTorsion : Epi (ideleToIdeleClassTorsion k K (p : ℤ)) :=
  (Rep.epi_iff_surjective _).2 fun c => by
    obtain ⟨x, hx, hxc⟩ := exists_torsion_idele_mk_eq hp c.1 (mem_torsionBy.1 c.2)
    exact ⟨⟨x, mem_torsionBy.2 hx⟩, Subtype.ext hxc⟩

include hp in
/-- **The elements killed by a prime of the units, of the ideles and of the idele classes form a
short exact sequence of representations of the Galois group.**  The principal ideles killed by the
prime are the roots of unity of the field, an idele killed by the prime is principal exactly when it
is the principal idele of such a root, and every class killed by the prime has a representative
killed by it. -/
theorem ideleClassTorsionShortComplex_shortExact :
    (ideleClassTorsionShortComplex k K (p : ℤ)).ShortExact where
  exact := (forget₂ _ (ModuleCat ℤ)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx => by
      obtain ⟨u, hu⟩ := (QuotientAddGroup.eq_zero_iff _).1 (congrArg Subtype.val hx)
      have h0 : (ideleDiag K) ((p : ℤ) • u) = 0 := by
        rw [map_zsmul, hu]
        exact mem_torsionBy.1 x.2
      exact ⟨⟨u, mem_torsionBy.2 (ideleDiag_injective K (h0.trans (map_zero _).symm))⟩,
        Subtype.ext hu⟩
  mono_f := (Rep.mono_iff_injective _).2
    (torsionHom_injective (p : ℤ) (ideleDiag K) (ideleDiag_injective K))
  epi_g := epi_ideleToIdeleClassTorsion k K hp

end SES

end InverseGalois.CFT
