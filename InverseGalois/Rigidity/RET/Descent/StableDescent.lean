/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Descent.BranchCycle
import InverseGalois.Rigidity.RET.Descent.Tower
import InverseGalois.Rigidity.RET.Descent.ConstantRealization

/-!
# The rigidity method over a number field

The descent `ℚ̄(T) → ℚ(T)` of `Descent.lean` needs the prescribed classes to be **rational**: the
branch-cycle formula twists the `i`-th class by the value `χ(e)` of the cyclotomic character, and
only a rational class absorbs every twist.  Many rigid class tuples are not rational — the
Mathieu groups `M₁₁` and `M₁₂` are the standard examples, where the rigid triple is stable only
under an index-two subgroup of the cyclotomic action.

This file performs the descent over the subgroup of the arithmetic fundamental group on which the
twist *is* absorbed.  Write

  `S = { e ∈ E | ∀ i, Cᵢ^{χ(e)} = Cᵢ }`,

the preimage under the cyclotomic character `χ : E → (ZMod M)ˣ` of the subgroup of units
stabilizing every prescribed class.  The geometric group `N` lies in `S` (roots of unity are
constants), the branch-cycle twist of any `e ∈ S` is again a rigid tuple in the prescribed classes,
so rigidity makes conjugation by `e` inner and centerlessness extends `φ : N ↠ G` to `ψ : S ↠ G`.
The constant field cut out by `S` is then a **number field** `K` over which `G` is a regular Galois
group (`exists_regular_over_constant_base`).

## Main results

* `Rigidity.RET.Descent.stabUnits` — the units of `ZMod M` fixing every prescribed class.
* `GeomTower.stab` — its preimage `S ≤ E` under the cyclotomic character.
* `GeomTower.exists_regular_numberField` — the descent over `S`.
* `Rigidity.RET.Descent.exists_regular_numberField_of_orbitRigid` — the rigidity method for class
  data every cyclotomic twist of which is rigid.
* `RigidityCertificateH.exists_regular_numberField` — the same for a certificate whose classes are
  stable only under a subgroup of the cyclotomic action.

The exponent bookkeeping is `exists_coprime_modEq`: geometry realizes the classes only up to a
coordinatewise twist by exponents coprime to the *element orders*, while a certificate's rigidity
clause is stated for exponents coprime to the *modulus*; lifting a unit of `ZMod d` to a unit of
`ZMod n` along `d ∣ n` reconciles the two.
-/

open Polynomial

namespace Rigidity.RET.Descent

/-! ## Cyclotomic exponents -/

/-- **Lifting a coprime exponent along a divisor.**  An exponent coprime to `d` agrees modulo `d`
with an exponent coprime to any multiple `n` of `d`. -/
theorem exists_coprime_modEq {d n : ℕ} [NeZero n] (hdn : d ∣ n) {u : ℕ} (hu : Nat.Coprime u d) :
    ∃ u' : ℕ, Nat.Coprime u' n ∧ u' ≡ u [MOD d] := by
  obtain ⟨w, hw⟩ := ZMod.unitsMap_surjective hdn (ZMod.unitOfCoprime u hu)
  refine ⟨(w : ZMod n).val, ZMod.val_coe_unit_coprime w, ?_⟩
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  have h1 : ((ZMod.unitsMap hdn w : (ZMod d)ˣ) : ZMod d) = ((u : ℕ) : ZMod d) := by
    rw [hw]; exact ZMod.coe_unitOfCoprime u hu
  rw [ZMod.natCast_val]
  simpa [ZMod.unitsMap_def] using h1

/-- **The cyclotomic power of a class only depends on the exponent modulo `M`**, provided the order
of the elements of the class divides `M`. -/
theorem powClass_congr_of_modEq {G : Type*} [Group G] {M : ℕ} {c : ConjClasses G}
    (hord : ∀ g : G, ConjClasses.mk g = c → orderOf g ∣ M) {a b : ℕ} (h : a ≡ b [MOD M]) :
    ConjClasses.powClass a c = ConjClasses.powClass b c := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep c
  show ConjClasses.powClass a (ConjClasses.mk g) = ConjClasses.powClass b (ConjClasses.mk g)
  rw [ConjClasses.powClass_mk, ConjClasses.powClass_mk]
  exact congrArg ConjClasses.mk (pow_eq_pow_iff_modEq.mpr (Nat.ModEq.of_dvd (hord g rfl) h))

/-- The exponent attached to a product of units is the product of the exponents, modulo `M`. -/
theorem val_mul_modEq {M : ℕ} [NeZero M] (u v : (ZMod M)ˣ) :
    ((u * v : (ZMod M)ˣ) : ZMod M).val ≡ (u : ZMod M).val * (v : ZMod M).val [MOD M] := by
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  push_cast
  simp [ZMod.natCast_val, ZMod.cast_id]

/-- The exponent attached to the identity unit is `1`, modulo `M`. -/
theorem val_one_modEq (M : ℕ) [NeZero M] : ((1 : (ZMod M)ˣ) : ZMod M).val ≡ 1 [MOD M] := by
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  simp [ZMod.natCast_val]

variable {G : Type} [Group G] [Finite G]

/-- **The cyclotomic stabilizer of a class tuple**: the units of `ZMod M` whose cyclotomic power
fixes every one of the classes `C₁,…,C_r`.  Because the order of every element of every class
divides `M`, the power `c ↦ c^u` depends only on `u` modulo `M`, so these units are closed under
multiplication and inversion. -/
def stabUnits {r M : ℕ} [NeZero M] (C : Fin r → ConjClasses G)
    (hord : ∀ (i : Fin r) (g : G), ConjClasses.mk g = C i → orderOf g ∣ M) :
    Subgroup (ZMod M)ˣ where
  carrier := {u | ∀ i, ConjClasses.powClass ((u : ZMod M).val) (C i) = C i}
  one_mem' := by
    intro i
    rw [powClass_congr_of_modEq (hord i) (val_one_modEq M), ConjClasses.powClass_one]
  mul_mem' := by
    intro u v hu hv i
    rw [powClass_congr_of_modEq (hord i) (val_mul_modEq u v),
      ← ConjClasses.powClass_powClass, hu i, hv i]
  inv_mem' := by
    intro u hu i
    have hkey := powClass_congr_of_modEq (hord i) (val_mul_modEq u u⁻¹)
    rw [mul_inv_cancel, ← ConjClasses.powClass_powClass, hu i] at hkey
    rw [← hkey, powClass_congr_of_modEq (hord i) (val_one_modEq M), ConjClasses.powClass_one]

omit [Finite G] in
theorem mem_stabUnits {r M : ℕ} [NeZero M] {C : Fin r → ConjClasses G}
    {hord : ∀ (i : Fin r) (g : G), ConjClasses.mk g = C i → orderOf g ∣ M} {u : (ZMod M)ˣ} :
    u ∈ stabUnits C hord ↔ ∀ i, ConjClasses.powClass ((u : ZMod M).val) (C i) = C i := Iff.rfl

end Rigidity.RET.Descent

/-! ## The descent over the stabilizing subgroup -/

open Rigidity.RET.Descent

namespace GeomTower

variable {G : Type} [Group G] [Finite G] {cert : RigidData G} (tw : GeomTower G cert)

/-- Every element of a prescribed class has order dividing the tower's cyclotomic modulus. -/
theorem order_dvd_rootOrder (i : Fin cert.r) (g : G) (hg : ConjClasses.mk g = cert.C i) :
    orderOf g ∣ tw.rootOrder := by
  rw [ConjClasses.orderOf_eq_of_mk_eq (hg.trans (tw.base_mem.1 i).symm)]
  exact tw.order_dvd i

/-- **The stabilizing subgroup of the arithmetic fundamental group**: the elements whose cyclotomic
twist fixes every prescribed class.  It is the preimage of `stabUnits` under the tower's cyclotomic
character, and it contains the geometric group `N`. -/
def stab : Subgroup tw.E :=
  (stabUnits cert.C tw.order_dvd_rootOrder).comap tw.cycloChar

theorem mem_stab {e : tw.E} :
    e ∈ tw.stab ↔
      ∀ i, ConjClasses.powClass ((tw.cycloChar e : ZMod tw.rootOrder).val) (cert.C i) = cert.C i :=
  Iff.rfl

/-- The geometric group acts trivially on roots of unity, so it stabilizes every class. -/
theorem N_le_stab : tw.N ≤ tw.stab := by
  intro x hx
  rw [mem_stab, tw.cycloChar_N ⟨x, hx⟩]
  intro i
  rw [powClass_congr_of_modEq (tw.order_dvd_rootOrder i) (val_one_modEq tw.rootOrder),
    ConjClasses.powClass_one]

/-- The geometric monodromy is surjective: the base tuple generates `G` and `φ` factors its sphere
hom through the presentation. -/
theorem surjφ : Function.Surjective tw.φ := by
  intro g
  obtain ⟨x, hx⟩ :=
    (Rigidity.RET.sphereHom_surjective_iff tw.base tw.base_mem.2.1).2 tw.base_mem.2.2 g
  exact ⟨tw.pres x, by rw [tw.φ_pres x, hx]⟩

/-- Conjugation by `e` is a bijection of the geometric group onto itself. -/
theorem conjN_surjective (e : tw.E) : Function.Surjective (Rigidity.RET.conjN tw.N e) := by
  intro n
  refine ⟨Rigidity.RET.conjN tw.N e⁻¹ n, ?_⟩
  apply Subtype.ext
  simp only [Rigidity.RET.conjN_coe]
  group

/-- **The branch-cycle twist by a stabilizing element is again a rigid tuple.**  Class membership is
the branch-cycle formula followed by stability; product-one and generation are elementary. -/
theorem branchTwistTuple_mem_of_stab {e : tw.E} (he : e ∈ tw.stab) :
    branchTwistTuple tw e ∈ rigidTuples cert.C := by
  refine ⟨fun i => ?_, branchTwistTuple_prod_one tw e, ?_⟩
  · show ConjClasses.mk (tw.φ (Rigidity.RET.conjN tw.N e (tw.pres (PresentedGroup.of i))))
      = cert.C i
    rw [tw.branchCycleχ e i]
    exact (mem_stab tw).mp he i
  · rw [← Rigidity.RET.sphereHom_surjective_iff (branchTwistTuple tw e)
      (branchTwistTuple_prod_one tw e)]
    have hfun : ⇑(Rigidity.RET.sphereHom (branchTwistTuple tw e) (branchTwistTuple_prod_one tw e))
        = fun x => tw.φ (Rigidity.RET.conjN tw.N e (tw.pres x)) := by
      funext x; exact (branchTwistTuple_φ_conj_pres tw e x).symm
    rw [hfun]
    intro g
    obtain ⟨n, hn⟩ := tw.surjφ g
    obtain ⟨m, hm⟩ := tw.conjN_surjective e n
    obtain ⟨x, hx⟩ := tw.surjPres m
    exact ⟨x, by
      show tw.φ (Rigidity.RET.conjN tw.N e (tw.pres x)) = g
      rw [hx, hm, hn]⟩

/-- **Rigidity makes the twist inner.**  For a stabilizing `e`, the branch-cycle twist and the
original monodromy tuple both lie in `rigidTuples C`, hence are simultaneously conjugate; so
conjugation by `e` acts on `G` through an inner automorphism. -/
theorem inner_of_stab {e : tw.E} (he : e ∈ tw.stab) :
    ∃ c : G, ∀ n : tw.N, tw.φ (Rigidity.RET.conjN tw.N e n) = c * tw.φ n * c⁻¹ := by
  have hZ : Subgroup.center G = ⊥ := center_triv_iff_center_eq_bot.mp cert.center_triv
  have hmem := tw.branchTwistTuple_mem_of_stab he
  obtain ⟨c, hc⟩ := Rigidity.RET.sphereHom_inner_equiv_of_rigid hZ cert.rigid
    tw.base_mem hmem tw.base_mem.2.1 hmem.2.1
  refine ⟨c, fun n => ?_⟩
  obtain ⟨x, rfl⟩ := tw.surjPres n
  have h1 : tw.φ (Rigidity.RET.conjN tw.N e (tw.pres x))
      = Rigidity.RET.sphereHom (branchTwistTuple tw e) hmem.2.1 x :=
    branchTwistTuple_φ_conj_pres tw e x
  have hcx := DFunLike.congr_fun hc x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hcx
  rw [h1, hcx, tw.φ_pres x]

/-- **The arithmetic monodromy over the stabilizing subgroup.**  Centerlessness plus the inner
property extend the geometric monodromy `φ : N ↠ G` to a surjection `ψ : S ↠ G` restricting to `φ`
on `N`. -/
theorem exists_psi :
    ∃ ψ : tw.stab →* G, Function.Surjective ψ ∧
      ∀ n : tw.N, ψ ⟨(n : tw.E), tw.N_le_stab n.2⟩ = tw.φ n := by
  have hZ : Subgroup.center G = ⊥ := center_triv_iff_center_eq_bot.mp cert.center_triv
  obtain ⟨ψ, hψsurj, hψext⟩ :=
    Rigidity.RET.extend_surjective_of_inner (tw.N.subgroupOf tw.stab)
      (tw.φ.comp (Subgroup.subgroupOfEquivOfLe tw.N_le_stab).toMonoidHom)
      (tw.surjφ.comp (Subgroup.subgroupOfEquivOfLe tw.N_le_stab).surjective) hZ
      (fun e => (tw.inner_of_stab e.2).imp fun _ hc m =>
        hc (Subgroup.subgroupOfEquivOfLe tw.N_le_stab m))
  exact ⟨ψ, hψsurj, fun n => hψext ⟨⟨(n : tw.E), tw.N_le_stab n.2⟩, n.2⟩⟩

/-- **The rigidity method over a number field, from a geometric tower.**  If the prescribed classes
are stable under the cyclotomic twist by every element of a subgroup `S ≤ E` containing the
geometric group, then `G` is a regular Galois group over `K(T)` for the number field `K` of
constants cut out by `S`. -/
theorem exists_regular_numberField :
    ∃ K : IntermediateField ℚ tw.Ω, K ≤ algebraicClosure ℚ tw.Ω ∧
      IsRegularGaloisGroupOver ↥K G := by
  classical
  obtain ⟨ψS, hψsurj, hψext⟩ := tw.exists_psi
  -- transport the stabilizing subgroup to the Galois group of `Ω / ℚ(T)`.
  set eG : tw.stab ≃* (tw.stab.map (tw.galE : tw.E →* (tw.Ω ≃ₐ[RatFunc ℚ] tw.Ω))) :=
    tw.galE.subgroupMap tw.stab with heG
  refine exists_regular_over_constant_base tw.Ω
    (E' := tw.stab.map (tw.galE : tw.E →* (tw.Ω ≃ₐ[RatFunc ℚ] tw.Ω))) ?_
    (ψS.comp eG.symm.toMonoidHom) (hψsurj.comp eG.symm.surjective) ?_
  -- the geometric group is contained in the stabilizing subgroup.
  · intro σ hσ
    have hmem : tw.galE.symm σ ∈ tw.N := by
      rw [tw.galN_iff, MulEquiv.apply_symm_apply, tw.geomBase_eq_constFieldBase]
      exact hσ
    exact Subgroup.mem_map.mpr
      ⟨tw.galE.symm σ, tw.N_le_stab hmem, tw.galE.apply_symm_apply σ⟩
  -- every element of `G` is already hit by the geometric part.
  · intro g
    obtain ⟨n, hn⟩ := tw.surjφ g
    refine ⟨eG ⟨(n : tw.E), tw.N_le_stab n.2⟩, ?_, ?_⟩
    · show tw.galE (n : tw.E) ∈ (constFieldBase tw.Ω).fixingSubgroup
      rw [← tw.geomBase_eq_constFieldBase, ← tw.galN_iff]
      exact n.2
    · show ψS (eG.symm (eG ⟨(n : tw.E), tw.N_le_stab n.2⟩)) = g
      rw [eG.symm_apply_apply, hψext n, hn]

end GeomTower

/-! ## The rigidity method for orbit-rigid class data -/

namespace Rigidity.RET.Descent

variable {G : Type} [Group G] [Finite G]

/-- **The rigidity method over a number field.**

A centerless group with a generating product-one class tuple `C₁,…,C_r` every cyclotomic twist of
which is rigid is a **regular** Galois group — not necessarily over `ℚ(T)`, but over `K(T)` for some
number field `K`.  The classes are *not* required to be rational: the descent runs over the subgroup
of the arithmetic fundamental group whose cyclotomic twist fixes the classes it is presented with,
and `K` is the constant field that subgroup cuts out.

Geometry realizes the classes only up to a coordinatewise cyclotomic twist by exponents coprime to
the element orders (`geomTower_nonempty_twist`); `exists_coprime_modEq` replaces those exponents by
exponents coprime to the modulus `n`, at which `horbit` applies.  Over the resulting tower the
descent is `GeomTower.exists_regular_numberField`. -/
theorem exists_regular_numberField_of_orbitRigid {r n : ℕ} [NeZero n] (C : Fin r → ConjClasses G)
    (hcenter : ∀ g : G, g ∈ Subgroup.center G → g = 1)
    (hord : ∀ (i : Fin r) (g : G), ConjClasses.mk g = C i → orderOf g ∣ n)
    (hgen : (rigidTuples C).Nonempty)
    (horbit : ∀ u : Fin r → ℕ, (∀ i, Nat.Coprime (u i) n) →
      Nat.card (rigidTuples fun i => ConjClasses.powClass (u i) (C i)) = Nat.card G) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), IsRegularGaloisGroupOver K G := by
  classical
  let rd : RigidData G :=
    { r := r, C := C, center_triv := hcenter, gen := hgen
      rigid := by simpa using horbit (fun _ => 1) fun _ => Nat.coprime_one_left n }
  obtain ⟨u, hcop, htw⟩ := geomTower_nonempty_twist rd
  -- Replace the geometric exponents by exponents coprime to the modulus.
  have hstep : ∀ i : Fin r, ∃ u' : ℕ, Nat.Coprime u' n ∧
      ConjClasses.powClass u' (C i) = ConjClasses.powClass (u i) (C i) := by
    intro i
    obtain ⟨g, hg⟩ := Quotient.exists_rep (C i)
    have hgmk : ConjClasses.mk g = C i := hg
    obtain ⟨u', hu'cop, hu'mod⟩ := exists_coprime_modEq (hord i g hgmk) (hcop i g hgmk)
    exact ⟨u', hu'cop, powClass_congr_of_modEq (M := orderOf g)
      (fun x hx => (ConjClasses.orderOf_eq_of_mk_eq (hx.trans hgmk.symm)).dvd) hu'mod⟩
  choose u' hu'cop hu'eq using hstep
  have hrig : Nat.card (rigidTuples fun i => ConjClasses.powClass (u i) (rd.C i))
      = Nat.card G := by
    rw [show (fun i => ConjClasses.powClass (u i) (rd.C i))
        = fun i => ConjClasses.powClass (u' i) (C i) from funext fun i => (hu'eq i).symm]
    exact horbit u' hu'cop
  obtain ⟨tw⟩ := htw hrig
  obtain ⟨K, hKac, hreg⟩ := tw.exists_regular_numberField
  haveI : FiniteDimensional ℚ ↥K :=
    Module.Finite.of_injective (IntermediateField.inclusion hKac).toLinearMap
      (IntermediateField.inclusion hKac).toRingHom.injective
  haveI : NumberField ↥K := ⟨⟩
  exact ⟨↥K, inferInstance, inferInstance, hreg⟩

end Rigidity.RET.Descent

/-- **The rigidity method over a number field, from a subgroup-stable certificate.**  A certificate
whose classes are stable only under a subgroup `H` of the cyclotomic action realizes `G` regularly
over a number field. -/
theorem RigidityCertificateH.exists_regular_numberField {G : Type} [Group G] [Finite G] {n : ℕ}
    [NeZero n] {H : Subgroup (ZMod n)ˣ} (certH : RigidityCertificateH G n H) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), IsRegularGaloisGroupOver K G :=
  Rigidity.RET.Descent.exists_regular_numberField_of_orbitRigid certH.C certH.center_triv
    certH.order_dvd certH.gen certH.orbitRigid
