/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.FixingSubgroup
import InverseGalois.CFT.Profinite.H1Conj
import InverseGalois.CFT.Profinite.Krull
import InverseGalois.CFT.Profinite.KummerHom

/-!
# The Kummer classes of an intermediate field are equivariant for the base

Let `Ω` be a Galois extension of `k` and let `K` be an intermediate field, normal over the base.
The subgroup of the Galois group which fixes `K` is normal, and Kummer theory over `K` attaches to
every unit of `K` a class in the first cohomology of that subgroup with coefficients in the roots
of unity.  Both sides carry an action of the Galois group of the base: it acts on the units of `K`
by restriction, and on the cohomology of the subgroup by conjugation.

**Those two actions agree.**  The reason is that the Kummer cochain is characterised, and not
merely constructed: it is the only cochain whose image in the units of the extension is the
coboundary of an `n`-th root.  Conjugating the cochain of a unit is the cochain built from the
conjugate of the chosen root, which is a root of the conjugate unit, so the two coincide before any
class is taken.  The one arithmetic input is that the base contains the roots of unity, which is
what makes an automorphism of the extension over the base fix the coefficients inside it.

## Main definitions

* `InverseGalois.CFT.kummerSubCochain`: the Kummer cochain of a unit of the intermediate field,
  read on the subgroup fixing that field.
* `InverseGalois.CFT.kummerSubClass`: its class in the first cohomology of that subgroup.
* `InverseGalois.CFT.kummerSubHom`: the Kummer homomorphism read on that subgroup.
* `InverseGalois.CFT.kummerSubEquiv`: **the Kummer isomorphism** read on that subgroup.

## Main results

* `InverseGalois.CFT.kummerSubCochain_smul`: **the Kummer cochain of a conjugated unit is the
  conjugate of the Kummer cochain.**
* `InverseGalois.CFT.kummerSubCochain_eq_conjCochain`: the same, read as the conjugation of
  cochains.
* `InverseGalois.CFT.conjH1_kummerSubClass`: **the Kummer classes are equivariant** for the
  conjugation action of the Galois group of the base.
* `InverseGalois.CFT.ker_kummerSubHom`: the kernel of the Kummer homomorphism read on the subgroup
  is the group of `n`-th powers.
* `InverseGalois.CFT.kummerSubHom_surjective`: that homomorphism is surjective.

## Tags

Kummer theory, infinite Galois theory, root of unity, Galois cohomology, conjugation
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IntermediateField groupCohomology

section Kummer

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K : IntermediateField k Ω}
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M] {ι : M →* (↥K)ˣ}
variable {n : ℕ} [NeZero n]

omit [IsGalois k Ω] in
/-- An element of the subgroup fixing an intermediate field acts on the extension as the
automorphism over that field which it defines. -/
theorem fixingSubgroupEquiv_smul (x : ↥K.fixingSubgroup) (β : Ωˣ) :
    (fixingSubgroupEquiv K x) • β = (x : Gal(Ω/k)) • β := rfl

omit [IsGalois k Ω] in
/-- An automorphism of the extension over the base acts on a unit of a normal intermediate field
through its restriction to that field. -/
theorem smul_units_algebraMap_intermediateField [Normal k ↥K] (σ : Gal(Ω/k)) (a : (↥K)ˣ) :
    σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) a
      = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (AlgEquiv.restrictNormalHom (↥K) σ • a) :=
  Units.ext (AlgEquiv.restrictNormal_commutes σ (↥K) (a : ↥K)).symm

/-- **The Kummer cochain of a unit of an intermediate field**, read on the subgroup of the Galois
group of the base which fixes that field. -/
noncomputable def kummerSubCochain (h : IsKummerData ↥K Ω M ι n) (a : (↥K)ˣ) :
    ↥K.fixingSubgroup → M := fun x => h.cochain a (fixingSubgroupEquiv K x)

/-- The image of the Kummer cochain is the coboundary of the chosen root. -/
theorem kummerSubCochain_spec (h : IsKummerData ↥K Ω M ι n) (a : (↥K)ˣ)
    (x : ↥K.fixingSubgroup) :
    Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι (kummerSubCochain h a x))
      = (x : Gal(Ω/k)) • h.root a / h.root a := h.cochain_spec a _

/-- **The Kummer cochain is smooth**, because the chosen root is fixed by an open normal subgroup
of the Galois group of the base. -/
theorem isSmooth₁_kummerSubCochain (h : IsKummerData ↥K Ω M ι n) (a : (↥K)ˣ) :
    IsSmooth₁ (kummerSubCochain h a) := by
  obtain ⟨R, hR, hfix⟩ := exists_isOpenNormal_forall_smul_eq (k := k) (h.root a)
  refine ⟨R.comap (K.fixingSubgroup).subtype, isOpenNormal_comap_subtype _ hR, fun x r hr => ?_⟩
  refine injective_units_algebraMap_comp (Ω := Ω) h.injective ?_
  show Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι (kummerSubCochain h a (x * r)))
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι (kummerSubCochain h a x))
  rw [kummerSubCochain_spec, kummerSubCochain_spec]
  congr 1
  have hrr : (r : Gal(Ω/k)) • h.root a = h.root a := hfix _ (Subgroup.mem_comap.1 hr)
  show ((x : Gal(Ω/k)) * (r : Gal(Ω/k))) • h.root a = (x : Gal(Ω/k)) • h.root a
  rw [mul_smul, hrr]

variable [MulDistribMulAction Gal(Ω/k) M]

/-- **The Kummer cochain is a one cocycle** for the action of the subgroup fixing the intermediate
field, which is trivial on the roots of unity. -/
theorem isMulCocycle₁_kummerSubCochain (h : IsKummerData ↥K Ω M ι n)
    (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) (a : (↥K)ˣ) :
    IsMulCocycle₁ (kummerSubCochain h a) := by
  intro x y
  show h.cochain a (fixingSubgroupEquiv K (x * y))
    = (x : Gal(Ω/k)) • h.cochain a (fixingSubgroupEquiv K y) * h.cochain a (fixingSubgroupEquiv K x)
  rw [htriv, map_mul, h.cochain_isMulCocycle₁ a, h.smul_eq]

/-- **The Kummer class of a unit of an intermediate field**, in the first cohomology of the
subgroup of the Galois group of the base which fixes that field. -/
noncomputable def kummerSubClass (h : IsKummerData ↥K Ω M ι n)
    (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) (a : (↥K)ˣ) :
    SmoothH1 ↥K.fixingSubgroup M :=
  smoothH1Mk (kummerSubCochain h a) (isMulCocycle₁_kummerSubCochain h htriv a)
    (isSmooth₁_kummerSubCochain h a)

/-! ### Equivariance -/

variable [Normal k ↥K]

omit [MulDistribMulAction Gal(Ω/k) M] in
/-- **The Kummer cochain of a conjugated unit is the conjugate of the Kummer cochain.**  Both are
the cochain built from the conjugate of the chosen root, which is a root of the conjugate unit; the
hypothesis is that an automorphism over the base fixes the roots of unity, so that conjugating does
not disturb the coefficients. -/
theorem kummerSubCochain_smul (h : IsKummerData ↥K Ω M ι n)
    (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
      σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
        = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
    (σ : Gal(Ω/k)) (a : (↥K)ˣ) (x : ↥K.fixingSubgroup) :
    kummerSubCochain h (AlgEquiv.restrictNormalHom (↥K) σ • a) x
      = kummerSubCochain h a (conjMemHom (normal_fixingSubgroup K) σ x) := by
  have key : (fun τ : Gal(Ω/↥K) => h.cochain a (fixingSubgroupEquiv K
      (conjMemHom (normal_fixingSubgroup K) σ ((fixingSubgroupEquiv K).symm τ))))
      = h.cochain (AlgEquiv.restrictNormalHom (↥K) σ • a) := by
    refine h.cochain_unique _ (β := σ • h.root a) ?_ ?_
    · rw [← smul_pow', h.root_pow, smul_units_algebraMap_intermediateField]
    · intro τ
      refine (hfix σ _).symm.trans ?_
      rw [h.cochain_spec, smul_div']
      congr 1
      show σ • ((σ⁻¹ * ((fixingSubgroupEquiv K).symm τ : Gal(Ω/k)) * σ) • h.root a)
        = τ • (σ • h.root a)
      rw [← mul_smul,
        show σ * (σ⁻¹ * ((fixingSubgroupEquiv K).symm τ : Gal(Ω/k)) * σ)
          = ((fixingSubgroupEquiv K).symm τ : Gal(Ω/k)) * σ by group, mul_smul]
      rfl
  exact (congrFun key (fixingSubgroupEquiv K x)).symm

/-- **The Kummer cochain of a conjugated unit is the conjugate of the Kummer cochain**, read as an
equality of cochains on the subgroup fixing the intermediate field. -/
theorem kummerSubCochain_eq_conjCochain (h : IsKummerData ↥K Ω M ι n)
    (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
      σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
        = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
    (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) (σ : Gal(Ω/k)) (a : (↥K)ˣ) :
    kummerSubCochain h (AlgEquiv.restrictNormalHom (↥K) σ • a)
      = conjCochain (normal_fixingSubgroup K) σ (kummerSubCochain h a) := by
  funext x
  rw [conjCochain_apply, htriv]
  exact kummerSubCochain_smul h hfix σ a x

/-- **The Kummer classes of an intermediate field are equivariant**: the class of a conjugated unit
is the conjugate of the class. -/
theorem conjH1_kummerSubClass (h : IsKummerData ↥K Ω M ι n)
    (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
      σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
        = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
    (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) (σ : Gal(Ω/k)) (a : (↥K)ˣ) :
    conjH1 (normal_fixingSubgroup K) σ (kummerSubClass h htriv a)
      = kummerSubClass h htriv (AlgEquiv.restrictNormalHom (↥K) σ • a) := by
  refine Eq.trans (conjH1_smoothH1Mk (normal_fixingSubgroup K) σ
    (isMulCocycle₁_kummerSubCochain h htriv a) (isSmooth₁_kummerSubCochain h a)) ?_
  exact smoothH1Mk_congr (kummerSubCochain_eq_conjCochain h hfix htriv σ a).symm
    (isMulCocycle₁_conjCochain (normal_fixingSubgroup K)
      (isMulCocycle₁_kummerSubCochain h htriv a) σ)
    (isSmooth₁_conjCochain (normal_fixingSubgroup K) (isSmooth₁_kummerSubCochain h a) σ)
    (isMulCocycle₁_kummerSubCochain h htriv _) (isSmooth₁_kummerSubCochain h _)

end Kummer

/-! ### The Kummer isomorphism in the subgroup picture -/

section Iso

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K : IntermediateField k Ω}
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M] {ι : M →* (↥K)ˣ}
variable {n : ℕ} [NeZero n] [MulDistribMulAction Gal(Ω/k) M]

omit [IsGalois k Ω] [NeZero n] in
/-- The subgroup fixing an intermediate field acts on the roots of unity in the two available ways,
through the Galois group of the base and through the Galois group over the field, and both actions
are trivial. -/
theorem smul_eq_smul_fixingSubgroupEquiv (h : IsKummerData ↥K Ω M ι n)
    (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) (x : ↥K.fixingSubgroup) (m : M) :
    x • m = fixingSubgroupEquiv K x • m := by
  rw [h.smul_eq]
  exact htriv (x : Gal(Ω/k)) m

/-- The first cohomology of the Galois group over an intermediate field, read on the subgroup of
the Galois group of the base which fixes that field. -/
noncomputable def kummerSubCongr (h : IsKummerData ↥K Ω M ι n)
    (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) :
    SmoothH1 Gal(Ω/↥K) M ≃* SmoothH1 ↥K.fixingSubgroup M :=
  smoothH1Congr (fixingSubgroupEquiv K) (smul_eq_smul_fixingSubgroupEquiv h htriv)
    (isSmoothHom_fixingSubgroupEquiv K) (isSmoothHom_fixingSubgroupEquiv_symm K)

/-- **The Kummer homomorphism of an intermediate field, in the subgroup picture**: a unit of the
field goes to the class of its Kummer cochain in the first cohomology of the subgroup of the Galois
group of the base which fixes that field. -/
noncomputable def kummerSubHom (h : IsKummerData ↥K Ω M ι n)
    (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) : (↥K)ˣ →* SmoothH1 ↥K.fixingSubgroup M :=
  (kummerSubCongr h htriv).toMonoidHom.comp h.kummerHom

/-- The Kummer homomorphism in the subgroup picture takes a unit to its Kummer class. -/
theorem kummerSubHom_apply (h : IsKummerData ↥K Ω M ι n)
    (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) (a : (↥K)ˣ) :
    kummerSubHom h htriv a = kummerSubClass h htriv a := rfl

/-- **The kernel of the Kummer homomorphism in the subgroup picture is the group of `n`-th
powers.** -/
theorem ker_kummerSubHom (h : IsKummerData ↥K Ω M ι n)
    (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) :
    (kummerSubHom h htriv).ker = (powMonoidHom n : (↥K)ˣ →* (↥K)ˣ).range := by
  ext a
  rw [MonoidHom.mem_ker, ← h.ker_kummerHom, MonoidHom.mem_ker]
  exact (kummerSubCongr h htriv).map_eq_one_iff

/-- **The Kummer homomorphism in the subgroup picture is surjective.** -/
theorem kummerSubHom_surjective (h : IsKummerData ↥K Ω M ι n)
    (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) :
    Function.Surjective (kummerSubHom h htriv) := by
  intro x
  obtain ⟨y, hy⟩ := EquivLike.surjective (kummerSubCongr h htriv) x
  obtain ⟨a, ha⟩ := h.kummerHom_surjective y
  refine ⟨a, ?_⟩
  show kummerSubCongr h htriv (h.kummerHom a) = x
  rw [ha, hy]

/-- **The Kummer isomorphism of an intermediate field, in the subgroup picture**: the units of the
field modulo the `n`-th powers are the first cohomology of the subgroup of the Galois group of the
base which fixes that field. -/
noncomputable def kummerSubEquiv (h : IsKummerData ↥K Ω M ι n)
    (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) :
    (↥K)ˣ ⧸ (powMonoidHom n : (↥K)ˣ →* (↥K)ˣ).range ≃* SmoothH1 ↥K.fixingSubgroup M :=
  (QuotientGroup.quotientMulEquivOfEq (ker_kummerSubHom h htriv).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (kummerSubHom_surjective h htriv))

/-- **The Kummer homomorphism in the subgroup picture is equivariant** for the Galois group of the
base, acting on the units of a normal intermediate field by restriction and on the cohomology of
the subgroup which fixes it by conjugation. -/
theorem conjH1_kummerSubHom [Normal k ↥K] (h : IsKummerData ↥K Ω M ι n)
    (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
      σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
        = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
    (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m) (σ : Gal(Ω/k)) (a : (↥K)ˣ) :
    conjH1 (normal_fixingSubgroup K) σ (kummerSubHom h htriv a)
      = kummerSubHom h htriv (AlgEquiv.restrictNormalHom (↥K) σ • a) :=
  conjH1_kummerSubClass h hfix htriv σ a

end Iso

end InverseGalois.CFT
