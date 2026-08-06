/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Statement
import InverseGalois.Rigidity.RET.CenterlessExtension
import InverseGalois.Rigidity.RET.BranchCycleBridge
import InverseGalois.Rigidity.StructureConstant

/-!
# Descent data structures — the frozen interface of the branch-cycle descent

This file holds the **data structures** of the branch-cycle rationality descent, with **no
`sorry`**.  It is the frozen interface that the four descent modules (`Descent.Tower`,
`Descent.BranchCycle`, `Descent.FieldTranslation`, and the assembly in `Descent`) share.  Splitting
these definitions out of `Descent.lean` breaks the import cycle: the modules that *produce*
inhabitants import this file, and `Descent.lean` imports the modules.

See `DESCENT_ROADMAP.md` for the mathematics and the module breakdown.

## Contents

* `ArithmeticDescentData` — the pre-digested descent datum (`inner`/`surjφ` assumed).
* `BranchCycleDescentData` — the sharpened, primitive branch-cycle datum.
* `ArithmeticDescentData.ofBranchCycle` — derives the former from the latter (`inner`/`surjφ`
  become theorems via the structure-constant machinery).
* `GeomTower` — the **geometric side** of the descent datum: the arithmetic fundamental-group tower
  `N ⊴ E`, the monodromy `φ`, and its geometric presentation as the certificate's rigid tuple.  This
  is the shared carrier produced by Modules A+B (`Descent.Tower`).
* `BranchTwist` — Module C's output over a `GeomTower`: the Galois-twist tuples, their
  class-membership, and the twisted-monodromy identity.
-/

open Polynomial

/-- The irreducible **arithmetic** input of the branch-cycle descent, packaged as a structure so
that the genuine, axiom-free group-theoretic assembly is cleanly separated from the Mathlib-absent
arithmetic geometry.  An inhabitant bundles:

* the arithmetic fundamental-group tower `N = Gal(Ω/ℚ̄(T)) ⊴ E = Gal(Ω/ℚ(T))`;
* the geometric monodromy `φ : N ↠ G`;
* the **branch-cycle + rationality + rigidity** consequence that conjugation by every `e ∈ E` is an
  *inner* automorphism through `φ` (the group-theoretic content of this step is proved, axiom-free,
  in `Rigidity.RET.sphereHom_inner_equiv_of_rigid` / `Rigidity.exists_pointwise_conj_of_rigid`,
  once the branch-cycle formula exhibits the Galois twist as another tuple in `rigidTuples C`);
* the **field translation** `toRegular`, carrying an arithmetic monodromy `ψ : E ↠ G` extending `φ`
  to a *regular* `ℚ(T)`-extension realizing `G`. -/
structure ArithmeticDescentData (G : Type) [Group G] where
  /-- the arithmetic fundamental group `E = Gal(Ω/ℚ(T))`. -/
  E : Type
  [groupE : Group E]
  /-- the geometric fundamental group `N = Gal(Ω/ℚ̄(T)) ⊴ E`. -/
  N : Subgroup E
  [normalN : N.Normal]
  /-- the geometric monodromy `φ : N ↠ G`. -/
  φ : N →* G
  /-- the geometric monodromy is surjective (the cover is connected with deck group `G`). -/
  surjφ : Function.Surjective φ
  /-- branch-cycle + rationality + rigidity: conjugation by every `e ∈ E` is inner through `φ`. -/
  inner : ∀ e : E, ∃ c : G, ∀ n : N, φ (Rigidity.RET.conjN N e n) = c * φ n * c⁻¹
  /-- field translation: an arithmetic monodromy `ψ : E ↠ G` extending `φ` yields a regular
  `ℚ(T)`-extension realizing `G`. -/
  toRegular : (∃ ψ : E →* G, Function.Surjective ψ ∧ ∀ n : N, ψ (n : E) = φ n) →
    IsRegularInverseGalois G

/-- The **sharpened** arithmetic input of the descent, stated in the *primitive* branch-cycle form
rather than the pre-digested `inner` form of `ArithmeticDescentData`.  Instead of assuming outright
that conjugation by every `e : E` is inner through `φ` (which is already the group-theoretic *payoff*
of rigidity), this structure exposes the concrete tuples and lets the payoff be **proved** from the
already-verified structure-constant machinery (`ArithmeticDescentData.ofBranchCycle`).

It bundles:

* the arithmetic fundamental-group tower `N = Gal(Ω/ℚ̄(T)) ⊴ E = Gal(Ω/ℚ(T))` and the geometric
  monodromy `φ : N →* G`;
* the **geometric presentation** `pres : SphereGroup r ↠ N` — the algebraic geometric `π₁` of the
  `r`-punctured line — realizing `φ` as the sphere hom of the certificate's rigid tuple `base`
  (`φ_pres`);
* the **branch-cycle + rationality** datum: for each `e : E`, the Galois twist of the monodromy is
  again a tuple `twist e` in the *same* rational classes, i.e. `twist e ∈ rigidTuples C`
  (`twist_mem`), and the twisted monodromy `φ ∘ conj e` is its sphere hom (`φ_conj_pres`);
* the **field translation** `toRegular`.

Everything previously assumed as `inner` (and even `surjφ`) is now *derived*
(`ArithmeticDescentData.ofBranchCycle`) via `Rigidity.RET.sphereHom_inner_equiv_of_rigid` and
`Rigidity.RET.sphereHom_surjective_iff` — so the proven `StructureConstant`/`BranchCycleBridge`
machinery is load-bearing, and the residual arithmetic assumption is strictly the recognizable
geometry (the presentation, the branch-cycle class-invariance, and the field translation), not the
group-theoretic conclusion. -/
structure BranchCycleDescentData (G : Type) [Group G] [Finite G]
    (cert : RigidityCertificate G) where
  /-- the arithmetic fundamental group `E = Gal(Ω/ℚ(T))`. -/
  E : Type
  [groupE : Group E]
  /-- the geometric fundamental group `N = Gal(Ω/ℚ̄(T)) ⊴ E`. -/
  N : Subgroup E
  [normalN : N.Normal]
  /-- the geometric monodromy `φ : N →* G`. -/
  φ : N →* G
  /-- the geometric presentation `SphereGroup r ↠ N` (the algebraic geometric `π₁`). -/
  pres : Rigidity.RET.SphereGroup cert.r →* N
  /-- the geometric presentation is surjective. -/
  surjPres : Function.Surjective pres
  /-- the geometric monodromy tuple: the certificate's rigid generating product-one tuple. -/
  base : Fin cert.r → G
  /-- the base tuple is a rigid tuple in the prescribed classes. -/
  base_mem : base ∈ rigidTuples cert.C
  /-- `φ` is the sphere hom of the rigid tuple `base`, read through the presentation. -/
  φ_pres : ∀ x : Rigidity.RET.SphereGroup cert.r,
    φ (pres x) = Rigidity.RET.sphereHom base base_mem.2.1 x
  /-- the Galois twist of the monodromy by `e : E`, as a tuple. -/
  twist : E → (Fin cert.r → G)
  /-- **branch-cycle + rationality**: each Galois twist stays in the prescribed rational classes. -/
  twist_mem : ∀ e, twist e ∈ rigidTuples cert.C
  /-- the twisted monodromy `φ ∘ conj e` is the sphere hom of `twist e`, through the presentation. -/
  φ_conj_pres : ∀ (e : E) (x : Rigidity.RET.SphereGroup cert.r),
    φ (Rigidity.RET.conjN N e (pres x)) = Rigidity.RET.sphereHom (twist e) (twist_mem e).2.1 x
  /-- field translation: an arithmetic monodromy `ψ : E ↠ G` extending `φ` yields a regular
  `ℚ(T)`-extension realizing `G`. -/
  toRegular : (∃ ψ : E →* G, Function.Surjective ψ ∧ ∀ n : N, ψ (n : E) = φ n) →
    IsRegularInverseGalois G

/-- **The genuine descent: `inner` (and surjectivity) are theorems, not assumptions.**  From the
primitive branch-cycle datum, the pre-digested `ArithmeticDescentData` is *constructed*: the
inner-automorphism property is discharged by `Rigidity.RET.sphereHom_inner_equiv_of_rigid` (rigidity
forces the branch-cycle twist to be simultaneously conjugate to the base tuple), and surjectivity of
`φ` by `Rigidity.RET.sphereHom_surjective_iff` (the base tuple generates).  This is exactly the point
where the proven structure-constant machinery does the work the old `inner` field merely assumed. -/
noncomputable def ArithmeticDescentData.ofBranchCycle {G : Type} [Group G] [Finite G]
    {cert : RigidityCertificate G} (bcd : BranchCycleDescentData G cert) :
    ArithmeticDescentData G where
  E := bcd.E
  groupE := bcd.groupE
  N := bcd.N
  normalN := bcd.normalN
  φ := bcd.φ
  surjφ := by
    letI := bcd.groupE
    intro g
    have hsurj : Function.Surjective (Rigidity.RET.sphereHom bcd.base bcd.base_mem.2.1) :=
      (Rigidity.RET.sphereHom_surjective_iff bcd.base bcd.base_mem.2.1).2 bcd.base_mem.2.2
    obtain ⟨x, hx⟩ := hsurj g
    exact ⟨bcd.pres x, by rw [bcd.φ_pres x, hx]⟩
  inner := by
    letI := bcd.groupE
    letI := bcd.normalN
    intro e
    have hZ : Subgroup.center G = ⊥ := center_triv_iff_center_eq_bot.mp cert.center_triv
    obtain ⟨c, hc⟩ := Rigidity.RET.sphereHom_inner_equiv_of_rigid hZ cert.rigid
      bcd.base_mem (bcd.twist_mem e) bcd.base_mem.2.1 (bcd.twist_mem e).2.1
    refine ⟨c, fun n => ?_⟩
    obtain ⟨x, rfl⟩ := bcd.surjPres n
    rw [bcd.φ_conj_pres e x]
    have hcx := DFunLike.congr_fun hc x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hcx
    rw [hcx, bcd.φ_pres x]
  toRegular := bcd.toRegular

/-- **The geometric side of the descent datum** — the shared carrier produced by Modules A+B
(`Descent.Tower`).  It is `BranchCycleDescentData` *without* the branch-cycle twist data
(`twist`/`twist_mem`/`φ_conj_pres`) and *without* the field translation (`toRegular`): purely the
arithmetic fundamental-group tower `N ⊴ E`, the geometric monodromy `φ : N →* G`, and its geometric
presentation `pres : SphereGroup r ↠ N` realizing `φ` as the sphere hom of the certificate's rigid
tuple `base`.

Producing a `GeomTower` is the content of **Module A** (the field tower `ℚ(T) ⊂ ℚ̄(T) ⊂ Ω` and the
fundamental exact sequence `1 → N → E → Gal(ℚ̄/ℚ) → 1`) together with **Module B** (the geometric
`π₁` presentation, i.e. the Riemann Existence Theorem at the `N` level).  See `Descent.Tower`.

## The field realization *(the enrichment)*

The tower does **not** carry the groups `E, N` abstractly only: it carries the actual **field
realization** — the finite Galois extension `Ω/ℚ(T)`, the identification `E ≃* Gal(Ω/ℚ(T))`, and the
geometric base `ℚ̄(T)` realized as an intermediate field `geomBase` with `N` its fixing subgroup.
This is what lets **Module D** (`descentTranslation`) actually *build a field* (`fixedField (ker ψ)`)
and prove it regular; you cannot produce a field from abstract groups.  The three field-theoretic
facts D consumes are:

* `galE` — `E` is the Galois group `Gal(Ω/ℚ(T))`;
* `galN_iff` — `N` is `Gal(Ω/ℚ̄(T))`, i.e. the fixing subgroup of `geomBase`, transported by `galE`;
* `const_le_geomBase` — the geometric base contains **all constants** (it is `ℚ̄(T) ⊇ ℚ̄`), so the
  algebraic closure of `ℚ` inside `Ω` lies in `geomBase`.  Together with `regular_ratFunc`
  (`ℚ` is relatively algebraically closed in `ℚ(T)`) this is what makes the descended field regular.

Constructing this field data is the genuine content of **Module A**. -/
structure GeomTower (G : Type) [Group G] [Finite G] (cert : RigidityCertificate G) where
  /-- the arithmetic fundamental group `E = Gal(Ω/ℚ(T))`. -/
  E : Type
  [groupE : Group E]
  /-- the geometric fundamental group `N = Gal(Ω/ℚ̄(T)) ⊴ E`. -/
  N : Subgroup E
  [normalN : N.Normal]
  /-- the geometric monodromy `φ : N →* G`. -/
  φ : N →* G
  /-- the geometric presentation `SphereGroup r ↠ N` (the algebraic geometric `π₁`). -/
  pres : Rigidity.RET.SphereGroup cert.r →* N
  /-- the geometric presentation is surjective. -/
  surjPres : Function.Surjective pres
  /-- the geometric monodromy tuple: the certificate's rigid generating product-one tuple. -/
  base : Fin cert.r → G
  /-- the base tuple is a rigid tuple in the prescribed classes. -/
  base_mem : base ∈ rigidTuples cert.C
  /-- `φ` is the sphere hom of the rigid tuple `base`, read through the presentation. -/
  φ_pres : ∀ x : Rigidity.RET.SphereGroup cert.r,
    φ (pres x) = Rigidity.RET.sphereHom base base_mem.2.1 x
  /-- **The branch-cycle formula** (Module C's tame-inertia + cyclotomic-character input, carried on
  the tower).  For each `e : E` lifting `σ ∈ Gal(k₀/ℚ)` with cyclotomic character value `k = χ(σ)`,
  conjugation by `e` twists each geometric generator `pres (xᵢ)` — through `φ` — into the cyclotomic
  power class `Cᵢ^{χ(σ)}`: `φ (e · pres xᵢ · e⁻¹)` is conjugate to `(base i)^k`, with `k` coprime to
  every base-generator order.  This is the arithmetic-geometry content Fried's branch-cycle argument
  supplies (tame inertia `≅ Ẑ(1)` with `Γ` acting through `χ`); it is bundled with the presentation
  because it is a property of *this* `pres`'s inertia generators.  Consumed by `Descent.BranchCycle`
  (`branchTwistTuple_cyclo`).  See `DESCENT_ROADMAP.md` §1.3. -/
  branchCycle : ∀ e : E, ∃ k : ℕ, (∀ i, Nat.Coprime k (orderOf (base i))) ∧
    ∀ i, ConjClasses.mk (φ (Rigidity.RET.conjN N e (pres (PresentedGroup.of i)))) =
      ConjClasses.mk (base i ^ k)
  -- The field realization (Module A output; consumed by Module D).
  /-- the top field `Ω` of the tower — a finite Galois extension of `ℚ(T)`. -/
  Ω : Type
  [fieldΩ : Field Ω]
  [algΩ : Algebra (RatFunc ℚ) Ω]
  [findimΩ : FiniteDimensional (RatFunc ℚ) Ω]
  [galΩ : IsGalois (RatFunc ℚ) Ω]
  -- `Ω`'s `ℚ`-algebra is the **canonical** `DivisionRing.toRatAlgebra` (built from `CharZero Ω`, not
  -- carried separately): this keeps its `ℚ`-scalar action defeq to the `SubfieldClass` `ℚ`-action on
  -- subfields of `Ω`, which is what Module D's regularity
  -- `IsScalarTower ℚ (RatFunc ℚ) (Ω^{ker ψ})` needs to typecheck.
  [charZeroΩ : CharZero Ω]
  [towerΩ : IsScalarTower ℚ (RatFunc ℚ) Ω]
  /-- `E` is the Galois group `Gal(Ω/ℚ(T))`. -/
  galE : E ≃* (Ω ≃ₐ[RatFunc ℚ] Ω)
  /-- the geometric base `ℚ̄(T)` realized as an intermediate field of `Ω/ℚ(T)`. -/
  geomBase : IntermediateField (RatFunc ℚ) Ω
  /-- `N = Gal(Ω/ℚ̄(T))`: under `galE`, `N` is exactly the fixing subgroup of `geomBase`. -/
  galN_iff : ∀ n : E, n ∈ N ↔ galE n ∈ geomBase.fixingSubgroup
  /-- the geometric base contains all constants: the algebraic closure of `ℚ` inside `Ω` (equivalently
  `ℚ̄`) lies in `geomBase = ℚ̄(T)`.  This is the "geometric" content of the base field. -/
  const_le_geomBase : algebraicClosure ℚ Ω ≤ geomBase.restrictScalars ℚ

attribute [instance] GeomTower.groupE GeomTower.normalN GeomTower.fieldΩ GeomTower.algΩ
  GeomTower.findimΩ GeomTower.galΩ GeomTower.charZeroΩ GeomTower.towerΩ

/-- **Module C's output over a `GeomTower`.**  The Galois-twist data of the branch-cycle formula: for
each `e : E`, a tuple `twist e` in the prescribed rational classes (`twist_mem` — the branch-cycle +
rationality class-invariance) such that the twisted monodromy `φ ∘ conj e` is its sphere hom
(`φ_conj_pres`).  Producing a `BranchTwist` is the content of `Descent.BranchCycle`. -/
structure BranchTwist {G : Type} [Group G] [Finite G] {cert : RigidityCertificate G}
    (tw : GeomTower G cert) where
  /-- the Galois twist of the monodromy by `e : E`, as a tuple. -/
  twist : tw.E → (Fin cert.r → G)
  /-- **branch-cycle + rationality**: each Galois twist stays in the prescribed rational classes. -/
  twist_mem : ∀ e, twist e ∈ rigidTuples cert.C
  /-- the twisted monodromy `φ ∘ conj e` is the sphere hom of `twist e`, through the presentation. -/
  φ_conj_pres : ∀ (e : tw.E) (x : Rigidity.RET.SphereGroup cert.r),
    tw.φ (Rigidity.RET.conjN tw.N e (tw.pres x)) =
      Rigidity.RET.sphereHom (twist e) (twist_mem e).2.1 x
