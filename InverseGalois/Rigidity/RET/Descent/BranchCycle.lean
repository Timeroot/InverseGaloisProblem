/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Descent.Data

/-!
# Module C — the branch-cycle formula (Fried's branch-cycle argument)

Over a `GeomTower G cert` (the arithmetic tower + geometric presentation from `Descent.Tower`), this
module produces the **branch-cycle twist data** `BranchTwist tw`: for each `e : E` the Galois twist
of the geometric monodromy tuple, its membership in the prescribed rational classes, and the
identity `φ ∘ conj e = sphereHom (twist e)`.

## The mathematics

For `e ∈ E` lifting `σ ∈ Γ = Gal(ℚ̄/ℚ)` with cyclotomic character `χ(σ) ∈ Ẑˣ`, Fried's branch-cycle
argument (tame inertia at each branch point is `≅ Ẑ(1)`, on which `Γ` acts through `χ`) shows that
conjugation by `e` carries each branch generator `xᵢ` to a conjugate of `x_{π(i)}^{χ(σ)}`.
Transported through `φ`, the Galois twist of the monodromy tuple `base` therefore lies in the classes
`(C₁^{χ(σ)}, …, C_r^{χ(σ)})` (up to the branch permutation `π`, which for a *single* rational class
tuple is absorbed).

## Arithmetic vs. geometric

* **Geometric** (tame inertia + the cyclotomic action): that the twist tuple lies in the classes
  `Cᵢ^{χ(σ)}` at all.  It is carried by the tower's `branchCycle` field (`GeomTower.branchCycle`),
  which `geomInertiaModel_exists` (`Descent.Tower`) populates.  In this file it is a **direct
  projection** (`branchTwistTuple_cyclo := tw.branchCycle e`).  Fried's branch-cycle argument (tame
  inertia `≅ Ẑ(1)` with `Γ` acting through `χ`) lives *once*, inside `geomInertiaModel_exists`,
  consolidated with the N-level Riemann Existence presentation; the two are faces of a single
  geometric object.
* **Arithmetic** (the class-invariance): once the twist lands in `Cᵢ^{χ(σ)}`, **class stability**
  under the coprime power `χ(σ)` — the hypothesis `hstab` — forces `Cᵢ^{χ(σ)} = Cᵢ`, so the twist
  lands in `rigidTuples cert.C`.  Rationality of the classes is one way to supply `hstab`, and it is
  exactly why rationality is a field of `RigidityCertificate`; stability under a subgroup of the
  cyclotomic action supplies it over a number field instead.

Once `twist e ∈ rigidTuples cert.C`, the *downstream* `ArithmeticDescentData.ofBranchCycle` uses
`sphereHom_inner_equiv_of_rigid` to turn rigidity into the inner-automorphism payoff — so Module C's
only job is to land the twist in the rational classes and match the sphere hom.

## Decomposition (this file)

The branch-cycle datum is packaged into `BranchCycleInput tw`: for each `e : E` a twist tuple that is
product-one, lands in the *cyclotomically twisted* classes `Cᵢ^{χ(σ)}` (encoded per index, the branch
permutation already absorbed into the tuple), and realizes `φ ∘ conjN e ∘ pres` as its sphere hom.
The concrete inhabitant `branchCycleInput` is assembled from the explicit twist tuple
`branchTwistTuple`, its elementary `prod_one`/`φ_conj_pres` proofs, and the branch-cycle formula
`branchTwistTuple_cyclo`, which projects the tower's `branchCycle` field.

Both `branchCycleInput` and `BranchCycleInput.toBranchTwist` are proved outright:

* **class-invariance** (`twist_mem`, first component): the stability hypothesis `hstab` collapses
  each cyclotomic power `Cᵢ^{χ(σ)}` back to `Cᵢ`.  *This is the entire reason `rational` is a
  certificate field.*
* **generation** (`twist_mem`, third component): **derived**, not assumed — `sphereHom (twist e)`
  equals `φ ∘ conjN e ∘ pres`, a composite of three surjections (`φ` onto `G` because `base`
  generates, `conjN e` a bijection of `N`, `pres` onto `N`), so it is surjective, whence the twist
  tuple generates (`sphereHom_surjective_iff`).
* **product-one** (`twist_mem`, second component): inherited from the input.

## Main results

* `BranchCycleInput` — the branch-cycle datum (twist tuple + its cyclotomic-class membership).
* `BranchCycleInput.toBranchTwist` — the class-invariance + generation glue.
* `branchCycleTwist` — the branch-cycle twist data over a `GeomTower`; its cyclotomic-class content
  is a projection of the tower's `branchCycle` field.
-/

open Polynomial

namespace Rigidity.RET

/-- Conjugation by `e` on the normal subgroup `N`, bundled as a monoid endomorphism.  This is
`conjN N e` (multiplicative because conjugation distributes over products), packaged so it can be
composed with the presentation hom `pres` to build the twisted monodromy `φ ∘ conjN e ∘ pres`. -/
def conjNHom {E : Type*} [Group E] (N : Subgroup E) [N.Normal] (e : E) : N →* N where
  toFun := conjN N e
  map_one' := Subtype.ext (by simp only [conjN_coe, OneMemClass.coe_one]; group)
  map_mul' a b := Subtype.ext (by simp only [conjN_coe, Subgroup.coe_mul]; group)

@[simp] lemma conjNHom_apply {E : Type*} [Group E] (N : Subgroup E) [N.Normal] (e : E) (n : N) :
    conjNHom N e n = conjN N e n := rfl

/-- **The product of all generators of the sphere group is trivial** — the single defining relation
`x₀·x₁···x_{r-1} = 1` of `Γ_r = SphereGroup r`.  (The `r`-general companion of the `r+1` computation
inside `sphereGroup_mulEquiv_free`.) -/
theorem sphereGroup_genProd_one (r : ℕ) :
    (List.ofFn (fun i : Fin r => PresentedGroup.of i : Fin r → SphereGroup r)).prod = 1 := by
  have hmem : (List.ofFn fun i : Fin r => FreeGroup.of i).prod ∈ sphereRel r :=
    Set.mem_singleton_iff.mpr rfl
  have h1 : (List.ofFn (fun i : Fin r => PresentedGroup.of i : Fin r → SphereGroup r)).prod
      = PresentedGroup.mk (sphereRel r) (List.ofFn fun i : Fin r => FreeGroup.of i).prod := by
    rw [map_list_prod, List.map_ofFn]
    rfl
  rw [h1]
  exact PresentedGroup.one_of_mem hmem

end Rigidity.RET

/-- **The branch-cycle datum over the tower `tw`.**  This packages the output of Fried's tame
branch-cycle argument, *before* the elementary rationality collapse: for each `e : E` a Galois-twist
tuple `twist e` that

* is **product-one** (`prod_one`);
* lands in the **cyclotomically twisted classes** (`cyclo`): there is a cyclotomic exponent `k`
  (the value `χ(σ)` of the cyclotomic character on the image `σ ∈ Γ` of `e`), coprime to each
  base-generator order, with `twist e i` conjugate to `base i ^ k` — i.e. in class `Cᵢ^{χ(σ)}`.
  The branch permutation `π` of the classical formula is taken to be already absorbed into the
  indexing of `twist e` (legitimate for the rational-class configuration of a rigidity certificate);
* realizes the **twisted monodromy** `φ ∘ conjN e ∘ pres` as its sphere hom (`φ_conj_pres`).

The `cyclo` field is the tame-inertia + cyclotomic-character content (`Γ` acts on tame inertia
`≅ Ẑ(1)` through `χ`); over a `GeomTower` it is supplied by the tower's `branchCycle` field.  Given
an inhabitant, `toBranchTwist` derives the full `BranchTwist`. -/
structure BranchCycleInput {G : Type} [Group G] [Finite G] {cert : RigidData G}
    (tw : GeomTower G cert) where
  /-- the Galois twist of the monodromy by `e : E`, as a tuple. -/
  twist : tw.E → (Fin cert.r → G)
  /-- each twist tuple is product-one. -/
  prod_one : ∀ e, (List.ofFn (twist e)).prod = 1
  /-- **tame branch-cycle formula**: each twist coordinate lies in the cyclotomic power `Cᵢ^{χ(σ)}`
  of the base class, for a single exponent `k = χ(σ)` coprime to every base-generator order. -/
  cyclo : ∀ e, ∃ k : ℕ, (∀ i, Nat.Coprime k (orderOf (tw.base i))) ∧
    ∀ i, ConjClasses.mk (twist e i) = ConjClasses.mk (tw.base i ^ k)
  /-- the twisted monodromy `φ ∘ conjN e ∘ pres` is the sphere hom of `twist e`. -/
  φ_conj_pres : ∀ (e : tw.E) (x : Rigidity.RET.SphereGroup cert.r),
    tw.φ (Rigidity.RET.conjN tw.N e (tw.pres x)) =
      Rigidity.RET.sphereHom (twist e) (prod_one e) x

/-- **The glue of Module C.**  From the abstracted branch-cycle datum, the twist
tuples land in the certificate's *rational* classes and the full `BranchTwist` follows.  Three
components:

* **class-invariance** — the stability hypothesis `hstab` collapses `Cᵢ^{χ(σ)}` to `Cᵢ`;
* **generation** — *derived* from surjectivity of `φ ∘ conjN e ∘ pres = sphereHom (twist e)`
  (a composite of three surjections), via `sphereHom_surjective_iff`;
* **product-one** — inherited.

No arithmetic-geometry input; this is exactly the elementary content class stability supplies. -/
noncomputable def BranchCycleInput.toBranchTwist {G : Type} [Group G] [Finite G]
    {cert : RigidData G} {tw : GeomTower G cert} (input : BranchCycleInput tw)
    (hstab : ∀ (i : Fin cert.r) (k : ℕ), Nat.Coprime k (orderOf (tw.base i)) →
      ConjClasses.mk (tw.base i ^ k) = cert.C i) :
    BranchTwist tw := by
  classical
  -- `φ : N ↠ G` is surjective: `base` generates, so its sphere hom is onto and `φ` factors it.
  have hφsurj : Function.Surjective tw.φ := by
    intro g
    have hs : Function.Surjective (Rigidity.RET.sphereHom tw.base tw.base_mem.2.1) :=
      (Rigidity.RET.sphereHom_surjective_iff tw.base tw.base_mem.2.1).2 tw.base_mem.2.2
    obtain ⟨x, hx⟩ := hs g
    exact ⟨tw.pres x, by rw [tw.φ_pres x, hx]⟩
  -- conjugation by `e` is a surjection `N ↠ N` (a bijection, inverse `conjN e⁻¹`).
  have hconj : ∀ e : tw.E, Function.Surjective (Rigidity.RET.conjN tw.N e) := by
    intro e n
    refine ⟨Rigidity.RET.conjN tw.N e⁻¹ n, ?_⟩
    apply Subtype.ext
    simp only [Rigidity.RET.conjN_coe]
    group
  -- each twist tuple is a rigid tuple in the prescribed classes.
  have htwist_mem : ∀ e, input.twist e ∈ rigidTuples cert.C := by
    intro e
    refine ⟨?_, input.prod_one e, ?_⟩
    · -- class membership: rationality collapses the cyclotomic power back to the base class.
      obtain ⟨k, hcop, heq⟩ := input.cyclo e
      intro i
      rw [heq i]
      exact hstab i k (hcop i)
    · -- generation: `sphereHom (twist e)` is `φ ∘ conjN e ∘ pres`, a composite of surjections.
      rw [← Rigidity.RET.sphereHom_surjective_iff (input.twist e) (input.prod_one e)]
      have hcomp : Function.Surjective
          (fun x => tw.φ (Rigidity.RET.conjN tw.N e (tw.pres x))) := by
        intro g
        obtain ⟨n, hn⟩ := hφsurj g
        obtain ⟨m, hm⟩ := hconj e n
        obtain ⟨x, hx⟩ := tw.surjPres m
        exact ⟨x, by
          show tw.φ (Rigidity.RET.conjN tw.N e (tw.pres x)) = g
          rw [hx, hm, hn]⟩
      have hfun : (⇑(Rigidity.RET.sphereHom (input.twist e) (input.prod_one e)))
          = fun x => tw.φ (Rigidity.RET.conjN tw.N e (tw.pres x)) := by
        funext x; exact (input.φ_conj_pres e x).symm
      rw [hfun]; exact hcomp
  exact
    { twist := input.twist
      twist_mem := htwist_mem
      φ_conj_pres := fun e x => input.φ_conj_pres e x }

/-- The **concrete Galois-twist tuple** of the branch-cycle datum: the `i`-th coordinate is the image
under `φ` of the `e`-conjugate of the `i`-th geometric generator `pres (xᵢ)`.  This is the tuple
whose *class membership* is the branch-cycle formula (`branchTwistTuple_cyclo`); its product-one and
sphere-hom properties (`branchTwistTuple_prod_one`, `branchTwistTuple_φ_conj_pres`) are elementary
group theory, proved below. -/
noncomputable def branchTwistTuple {G : Type} [Group G] [Finite G] {cert : RigidData G}
    (tw : GeomTower G cert) (e : tw.E) : Fin cert.r → G :=
  fun i => tw.φ (Rigidity.RET.conjN tw.N e (tw.pres (PresentedGroup.of i)))

/-- The twisted monodromy `φ ∘ conjN e ∘ pres : SphereGroup r →* G`, bundled as a hom.  Its value on
the `i`-th generator is `branchTwistTuple tw e i` by definition (`branchTwistHom_of`). -/
noncomputable def branchTwistHom {G : Type} [Group G] [Finite G] {cert : RigidData G}
    (tw : GeomTower G cert) (e : tw.E) : Rigidity.RET.SphereGroup cert.r →* G :=
  tw.φ.comp ((Rigidity.RET.conjNHom tw.N e).comp tw.pres)

@[simp] theorem branchTwistHom_of {G : Type} [Group G] [Finite G] {cert : RigidData G}
    (tw : GeomTower G cert) (e : tw.E) (i : Fin cert.r) :
    branchTwistHom tw e (PresentedGroup.of i) = branchTwistTuple tw e i := rfl

/-- **Product-one (elementary).**  The twist tuple is the image of the sphere group's generators
under the hom `branchTwistHom`; the product of all generators is trivial by the sphere relation
(`sphereGroup_genProd_one`), so the product of the tuple is `1`. -/
theorem branchTwistTuple_prod_one {G : Type} [Group G] [Finite G] {cert : RigidData G}
    (tw : GeomTower G cert) (e : tw.E) :
    (List.ofFn (branchTwistTuple tw e)).prod = 1 := by
  have hprod : (List.ofFn (branchTwistTuple tw e)).prod
      = branchTwistHom tw e (List.ofFn (fun i : Fin cert.r => PresentedGroup.of i)).prod := by
    rw [map_list_prod, List.map_ofFn]
    rfl
  rw [hprod, Rigidity.RET.sphereGroup_genProd_one, map_one]

/-- **Sphere-hom identity (elementary).**  `φ ∘ conjN e ∘ pres` (bundled as `branchTwistHom`) and
`sphereHom (branchTwistTuple tw e)` are two homs `SphereGroup r →* G` agreeing on every generator,
hence equal. -/
theorem branchTwistTuple_φ_conj_pres {G : Type} [Group G] [Finite G]
    {cert : RigidData G} (tw : GeomTower G cert) (e : tw.E)
    (x : Rigidity.RET.SphereGroup cert.r) :
    tw.φ (Rigidity.RET.conjN tw.N e (tw.pres x)) =
      Rigidity.RET.sphereHom (branchTwistTuple tw e) (branchTwistTuple_prod_one tw e) x := by
  have hhom : branchTwistHom tw e
      = Rigidity.RET.sphereHom (branchTwistTuple tw e) (branchTwistTuple_prod_one tw e) := by
    ext i
    rw [Rigidity.RET.sphereHom_of]
    rfl
  exact DFunLike.congr_fun hhom x

/-- **The tame branch-cycle formula.**  For each `e : E` lifting `σ ∈ Γ = Gal(ℚ̄/ℚ)` with cyclotomic
character value `k = χ(σ)`, the twist coordinate `branchTwistTuple tw e i` lies in the cyclotomic
power class `Cᵢ^{χ(σ)}` — i.e. is conjugate to `base i ^ k` — with `k` coprime to every base-generator
order.

This is now a **direct projection** of the tower's `branchCycle` field (`branchTwistTuple tw e i` is
definitionally `φ (conjN e (pres (xᵢ)))`).  The arithmetic-geometry content — Fried's branch-cycle
argument (tame inertia `≅ Ẑ(1)` with `Γ` acting through `χ`) — has been consolidated into
`geomInertiaModel_exists` that populates `branchCycle`; see `Descent.Tower` and the geometric `π₁`
development.  See `DESCENT_ROADMAP.md` §1.3. -/
theorem branchTwistTuple_cyclo {G : Type} [Group G] [Finite G] {cert : RigidData G}
    (tw : GeomTower G cert) (e : tw.E) :
    ∃ k : ℕ, (∀ i, Nat.Coprime k (orderOf (tw.base i))) ∧
      ∀ i, ConjClasses.mk (branchTwistTuple tw e i) = ConjClasses.mk (tw.base i ^ k) :=
  tw.branchCycle e

/-- The branch-cycle datum over any tower, assembled from the concrete twist tuple.  Three of its four
fields (`twist`, `prod_one`, `φ_conj_pres`) are the elementary group theory proved above
(`branchTwistTuple`, `branchTwistTuple_prod_one`, `branchTwistTuple_φ_conj_pres`); the fourth,
`cyclo`, is the tame branch-cycle formula `branchTwistTuple_cyclo`, which projects the tower's
`branchCycle` field.  See `DESCENT_ROADMAP.md` §1.3. -/
noncomputable def branchCycleInput {G : Type} [Group G] [Finite G] {cert : RigidData G}
    (tw : GeomTower G cert) : BranchCycleInput tw where
  twist := branchTwistTuple tw
  prod_one := branchTwistTuple_prod_one tw
  cyclo := branchTwistTuple_cyclo tw
  φ_conj_pres := branchTwistTuple_φ_conj_pres tw

/-- **Module C.**  Over the geometric tower `tw`, the branch-cycle formula produces the Galois-twist
data: for each `e : E` a tuple `twist e` in the prescribed rational classes such that the twisted
monodromy `φ ∘ conj e` is its sphere hom.

The tame branch-cycle content (the Galois twist landing in the classes `Cᵢ^{χ(σ)}`) is supplied by
`branchCycleInput` via the tower's `branchCycle` field; the class-invariance `Cᵢ^{χ(σ)} = Cᵢ`
(hypothesis `hstab`) and the derivation of generation are the `BranchCycleInput.toBranchTwist` glue.  See
`DESCENT_ROADMAP.md` §1.3 and the module docstring. -/
noncomputable def branchCycleTwist {G : Type} [Group G] [Finite G] {cert : RigidData G}
    (tw : GeomTower G cert)
    (hstab : ∀ (i : Fin cert.r) (k : ℕ), Nat.Coprime k (orderOf (tw.base i)) →
      ConjClasses.mk (tw.base i ^ k) = cert.C i) : BranchTwist tw :=
  (branchCycleInput tw).toBranchTwist hstab
