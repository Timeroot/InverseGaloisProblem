import InverseGalois.Rigidity.RET.Presentation
import InverseGalois.Rigidity.RET.Pi1.Completion
import InverseGalois.Rigidity.RET.Pi1.SphereCompletion
import InverseGalois.Rigidity.RET.Statement
import InverseGalois.Rigidity.RET.Cayley
import InverseGalois.Rigidity.RET.Existence
import InverseGalois.Rigidity.RET.Pi1.CoverCompletion
import InverseGalois.Rigidity.RET.Pi1.FundamentalGroup
import InverseGalois.Rigidity.RET.Pi1.FundamentalGroupCover
import InverseGalois.Rigidity.RET.Pi1.InertiaGenerators
import InverseGalois.Rigidity.RET.Pi1.Etale.Fiber
import InverseGalois.Rigidity.RET.Pi1.Etale.Category
import InverseGalois.Rigidity.RET.Pi1.Etale.Closure
import InverseGalois.Rigidity.RET.Pi1.Etale.Limits
import InverseGalois.Rigidity.RET.Pi1.Etale.Pushout
import InverseGalois.Rigidity.RET.Pi1.Etale.Subalgebra
import InverseGalois.Rigidity.RET.Pi1.Etale.Equalizer
import InverseGalois.Rigidity.RET.Pi1.Etale.DirectSummand
import InverseGalois.Rigidity.RET.Pi1.Etale.FiberFunctor
import InverseGalois.Rigidity.RET.Pi1.Etale.Quotient
import InverseGalois.Rigidity.RET.Pi1.Etale.Connected
import InverseGalois.Rigidity.RET.Pi1.Etale.AbsoluteGalois
import InverseGalois.Rigidity.RET.Pi1.Etale.Equivalence
import InverseGalois.Rigidity.RET.Pi1.Topological.Monodromy
import InverseGalois.Rigidity.RET.Pi1.Topological.QuotientPi1
import InverseGalois.Rigidity.RET.Pi1.Topological.Transport
import InverseGalois.Rigidity.RET.Pi1.Topological.CircleGroup
import InverseGalois.Rigidity.RET.Pi1.Topological.TameCover
import InverseGalois.Rigidity.RET.Pi1.Topological.TameMonodromy
import InverseGalois.Rigidity.RET.Pi1.Topological.SphereBaseCase
import InverseGalois.Rigidity.RET.Pi1.Topological.Wedge
import InverseGalois.Rigidity.RET.Pi1.Topological.VanKampen.Group
import InverseGalois.Rigidity.RET.Pi1.Topological.PuncturedPlane
import InverseGalois.Rigidity.RET.Pi1.Topological.Comparison
import InverseGalois.Rigidity.RET.Pi1.AbsoluteGaloisQuotient
import InverseGalois.Rigidity.RET.KummerCover
import InverseGalois.Rigidity.RET.KummerAbelian
import InverseGalois.Rigidity.RET.ArtinFixedField
import InverseGalois.Rigidity.RET.RatFuncSubst
import InverseGalois.Rigidity.RET.SerreCovers
import InverseGalois.Rigidity.RET.ExistenceLowRank
import InverseGalois.Rigidity.RET.Descent
import InverseGalois.Rigidity.RET.Specialization

/-!
# Decomposing the Riemann Existence Theorem: an honest axiom cut

This directory **replaced** the single, over-specified axiom `riemann_existence_ax` (formerly in
`InverseGalois/Rigidity/RiemannExistence.lean`, now deleted) — which handed over the *entire*
`of_regular_family` polynomial bundle in one gulp — with a decomposition that isolates a single,
recognizably textbook Riemann Existence Theorem as the only deep geometric ingredient, and whose
remaining layers are genuine, complete Lean.  The Riemann Existence Theorem is recorded in two forms:
the covers correspondence (`riemann_existence_cover`, `RET.Existence`), which supports the
profinite-`π₁` reformulation (`RET.Pi1.CoverCompletion`, `RET.Pi1.FundamentalGroupCover`); and — the
form consumed by `Rigidity.rigidity_realizable` — the tame-inertia realization
(`inertiaRootData_exists`, `RET.Descent.Tower`), which additionally supplies the branch-cycle inertia
generators and their cyclotomic conjugation, at exactly the interface the branch-cycle descent
consumes.  Everything from that datum down to `IsInverseGalois G` — the descent to `ℚ(T)` and the
Hilbert specialization to `ℚ` — is genuine, complete Lean; the geometric input itself is being built
from the étale/tame fundamental-group theory under `RET.Pi1`.

## Why the old axiom was dishonest

`riemann_existence_ax` asserted, verbatim, the nine-conjunct hypothesis bundle of
`IsInverseGalois.of_regular_family` for `H = φ.range`: a monic `ℚ[T][X]` family `F`, an absolutely
irreducible resolvent `Gp`, cofinite separability, and the *per-specialization* landing (`hland`)
and root (`hroot`) certificates.  A textbook RET produces only a **regular Galois cover** (a field
extension) with prescribed monodromy and branch data; the translation of that cover into an explicit
monic polynomial family *with per-`t` arithmetic certificates* is real algebra that the axiom was
smuggling.  The fully-worked `Aₙ` development (`InverseGalois/Hilbert/Alternating*`) is exactly that
translation done by hand for one family — proof that it is provable, not axiomatic.  This directory
does the same translation *generally* in `RET.Specialization` (`exists_regular_family`), modulo two
isolated arithmetic-geometry bridges.

## The honest cut (chosen architecture)

There are three reasonable places to state RET:

* **Topological** — π₁(ℙ¹(ℂ) ∖ S) and covers ↔ π₁-sets.  *Rejected for now*: Mathlib has covering
  spaces and `FundamentalGroup` but **no concrete π₁ is computed for any space**, no
  covers↔π₁-sets equivalence, no ℂP¹/punctured sphere, no van Kampen; and GAGA / algebraic curves /
  analytification are entirely absent.  This route is a multi-year prerequisite stack.
* **Grothendieck / Galois-category** — the profinite π₁ of the punctured line via
  `CategoryTheory.Galois`.  That framework *does* exist in Mathlib (`GaloisCategory`,
  `IsFundamentalGroup`, `ContAction`), but linking it to actual finite extensions of `ℚ̄(t)` needs
  the covers↔extensions dictionary, which is absent.
* **Algebraic (field-theoretic)** — *chosen*.  State RET directly as: a rigid rational generating
  tuple yields a **regular Galois extension of `ℚ̄(t)`** with the prescribed group and inertia.
  This is textbook (Völklein *Groups as Galois Groups* Thm 2.13; Serre *Topics in Galois Theory*
  §6–8), lives in the algebraic world the repo already inhabits (`ℚ[T][X]`, `specialize`,
  `Polynomial.Gal`), and makes the descent and model-translation layers provable.

## The honest conclusion, and the two Mathlib-blocked steps

The textbook output of the method is a **regular Galois extension of `ℚ(T)`** with group `G` —
not a polynomial bundle.  That conclusion is now named `IsRegularInverseGalois G`
(`RET.Statement`): a finite Galois `L / ℚ(T)` with `Gal ≃* G` in which `ℚ` is relatively
algebraically closed (`algebraicClosure ℚ L = ⊥`).  Against it the honest cut is *two*
recognizable theorems, each a textbook statement, rather than one over-specified bundle:

* **(A) rigidity ⟹ regular realization**: `RigidityCertificate G → IsRegularInverseGalois G`.
  This is Völklein Thm 2.13 = RET + branch-cycle rationality descent.  Mathlib-blocked (GAGA /
  algebraic curves); this is the honest home of the sole geometric axiom.
* **(B) regular realization ⟹ inverse Galois**: `IsRegularInverseGalois G → IsInverseGalois G`.
  This is Hilbert irreducibility / specialization: a regular `ℚ(T)`-extension specializes to a
  `ℚ`-extension with the same group at infinitely many `T`.  The repo already has the
  polynomial-model form of this (`of_regular_family` + `hilbert_irreducibility_theorem`); the
  gap is only the *model translation* abstract-extension → polynomial family (the `Aₙ` template).

Two recognizable theorems is strictly more honest than the current single bundle, which fuses
A, B, and the per-specialization certificates into `of_regular_family`'s hypothesis.

## Layer decomposition

Input: a `RigidityCertificate G` (branch count `r`, rational classes `C`, centerless, a nonempty
rigid set of generating product-one tuples) plus a faithful `φ : G ↪ Sₙ`.
Output: the `of_regular_family` bundle for `H = φ.range`.  In between:

* **L1 — Presentation layer** (`RET.Presentation`).  Pure group theory, all Mathlib vocabulary
  present (`FreeGroup`, `PresentedGroup`).  The sphere group `Γ_r = ⟨x₀,…,x_{r-1} | ∏ xᵢ = 1⟩`; the
  bijection between generating product-one `r`-tuples of `G` and surjections `Γ_r ↠ G`, with
  simultaneous conjugation ↔ post-composition by `Inn G`.  This is the algebraic shadow of
  `π₁(ℙ¹∖S)` and the interface the certificate plugs into.  **Immediately ATP-able.**
* **L2 — Rigidity / branch-cycle descent** `ℚ̄(t) → ℚ(t)`.  The heart of the *method*, and mostly
  provable (Galois-action bookkeeping + group cohomology).  `Gal(ℚ̄/ℚ)` acts on tuples via the
  cyclotomic character on the rational classes; rationality fixes the class-tuple, rigidity (single
  `Inn G`-orbit, from `Rigidity.rigid_card_iff_single_orbit`) makes the cover class Galois-stable,
  and centerless kills the `H¹(·, Z G)` obstruction — giving descent to a *regular* `ℚ(t)`-extension.
* **L3 — RET existence** (the irreducible GAGA content).  A surjection `Γ_r ↠ G` with
  prescribed branch points yields a regular Galois extension of `ℚ̄(t)` with deck group `G` and
  inertia generators in the classes `Cᵢ`.  This is the sole geometric input, and it is being built
  from the étale and topological fundamental-group theory under `RET.Pi1`.  For particular groups it
  is already established outright, with no geometry: for the finite abelian groups by Kummer theory
  (`RET.KummerCover`, `RET.KummerAbelian`), for `Aₙ` and `Sₙ` by Serre's explicit family
  (`RET.SerreCovers`), and for *every* group when there are at most two branch points
  (`RET.ExistenceLowRank`, where the sphere group is cyclic).  `RET.ArtinFixedField` is the general
  engine for such by-hand constructions: a faithful action on a field with invariants `ℚ̄(T)`.
* **L4 — Model translation** to the `of_regular_family` bundle.  Algebra: primitive element +
  resolvent (orbit of a generic linear form) + specialization/reduction-of-inertia.  The `Aₙ`
  development is the worked template.

Assembly (`L5`, **done**): `Rigidity.rigidity_realizable` now composes L1+L2+L3+L4 through the honest
chain `RigidityCertificate G → IsRegularInverseGalois G → IsInverseGalois G`, resting on the single
L3 Riemann Existence Theorem (`inertiaRootData_exists`, in its tame-inertia form) with the L2 descent
and the L4 arithmetic-geometry bridges all genuine Lean.  The over-specified `riemann_existence_ax`
and its file `RiemannExistence.lean` have been deleted.

## Mathlib grounding (survey, 2026-07-29)

READY to consume: `FreeGroup`, `IsFreeGroup`, `PresentedGroup` (+ `toGroup` universal property);
`CategoryTheory.Galois.*` (Galois categories ≌ continuous finite `Aut F`-sets, `IsFundamentalGroup`);
`IsCoveringMap`, path/homotopy lifting, `IsCoveringMap.monodromyFunctor`; `RatFunc`, `FunctionField`
(over `Fq`), `Scheme.functionField`, `IsDominant`; the repo's `ℚ[T][X]`/`specialize`/`Polynomial.Gal`
backbone and the complete `Aₙ` template.

ABSENT (must be built or axiomatized): concrete π₁ of any space; covers↔π₁-sets equivalence /
cover-existence; deck transformations, degree; ℂP¹ / Riemann sphere / punctured sphere as a
space/manifold; Seifert–van Kampen; **GAGA / analytification**; algebraic curves, degree /
ramification of morphisms, covers↔function-field-extensions; Riemann–Roch, genus.  The GAGA + curves
gap is why L3 is still open — carried as an honest `sorry` on its own statement, never as an axiom;
everything else above the cut is provable.

## Currently landed

* **L1** — `InverseGalois.Rigidity.RET.Presentation`: the sphere presentation group `Γ_r`, the
  tuple ↔ surjection dictionary (`sphereHom`, `sphereHom_surjective_iff`), the
  conjugation ↔ inner-automorphism correspondence (`sphereHom_conj`), and the freeness
  `sphereGroup_mulEquiv_free` (`Γ_r ≅ FreeGroup (Fin (r-1))`).  **Complete and sorry-free.**
* **Honest conclusion** — `InverseGalois.Rigidity.RET.Statement`: `IsRegularInverseGalois G`, the
  recognizable target of step (A) and source of step (B) above, with `of_mulEquiv`.
* **Unconditional pieces of L3** — the finite abelian groups (`RET.KummerAbelian`), `Aₙ` and `Sₙ`
  for `n ≥ 3` (`RET.SerreCovers`), and every branch datum with at most two points
  (`RET.ExistenceLowRank`), together with the closure of the predicate under quotients of the group
  and under isomorphism of the base field (`RET.Pi1.AbsoluteGaloisQuotient`) and Artin's theorem as
  a supplier of covers from invariant theory (`RET.ArtinFixedField`).  All sorry-free.
-/
