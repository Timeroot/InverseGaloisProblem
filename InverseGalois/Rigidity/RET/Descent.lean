/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Existence
import InverseGalois.Rigidity.RET.Statement
import InverseGalois.Rigidity.RET.CenterlessExtension
import InverseGalois.Rigidity.RET.BranchCycleBridge
import InverseGalois.Rigidity.StructureConstant
import InverseGalois.Rigidity.RET.Descent.Data
import InverseGalois.Rigidity.RET.Descent.Matching
import InverseGalois.Rigidity.RET.Descent.Tower
import InverseGalois.Rigidity.RET.Descent.BranchCycle
import InverseGalois.Rigidity.RET.Descent.FieldTranslation
import InverseGalois.Rigidity.RET.Descent.Ramification
import InverseGalois.Rigidity.RET.Descent.GeomArithBridge
import InverseGalois.Rigidity.RET.Descent.ConstantNormal
import InverseGalois.Rigidity.RET.Descent.CompositumBranch
import InverseGalois.Rigidity.RET.Descent.ModelEnlarge
import InverseGalois.Rigidity.RET.Descent.BranchCycles

/-!
# L2 — Branch-cycle rationality descent `ℚ̄(T) → ℚ(T)`

The Riemann Existence Theorem (`riemann_existence_cover`, `RET.Existence`) produces the geometric
cover over `ℚ̄`: a Galois extension of `ℚ̄(T)` with deck group `G`.  This file carries that cover
down to a *regular* Galois extension of `ℚ(T)` (`IsRegularInverseGalois G`) — the **branch-cycle
rationality descent**, which is exactly the recognizable **rigidity criterion** (Völklein, *Groups
as Galois Groups*, Thm 2.13; Serre, *Topics in Galois Theory*, §8; Fried–Völklein).

This is **not** an axiom.  The descent splits cleanly into

* a **group-theoretic core** — the *centerless extension lemma*
  (`Rigidity.RET.extend_surjective_of_inner`) fed by the *rigidity → inner* bridge
  (`Rigidity.RET.sphereHom_inner_equiv_of_rigid`, `Rigidity.exists_pointwise_conj_of_rigid`); and
* an **arithmetic-geometry layer** that Mathlib lacks — the arithmetic fundamental-group exact
  sequence, the branch-cycle formula, and the field translation `Gal(ℚ̄(T)/ℚ(T)) ≅ Gal(ℚ̄/ℚ)` with
  the regularity bridge.

The second bullet is **decomposed** (see `DESCENT_ROADMAP.md`) into four modules with a frozen
interface (`Descent.Data`):

* **Module A+B** (`Descent.Tower`, `geomTower_nonempty`): the field tower `ℚ(T) ⊂ ℚ̄(T) ⊂ Ω` with its
  fundamental exact sequence, and the geometric `π₁` presentation `SphereGroup r ↠ N`.
* **Module C** (`Descent.BranchCycle`, `branchCycleTwist`): the branch-cycle formula giving the
  Galois-twist tuples in the prescribed rational classes.
* **Module D** (`Descent.FieldTranslation`, `descentTranslation`): the fixed field of `ker ψ` is a
  regular `ℚ(T)`-extension realizing `G`.

Every module is proven from a single geometric statement, the existence direction
`Rigidity.RET.geomRETExistence_of_injective` of the Riemann Existence Theorem over `ℚ̄`, which
enters through `Descent.BranchCycles`; the completeness direction that module also uses,
`Rigidity.RET.geomRETCompleteness_of_injective`, is proven.  The arithmetic packaging
of its output as a tame inertia model is `Descent.Tower`.  The structures and the assembly here are
*assembled* from the three module producers, and the group-theoretic core (`ofBranchCycle` +
`extend_surjective_of_inner`) is proven outright.

## The mathematics of the descent (the proof plan)

Write `Γ = Gal(ℚ̄/ℚ)`.  It acts on `ℚ̄(T)` coefficient-wise, hence on the `G`-covers of `ℙ¹_{ℚ̄}`
branched over rational points.  Let `Ω/ℚ(T)` be a common Galois closure, giving the exact sequence

  `1 → N → E → Γ → 1`,  `N = Gal(Ω/ℚ̄(T))`,  `E = Gal(Ω/ℚ(T))`,

and let `φ : N ↠ G` be the geometric monodromy of the cover.

* **Branch-cycle formula.** For `σ ∈ Γ` with cyclotomic character `χ(σ)`, conjugation by a lift of
  `σ` carries the inertia data `(C₁,…,C_r)` to `(C₁^{χ(σ)},…,C_r^{χ(σ)})` (Fried's branch cycle
  argument).
* **Rationality** (`cert.rational`) makes the class-tuple `Γ`-invariant: `Cᵢ^{χ(σ)} = Cᵢ`, so the
  twisted monodromy tuple again lies in `rigidTuples C`.
* **Rigidity** (`cert.rigid`, via `Rigidity.rigid_card_iff_single_orbit`): the tuples in
  `rigidTuples C` form a single simultaneous-conjugation orbit, so the twist is *simultaneously
  conjugate* to the original — i.e. conjugation by every `e ∈ E` is **inner** through `φ`.  This is
  exactly `Rigidity.RET.sphereHom_inner_equiv_of_rigid`.
* **Centerless** (`cert.center_triv`, `Z(G) = ⊥`) makes that inner twist **unique**, so `φ`
  extends to a homomorphism `ψ : E ↠ G` (`Rigidity.RET.extend_surjective_of_inner`): the
  field-of-moduli obstruction `H¹(Γ, Z(G))` vanishes and the field of moduli is a field of
  definition.  `ψ|_N = φ` stays surjective, so the fixed field of `ker ψ` is a **regular**
  Galois extension of `ℚ(T)` with group `G`.

## Main results

* `branchCycleDescentData_nonempty` — assembled from the three module producers.
* `arithmeticDescentData_nonempty` — derived via `ArithmeticDescentData.ofBranchCycle`.
* `branch_cycle_descent` — the descent, proved from the datum with the group-theoretic core.
* `RigidityCertificate.isRegularInverseGalois` — the rigidity criterion, assembled from RET and the
  descent.
-/

open Polynomial

/-- **The branch-cycle descent datum exists** — *assembled* from the three descent modules.  The
geometric tower (Modules A+B, `geomTower_nonempty_twist`) supplies `N ⊴ E`, the monodromy `φ`, and
its presentation as the certificate's rigid tuple — over a cyclotomic twist of the prescribed
classes, which rationality identifies with the classes themselves; the branch-cycle formula
(Module C, `branchCycleTwist`) supplies the Galois-twist tuples in the prescribed rational classes;
and the field translation (Module D, `descentTranslation`) supplies `toRegular`.

The arithmetic-geometry content of those three producers rests on the geometric existence theorem
`Rigidity.RET.geomRETExistence_of_injective`; see `DESCENT_ROADMAP.md`. -/
theorem branchCycleDescentData_nonempty {G : Type} [Group G] [Finite G]
    (cert : RigidityCertificate G) :
    Nonempty (BranchCycleDescentData G cert.toRigidData) := by
  -- Geometry realizes the classes only up to a coordinatewise cyclotomic twist; rationality
  -- absorbs the twist, so the tower is available over the certificate's own classes.
  obtain ⟨u, hcop, htw⟩ := geomTower_nonempty_twist cert.toRigidData
  have hpow : ∀ i, ConjClasses.powClass (u i) (cert.C i) = cert.C i :=
    fun i => (cert.rational i).powClass_eq (hcop i)
  have hrig : Nat.card (rigidTuples fun i => ConjClasses.powClass (u i) (cert.toRigidData.C i))
      = Nat.card G := by
    rw [show (fun i => ConjClasses.powClass (u i) (cert.toRigidData.C i)) = cert.C from
      funext hpow]
    exact cert.rigid
  obtain ⟨tw⟩ := RigidData.twistBy_eq_self cert.toRigidData u hrig hpow ▸ htw hrig
  obtain ⟨twist, twist_mem, φ_conj_pres⟩ := branchCycleTwist tw
    (fun i k hk => cert.rational i (tw.base i) (tw.base_mem.1 i) k hk)
  exact ⟨{
    E := tw.E
    N := tw.N
    φ := tw.φ
    pres := tw.pres
    surjPres := tw.surjPres
    base := tw.base
    base_mem := tw.base_mem
    φ_pres := tw.φ_pres
    twist := twist
    twist_mem := twist_mem
    φ_conj_pres := φ_conj_pres
    toRegular := descentTranslation tw }⟩

/-- The pre-digested arithmetic descent datum exists — **derived** from
`branchCycleDescentData_nonempty` via `ArithmeticDescentData.ofBranchCycle`, which proves the
inner-automorphism property from rigidity rather than assuming it. -/
theorem arithmeticDescentData_nonempty {G : Type} [Group G] [Finite G]
    (cert : RigidityCertificate G) :
    Nonempty (ArithmeticDescentData G) :=
  (branchCycleDescentData_nonempty cert).map ArithmeticDescentData.ofBranchCycle

/-- **Branch-cycle rationality descent** (the rigidity criterion's analytic-arithmetic core).

From a rigidity certificate (rational inertia classes, a rigid generating product-one tuple, and `G`
centerless), the geometric cover — a Galois extension of `ℚ̄(T)` with deck group `G`, produced by the
Riemann Existence Theorem over `ℚ̄` and packaged as a tame inertia model by
`geomInertiaModel_exists` — descends to a **regular** Galois extension of `ℚ(T)` with group `G`.

This is *not* an axiom.  Its proof is the branch-cycle argument (see the module docstring): the
**group-theoretic core** is assembled here — the *centerless extension lemma*
`Rigidity.RET.extend_surjective_of_inner`, whose inner-automorphism hypothesis is the rigidity
content of `Rigidity.RET.sphereHom_inner_equiv_of_rigid`, and whose uniqueness input is
`cert.center_triv`.  The arithmetic geometry Mathlib lacks is built in the descent modules feeding
`arithmeticDescentData_nonempty`. -/
theorem branch_cycle_descent {G : Type} [Group G] [Finite G]
    (cert : RigidityCertificate G) :
    IsRegularInverseGalois G := by
  -- The arithmetic descent datum exists (the Mathlib gaps live in the descent modules).
  obtain ⟨data⟩ := arithmeticDescentData_nonempty cert
  letI := data.groupE
  letI := data.normalN
  -- **Genuine group theory.**  Centerless (`cert.center_triv`) + the inner-automorphism property
  -- (branch-cycle + rationality + rigidity) extend the geometric monodromy `φ : N ↠ G` to the
  -- arithmetic monodromy `ψ : E ↠ G`, restricting to `φ` on `N`.
  obtain ⟨ψ, hψsurj, hψext⟩ :=
    Rigidity.RET.extend_surjective_of_inner data.N data.φ data.surjφ
      (center_triv_iff_center_eq_bot.mp cert.center_triv) data.inner
  -- The fixed field of `ker ψ` is the regular `ℚ(T)`-extension (field translation).
  exact data.toRegular ⟨ψ, hψsurj, hψext⟩

/-- **The rigidity criterion** (Völklein, *Groups as Galois Groups*, Thm 2.13): a group with a
rigidity certificate occurs as the Galois group of a *regular* extension of `ℚ(T)`.

This is the branch-cycle descent (`branch_cycle_descent`), whose deep geometric input — the Riemann
Existence Theorem over `ℚ̄`, producing the cover with its tame inertia data — enters through
`geomInertiaModel_exists` and the descent modules feeding `arithmeticDescentData_nonempty`. -/
theorem RigidityCertificate.isRegularInverseGalois {G : Type} [Group G] [Finite G]
    (cert : RigidityCertificate G) : IsRegularInverseGalois G :=
  branch_cycle_descent cert
