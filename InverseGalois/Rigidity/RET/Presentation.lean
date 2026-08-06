/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finite.Card

/-!
# L1: the sphere presentation group `Γ_r` and the tuple ↔ surjection correspondence

The classical Riemann Existence Theorem is stated for the fundamental group of the `r`-punctured
sphere, `π₁(ℙ¹(ℂ) ∖ {p₁,…,p_r}) ≅ ⟨x₁,…,x_r | x₁···x_r = 1⟩`.  Its *algebraic shadow* — all that
the rigidity method actually consumes — is the finitely-presented group

  `Γ_r = ⟨x₀,…,x_{r-1} | x₀·x₁···x_{r-1} = 1⟩`,

here `SphereGroup r`, together with the elementary dictionary between its finite quotients and the
generating product-one tuples that a `RigidityCertificate` records.  This layer is pure group theory;
every Mathlib prerequisite (`FreeGroup`, `PresentedGroup`, the `toGroup` universal property) exists.

## Main definitions / results

* `Rigidity.RET.SphereGroup r` — the presentation group `Γ_r`.
* `Rigidity.RET.sphereHom` — the hom `Γ_r →* G` induced by a product-one tuple `g : Fin r → G`.
* `Rigidity.RET.sphereHom_of` — it sends the `i`-th generator to `g i`.
* `Rigidity.RET.sphereHom_surjective_iff` — it is surjective iff `g` generates `G`.
* `Rigidity.RET.sphereHom_conj` — simultaneous conjugation of the tuple ↔ post-composition by the
  inner automorphism `conj c` (covers ↔ surjections up to conjugacy).
* `Rigidity.RET.sphereGroup_mulEquiv_free` — `Γ_r ≅ FreeGroup (Fin (r-1))` for `r ≥ 1`.
-/

namespace Rigidity.RET

variable {r : ℕ} {G : Type*} [Group G]

/-- The single defining relation `x₀·x₁···x_{r-1} = 1` of `Γ_r`, as an element of the free group. -/
def sphereRel (r : ℕ) : Set (FreeGroup (Fin r)) :=
  {(List.ofFn fun i => FreeGroup.of i).prod}

/-- **The sphere presentation group** `Γ_r = ⟨x₀,…,x_{r-1} | x₀···x_{r-1} = 1⟩`: the algebraic
shadow of `π₁(ℙ¹(ℂ) ∖ {r points})`. -/
abbrev SphereGroup (r : ℕ) := PresentedGroup (sphereRel r)

/-- A product-one tuple satisfies the sphere relation under the free-group lift, so it induces a
hom out of `Γ_r`. -/
theorem lift_sphereRel_eq_one (g : Fin r → G) (hg : (List.ofFn g).prod = 1) :
    ∀ x ∈ sphereRel r, FreeGroup.lift g x = 1 := by
  rintro x hx
  simp only [sphereRel, Set.mem_singleton_iff] at hx
  subst hx
  rw [map_list_prod, List.map_ofFn]
  have hfun : (⇑(FreeGroup.lift g) ∘ fun i => FreeGroup.of i) = g := by
    funext i; simp only [Function.comp_apply, FreeGroup.lift_apply_of]
  rw [hfun]; exact hg

/-- The hom `Γ_r →* G` induced by a generating-agnostic product-one tuple `g`. -/
def sphereHom (g : Fin r → G) (hg : (List.ofFn g).prod = 1) : SphereGroup r →* G :=
  PresentedGroup.toGroup (lift_sphereRel_eq_one g hg)

@[simp]
theorem sphereHom_of (g : Fin r → G) (hg : (List.ofFn g).prod = 1) (i : Fin r) :
    sphereHom g hg (PresentedGroup.of i) = g i :=
  PresentedGroup.toGroup.of _

/-- The induced hom `Γ_r →* G` is surjective exactly when the tuple generates `G`.  This is the
group-theoretic content of "connected cover ↔ transitive monodromy". -/
theorem sphereHom_surjective_iff (g : Fin r → G) (hg : (List.ofFn g).prod = 1) :
    Function.Surjective (sphereHom g hg) ↔ Subgroup.closure (Set.range g) = ⊤ := by
  have hrange : (sphereHom g hg).range = Subgroup.closure (Set.range g) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of (sphereRel r),
      MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (sphereHom_of g hg i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨PresentedGroup.of i, ⟨i, rfl⟩, sphereHom_of g hg i⟩
  rw [← MonoidHom.range_eq_top, hrange]

/-- Conjugating a product-one tuple coordinatewise keeps it product-one: the conjugate of the
product is the product of the conjugates, and `c · 1 · c⁻¹ = 1`. -/
theorem prod_conj_eq_one (g : Fin r → G) (hg : (List.ofFn g).prod = 1) (c : G) :
    (List.ofFn fun i => MulAut.conj c (g i)).prod = 1 := by
  set f : G →* G := (MulAut.conj c).toMonoidHom with hf
  have hlist : (List.ofFn fun i => MulAut.conj c (g i)) = (List.ofFn g).map f := by
    rw [List.map_ofFn]; rfl
  rw [hlist, ← map_list_prod f, hg, map_one]

/-- **Simultaneous conjugation ↔ post-composition by an inner automorphism.**  The hom induced by
the coordinatewise `c`-conjugate of `g` is `(conj c) ∘ sphereHom g`.  This is the algebraic shadow
of "a connected cover is determined by its monodromy surjection *only up to conjugacy*": the inner
automorphisms of `G` act on the surjections `Γ_r ↠ G` exactly as simultaneous conjugation acts on
the generating product-one tuples.  It is the interface the branch-cycle descent (L2) plugs into. -/
theorem sphereHom_conj (g : Fin r → G) (hg : (List.ofFn g).prod = 1) (c : G) :
    sphereHom (fun i => MulAut.conj c (g i)) (prod_conj_eq_one g hg c)
      = (MulAut.conj c).toMonoidHom.comp (sphereHom g hg) := by
  ext i
  simp

/-- **`Γ_r` is free of rank `r - 1`** (for `r ≥ 1`): the single product-one relation lets one
generator be eliminated.  This mirrors `π₁` of the punctured sphere being free on `r - 1` loops. -/
theorem sphereGroup_mulEquiv_free (hr : 1 ≤ r) :
    Nonempty (SphereGroup r ≃* FreeGroup (Fin (r - 1))) := by
  induction r with
  | zero => omega
  | succ r hr =>
  -- Goal: SphereGroup (r+1) ≃* FreeGroup (Fin r)
  let freeProds : FreeGroup (Fin r) := (List.ofFn (fun j : Fin r => FreeGroup.of j)).prod
  let toSphere : FreeGroup (Fin r) →* SphereGroup (r + 1) :=
    FreeGroup.lift (fun i => PresentedGroup.of (Fin.castSucc i))
  -- toFree sends last to inverse of freeProds, others to corresponding generator
  let toFree : Fin (r + 1) → FreeGroup (Fin r) := fun i =>
    if h : i.val < r then FreeGroup.of ⟨i.val, h⟩ else freeProds⁻¹
  -- Key lemma: List.ofFn toFree = List.ofFn (free generators on Fin r) ++ [freeProds⁻¹]
  have hlist : List.ofFn toFree = List.ofFn (fun j : Fin r => FreeGroup.of j) ++ [freeProds⁻¹] := by
    apply List.ext_get
    · simp [List.length_ofFn, List.length_append]
    · intro i hi
      simp only [List.get_ofFn]
      intro h₂
      have hi' : i < r + 1 := by
        simp [List.length_ofFn] at hi; omega
      by_cases h : i < r
      · simp [h, toFree]
      · simp [not_lt.mp h, toFree]
  have hrel : (List.ofFn (fun i : Fin (r + 1) => toFree i)).prod = 1 := by
    rw [hlist, List.prod_append, List.prod_singleton, mul_inv_cancel]
  -- sphereHom toFree hrel : SphereGroup (r+1) →* FreeGroup (Fin r)
  let fwd := sphereHom toFree hrel
  -- FreeGroup.lift toSphere : FreeGroup (Fin r) →* SphereGroup (r+1)
  let bwd := toSphere
  -- fwd ∘ bwd = id on FreeGroup (Fin r)
  have hfwd_bwd : fwd.comp bwd = MonoidHom.id _ := by
    have hgen : ∀ j : Fin r, fwd (bwd (FreeGroup.of j)) = FreeGroup.of j := by
      intro j
      show fwd (bwd (FreeGroup.of j)) = FreeGroup.of j
      simp only [bwd, toSphere]
      show sphereHom toFree hrel (PresentedGroup.of j.castSucc) = FreeGroup.of j
      rw [sphereHom_of toFree hrel (Fin.castSucc j)]
      simp [toFree, Fin.castSucc]
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    rw [hgen x]
  -- bwd ∘ fwd = id on SphereGroup (r+1)
  -- It suffices to show it's id on generators (PresentedGroup.of i for i : Fin (r+1))
  -- First establish the sphere relation in SphereGroup (r+1)
  let sphereProd : FreeGroup (Fin (r + 1)) := (List.ofFn (fun i : Fin (r + 1) => FreeGroup.of i)).prod
  have hmem : sphereProd ∈ sphereRel (r + 1) := by
    dsimp [sphereRel]; exact rfl
  have hrelSG : (List.ofFn (fun i : Fin (r + 1) => PresentedGroup.of i : Fin (r + 1) → SphereGroup (r + 1))).prod = 1 := by
    -- The product of generators = `mk sphereProd`, and the relator `sphereProd ∈ sphereRel` dies.
    have h1 : (List.ofFn (fun i : Fin (r + 1) => PresentedGroup.of i)).prod
        = PresentedGroup.mk (sphereRel (r + 1)) sphereProd := by
      dsimp only [sphereProd]
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [h1]
    exact PresentedGroup.one_of_mem hmem
  have hbwd_fwd_gen : ∀ i : Fin (r + 1), bwd.comp fwd (PresentedGroup.of i) = PresentedGroup.of i := by
    intro i
    show bwd (sphereHom toFree hrel (PresentedGroup.of i)) = PresentedGroup.of i
    rw [sphereHom_of toFree hrel i]
    by_cases h : i.val < r
    · have hi : i = Fin.castSucc ⟨i.val, h⟩ := Fin.ext (by simp)
      rw [hi]
      simp [h, toFree, bwd, toSphere]
    · -- i.val ≥ r, and i : Fin (r+1), so i.val = r, i = Fin.last r
      have hi_lt : (i : ℕ) < r + 1 := i.is_lt
      have hi_eq_r : (i : ℕ) = r := by omega
      have hi_last : i = Fin.last r := Fin.ext hi_eq_r
      rw [hi_last]
      simp [toFree]
      have hbwd_fp : bwd freeProds = (List.ofFn (fun j : Fin r => PresentedGroup.of (rels := sphereRel (r + 1)) (j.castSucc))).prod := by
        simp [bwd, toSphere, freeProds, map_list_prod, List.map_ofFn]
        congr 1
      show (bwd freeProds)⁻¹ = PresentedGroup.of (rels := sphereRel (r + 1)) (Fin.last r)
      rw [hbwd_fp]
      -- From hrelSG and hdecomp_prod: (list_prod_castSucc) * of(last r) = 1
      have hdecomp_prod : ∀ (n : ℕ) (G : Type) [Monoid G] (g : Fin (n + 1) → G),
          (List.ofFn g).prod = ((List.ofFn (fun j : Fin n => g (Fin.castSucc j))).prod) * g (Fin.last n) := by
        intro n G _ g
        have hlist_ofFn_append : ∀ (n : ℕ) (G : Type) [Monoid G] (g : Fin (n + 1) → G),
            List.ofFn g = List.ofFn (fun j : Fin n => g (Fin.castSucc j)) ++ [g (Fin.last n)] := by
          intro n G _ g
          apply List.ext_get
          · simp [List.length_ofFn, List.length_append]
          · intro i hi
            simp only [List.get_ofFn]
            intro h₂
            by_cases h : i < n
            · simp [h, Fin.castSucc]
            · simp [List.length_ofFn, List.length_append] at h₂
              have hi_eq_n : i = n := by omega
              subst hi_eq_n
              simp [Fin.last]
        rw [hlist_ofFn_append n G g, List.prod_append, List.prod_singleton]
      have hdecomp := hdecomp_prod r (PresentedGroup (rels := sphereRel (r + 1))) (fun i => PresentedGroup.of i)
      have hmul : ((List.ofFn (fun j : Fin r => PresentedGroup.of (rels := sphereRel (r + 1)) (j.castSucc))).prod) * PresentedGroup.of (rels := sphereRel (r + 1)) (Fin.last r) = 1 := by
        rw [← hdecomp, hrelSG]
      rw [eq_inv_of_mul_eq_one_left hmul, inv_inv]
  have hbwd_fwd : bwd.comp fwd = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro i
    exact hbwd_fwd_gen i
  exact ⟨{
    toFun := fwd
    invFun := bwd
    left_inv := fun x => by exact congr_arg (fun f => f x) hbwd_fwd
    right_inv := fun x => by exact congr_arg (fun f => f x) hfwd_bwd
    map_mul' := fwd.map_mul
  }⟩

/-- **Every finite group is a quotient of some sphere group.**

Because `Γ_r` is free of rank `r - 1` (`sphereGroup_mulEquiv_free`), a surjection `Γ_r ↠ G` is
exactly a generating `(r-1)`-tuple of `G`.  Taking `r = |G| + 1` and the tuple listing every
element of `G` gives one, so the *group-theoretic* side of the Riemann Existence correspondence
imposes no condition at all on a finite `G`: all of that correspondence's content lies in
producing an actual cover from such a surjection. -/
theorem exists_sphereGroup_surjective [Finite G] :
    ∃ (r : ℕ) (φ : SphereGroup r →* G), Function.Surjective φ := by
  classical
  set e : Fin (Nat.card G) ≃ G := (Finite.equivFin G).symm with he
  refine ⟨Nat.card G + 1,
    (FreeGroup.lift (e : Fin (Nat.card G) → G)).comp
      (sphereGroup_mulEquiv_free (r := Nat.card G + 1) (by omega)).some.toMonoidHom,
    fun g => ?_⟩
  refine ⟨(sphereGroup_mulEquiv_free (r := Nat.card G + 1) (by omega)).some.symm
    (FreeGroup.of (e.symm g)), ?_⟩
  simp

end Rigidity.RET
