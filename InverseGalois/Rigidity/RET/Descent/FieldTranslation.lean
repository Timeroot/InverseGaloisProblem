/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Descent.Data
import InverseGalois.Rigidity.RET.Descent.RegularFixedField
import InverseGalois.Rigidity.RET.GeometricIrreducibility

/-!
# Module D — field translation: the fixed field of `ker ψ` is a regular `ℚ(T)`-extension

Over a `GeomTower G cert`, once the centerless extension lemma has produced the arithmetic monodromy
`ψ : E ↠ G` extending the geometric monodromy `φ : N ↠ G`, this module carries that homomorphism
back to a **regular** Galois extension of `ℚ(T)` realizing `G` — i.e. it discharges the `toRegular`
field of `BranchCycleDescentData`.

## The mathematics *(genuine field theory)*

Let `L' = Ω^{ker ψ}` be the fixed field of `ker ψ`.  Then:

* `L'/ℚ(T)` is Galois with `Gal(L'/ℚ(T)) ≃ E / ker ψ ≃ G` (`ψ` surjective) — the fundamental
  theorem of Galois theory (`IsGalois`, `IntermediateField.fixedField`, and the
  `Gal ≃ E/ker` isomorphism).
* **Regularity.**  Because `ψ|_N = φ` is *surjective*, `N` already surjects onto `G`, so
  `ker ψ · N = E` and `ker ψ ∩ N` has index `|G|` in `N`.  Equivalently the field of constants of
  `L'` is `ℚ`: `L' ∩ ℚ̄(T) = ℚ(T)`, i.e. `algebraicClosure ℚ L' = ⊥`.  This is the regularity
  condition of `IsRegularInverseGalois`, and it is exactly what the surjectivity of `ψ|_N` buys.

Both bullets are Mathlib-expressible Galois theory over the tower built in `Descent.Tower`; the
module has **no irreducible arithmetic-geometry input** — it is genuine field theory, contingent only
on the tower's field data (which is why `descentTranslation` takes the tower `tw`, not just abstract
groups: the regularity computation needs the field realization).

Both bullets are carried out by `Rigidity.RET.isRegularGaloisGroupOverBase_fixedField`
(`Descent.RegularFixedField`), stated over an arbitrary base `F / k` regular over its constant
field; what remains here is to transport the abstract monodromy `ψ : E ↠ G` to the concrete Galois
group `Gal(Ω/ℚ(T))` and to check its surjectivity on the geometric part.

## Main result

* `descentTranslation` — the `toRegular` field of the descent datum.
-/

open Polynomial

open scoped IntermediateField

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **Module D.**  The field translation: given the arithmetic monodromy `ψ : E ↠ G` extending the
geometric monodromy `φ : N ↠ G` over the tower `tw`, the fixed field `Ω^{ker ψ}` is a **regular**
Galois extension of `ℚ(T)` with group `G`.

This is genuine field theory (fixed fields + a regularity computation): the surjectivity of `ψ|_N`
forces the field of constants to be `ℚ`, giving `algebraicClosure ℚ L' = ⊥`.  There is no
irreducible arithmetic-geometry input — only the tower's field realization.  See
`DESCENT_ROADMAP.md` §1.4 and the module docstring. -/
theorem descentTranslation {G : Type} [Group G] [Finite G] {cert : RigidityCertificate G}
    (tw : GeomTower G cert) :
    (∃ ψ : tw.E →* G, Function.Surjective ψ ∧ ∀ n : tw.N, ψ (n : tw.E) = tw.φ n) →
      IsRegularInverseGalois G := by
  rintro ⟨ψ, hψsurj, hψext⟩
  classical
  -- Transport the abstract arithmetic monodromy to the actual Galois group `Gal(Ω/ℚ(T))`.
  let ψ' : (tw.Ω ≃ₐ[RatFunc ℚ] tw.Ω) →* G := ψ.comp tw.galE.symm.toMonoidHom
  have hψ'surj : Function.Surjective ψ' := hψsurj.comp tw.galE.symm.surjective
  -- The geometric monodromy `φ` is surjective (its sphere hom `sphereHom base` is, and `pres` is).
  have hφsurj : Function.Surjective tw.φ := by
    intro g
    have hs : Function.Surjective (Rigidity.RET.sphereHom tw.base tw.base_mem.2.1) :=
      (Rigidity.RET.sphereHom_surjective_iff tw.base tw.base_mem.2.1).2 tw.base_mem.2.2
    obtain ⟨x, hx⟩ := hs g
    exact ⟨tw.pres x, by rw [tw.φ_pres x, hx]⟩
  -- `ψ'` is already surjective on `N' = Gal(Ω/ℚ̄(T)) = geomBase.fixingSubgroup`.
  have hψ'N : ∀ g : G, ∃ n' ∈ tw.geomBase.fixingSubgroup, ψ' n' = g := by
    intro g
    obtain ⟨n, hn⟩ := hφsurj g
    refine ⟨tw.galE (n : tw.E), (tw.galN_iff (n : tw.E)).mp n.2, ?_⟩
    show ψ (tw.galE.symm (tw.galE (n : tw.E))) = g
    rw [tw.galE.symm_apply_apply, hψext n, hn]
  exact isRegularInverseGalois_of_overBase _
    (Rigidity.RET.isRegularGaloisGroupOverBase_fixedField Rigidity.RET.regular_ratFunc
      tw.geomBase tw.const_le_geomBase ψ' hψ'surj hψ'N)
