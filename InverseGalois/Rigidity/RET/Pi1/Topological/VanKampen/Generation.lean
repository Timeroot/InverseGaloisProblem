/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.VanKampen.Subdivision
import Mathlib.Topology.Homotopy.Path

/-!
# Reassembly of a subdivided path

Companion to `VanKampen/Subdivision.lean`.  Having chopped a path `γ` into subpaths each lying in a
single cover element (`exists_subpath_cover`), we reassemble: `γ` is homotopic to the concatenation
of those subpaths.  This is the reparametrization content, supplied by Mathlib's
`Path.Homotopic.concat_subpath`; here we combine it with the endpoint normalization `t 0 = 0`,
`t n = 1` so that the concatenation is honestly homotopic to `γ` itself.

Together with the subdivision, this is the **generation** half of the Seifert–van Kampen theorem:
every path — hence every morphism of the fundamental groupoid of `X` — is a composite of pieces each
supported in `U` or in `V`.

## Main declarations

* `Rigidity.RET.VanKampen.cast_concat_eq_subpath` — the reassembly at the level of endpoints: the
  full subpath `γ.subpath (t 0) (t n)` equals `γ` once the endpoints are normalized (`t 0 = 0`,
  `t n = 1`).
* `Rigidity.RET.VanKampen.mk_eq_cast_concat` — the generation identity in the fundamental groupoid:
  the homotopy class of `γ` is (a reindexing of) the class of the concatenation of its subpaths.
* `Rigidity.RET.VanKampen.exists_homotopic_concat_cover` — the packaged generation statement: a
  cover-adapted subdivision whose subpath-concatenation represents the class of `γ`.
-/

open Set unitInterval Path Fin

namespace Rigidity.RET.VanKampen

variable {X : Type*} [TopologicalSpace X]

/-- With normalized endpoints `t 0 = 0`, `t n = 1`, the subpath of `γ` spanning the whole partition
is, after the harmless endpoint recast, literally `γ`.  (The underlying function of a subpath from
`0` to `1` is `γ` itself.) -/
theorem cast_concat_eq_subpath {a b : X} (γ : Path a b) {n : ℕ} (t : Fin (n + 1) → I)
    (h0 : t 0 = 0) (h1 : t (Fin.last n) = 1)
    (hx : a = γ (t 0)) (hy : b = γ (t (Fin.last n))) :
    (γ.subpath (t 0) (t (Fin.last n))).cast hx hy = γ := by
  ext s
  simp only [Path.cast_coe, Path.subpath, Path.coe_mk_mk, Function.comp_apply, h0, h1]
  congr 1
  apply Subtype.ext
  simp [subpathAux]

/-- **Generation identity (groupoid form).**  In the fundamental groupoid, the homotopy class of a
path `γ` is the class of the concatenation of its subpaths along any endpoint-normalized partition
(reindexed by the harmless endpoint casts).  This is the reassembly half of Seifert–van Kampen: it
says every morphism of `π(X)` is the composite of the morphisms of its subpaths. -/
theorem mk_eq_cast_concat {a b : X} (γ : Path a b) {n : ℕ} (t : Fin (n + 1) → I)
    (h0 : t 0 = 0) (h1 : t (Fin.last n) = 1) :
    (⟦γ⟧ : Path.Homotopic.Quotient a b)
      = Path.Homotopic.Quotient.cast
          ⟦concat (γ ∘ t) fun k => γ.subpath (t k.castSucc) (t k.succ)⟧
          (show a = (γ ∘ t) 0 by rw [Function.comp_apply, h0]; exact γ.source.symm)
          (show b = (γ ∘ t) (Fin.last n) by rw [Function.comp_apply, h1]; exact γ.target.symm) := by
  have hx : a = γ (t 0) := by rw [h0]; exact γ.source.symm
  have hy : b = γ (t (Fin.last n)) := by rw [h1]; exact γ.target.symm
  -- The concatenation is homotopic to the full subpath …
  have hc : (⟦concat (γ ∘ t) fun k => γ.subpath (t k.castSucc) (t k.succ)⟧
      : Path.Homotopic.Quotient ((γ ∘ t) 0) ((γ ∘ t) (Fin.last n)))
      = ⟦γ.subpath (t 0) (t (Fin.last n))⟧ :=
    Quotient.sound (Path.Homotopic.concat_subpath γ t)
  -- `Quotient.cast ⟦p⟧ hx hy` is definitionally `⟦p.cast hx hy⟧`, and the recast full subpath is `γ`.
  rw [hc]
  exact (congrArg (fun p => (⟦p⟧ : Path.Homotopic.Quotient a b))
    (cast_concat_eq_subpath γ t h0 h1 hx hy)).symm

/-- **Generation (packaged).**  For an open cover `X = U ∪ V` and any path `γ`, there is a finite
subdivision of `γ` into subpaths each supported in `U` or in `V`, and the homotopy class of `γ` is
the (reindexed) class of the concatenation of those subpaths.  This packages `exists_subpath_cover`
with the reassembly identity `mk_eq_cast_concat`. -/
theorem exists_homotopic_concat_cover (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) {a b : X} (γ : Path a b) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I) (h0 : t 0 = 0) (h1 : t (Fin.last n) = 1), Monotone t ∧
      (∀ k : Fin n, (range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U) ∨
                    (range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V)) ∧
      (⟦γ⟧ : Path.Homotopic.Quotient a b)
        = Path.Homotopic.Quotient.cast
            ⟦concat (γ ∘ t) fun k => γ.subpath (t k.castSucc) (t k.succ)⟧
            (show a = (γ ∘ t) 0 by rw [Function.comp_apply, h0]; exact γ.source.symm)
            (show b = (γ ∘ t) (Fin.last n) by rw [Function.comp_apply, h1]; exact γ.target.symm) := by
  obtain ⟨n, t, h0, h1, hmono, hcov⟩ := exists_subpath_cover U V hU hV hUV γ
  exact ⟨n, t, h0, h1, hmono, hcov, mk_eq_cast_concat γ t h0 h1⟩

end Rigidity.RET.VanKampen
