/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.VanKampen.Generation
import InverseGalois.Rigidity.RET.Pi1.Topological.VanKampen.Bridge

/-!
# Seifert–van Kampen: the uniqueness half

The pushout universal property has two halves.  This file proves the **uniqueness** half: two
functors out of `π(X)` that agree, after restriction along the inclusions, on `π(U)` and `π(V)` are
equal.  Equivalently, `π(X)` is *generated* by the images of the inclusion functors, so a functor
out of it is determined by its restrictions to `π(U)` and `π(V)`.

The proof is the generation analysis of `Subdivision.lean` / `Generation.lean` / `Bridge.lean`:

* on objects, every point of `X` lies in `U` or `V`, so object values are pinned by the
  restrictions (`obj_eq_of_restrictions`);
* on morphisms, every class `⟦γ⟧` is (a recast of) a concatenation of subpath classes
  (`mk_eq_cast_concat`), and each subpath class comes from `π(U)` or `π(V)` (the `Bridge` lemmas),
  where the two functors agree.  Agreement propagates along composition, identities, and endpoint
  recasts.

## Main declarations

* `Rigidity.RET.VanKampen.functor_ext_of_restrictions` — a functor `π(X) ⥤ H` is determined by its
  composites with the two inclusion functors.
-/

universe u v w

open CategoryTheory FundamentalGroupoid Set unitInterval

namespace Rigidity.RET.VanKampen

variable {X : Type u} [TopologicalSpace X]
variable {H : Type v} [Category.{w} H]

/-- **Object determination.**  If two functors out of `π(X)` agree, after restriction along the
inclusions, on `π(U)` and on `π(V)`, then they agree on every object of `π(X)` (because every point
of `X` lies in `U` or in `V`). -/
theorem obj_eq_of_restrictions (U V : Set X) (hUV : U ∪ V = univ)
    (Φ Ψ : FundamentalGroupoid X ⥤ H)
    (hU : FundamentalGroupoid.map (inclUX U) ⋙ Φ = FundamentalGroupoid.map (inclUX U) ⋙ Ψ)
    (hV : FundamentalGroupoid.map (inclVX V) ⋙ Φ = FundamentalGroupoid.map (inclVX V) ⋙ Ψ)
    (x : FundamentalGroupoid X) : Φ.obj x = Ψ.obj x := by
  have hx : x.as ∈ U ∪ V := by rw [hUV]; trivial
  rcases hx with hxU | hxV
  · have := Functor.congr_obj hU (⟨⟨x.as, hxU⟩⟩ : FundamentalGroupoid U)
    simpa [FundamentalGroupoid.map, inclUX] using this
  · have := Functor.congr_obj hV (⟨⟨x.as, hxV⟩⟩ : FundamentalGroupoid V)
    simpa [FundamentalGroupoid.map, inclVX] using this

variable (Φ Ψ : FundamentalGroupoid X ⥤ H) (E : ∀ z, Φ.obj z = Ψ.obj z)

/-- Two functors "agree" on a morphism `f : a ⟶ b` (relative to a fixed object-agreement `E`) when
their images differ only by the `eqToHom` bookkeeping forced by `E`. -/
def AgrM {a b : FundamentalGroupoid X} (f : a ⟶ b) : Prop :=
  Φ.map f = eqToHom (E a) ≫ Ψ.map f ≫ eqToHom (E b).symm

theorem agrM_id (a : FundamentalGroupoid X) : AgrM Φ Ψ E (𝟙 a) := by
  simp [AgrM]

theorem agrM_eqToHom {a b : FundamentalGroupoid X} (h : a = b) :
    AgrM Φ Ψ E (eqToHom h) := by
  subst h; simp [AgrM]

theorem agrM_comp {a b c : FundamentalGroupoid X} {f : a ⟶ b} {g : b ⟶ c}
    (hf : AgrM Φ Ψ E f) (hg : AgrM Φ Ψ E g) : AgrM Φ Ψ E (f ≫ g) := by
  simp only [AgrM, Functor.map_comp] at hf hg ⊢
  rw [hf, hg]
  simp

/-- Agreement is stable under the harmless endpoint recast of a morphism. -/
theorem agrM_cast {a b a' b' : X} (q : Path.Homotopic.Quotient a' b') (hx : a = a') (hy : b = b')
    (hq : AgrM Φ Ψ E (q : (⟨a'⟩ : FundamentalGroupoid X) ⟶ ⟨b'⟩)) :
    AgrM Φ Ψ E (Path.Homotopic.Quotient.cast q hx hy : (⟨a⟩ : FundamentalGroupoid X) ⟶ ⟨b⟩) := by
  subst hx; subst hy
  have hc : Path.Homotopic.Quotient.cast q rfl rfl = q := by simp
  rw [hc]; exact hq

/-- A subpath lying in `U` is agreed upon: its class comes from `π(U)`, where `Φ` and `Ψ` agree. -/
theorem agrM_piece_U (U : Set X)
    (hU : FundamentalGroupoid.map (inclUX U) ⋙ Φ = FundamentalGroupoid.map (inclUX U) ⋙ Ψ)
    {a b : X} (γ : Path a b) (t₀ t₁ : I) (h : range (γ.subpath t₀ t₁) ⊆ U) :
    AgrM Φ Ψ E (⟦γ.subpath t₀ t₁⟧ : (⟨γ t₀⟩ : FundamentalGroupoid X) ⟶ ⟨γ t₁⟩) := by
  obtain ⟨m0, m1, δ, hδ⟩ := mk_subpath_eq_mapUX U γ t₀ t₁ h
  simp only [AgrM, ← hδ]
  exact Functor.congr_hom hU δ

/-- A subpath lying in `V` is agreed upon: its class comes from `π(V)`, where `Φ` and `Ψ` agree. -/
theorem agrM_piece_V (V : Set X)
    (hV : FundamentalGroupoid.map (inclVX V) ⋙ Φ = FundamentalGroupoid.map (inclVX V) ⋙ Ψ)
    {a b : X} (γ : Path a b) (t₀ t₁ : I) (h : range (γ.subpath t₀ t₁) ⊆ V) :
    AgrM Φ Ψ E (⟦γ.subpath t₀ t₁⟧ : (⟨γ t₀⟩ : FundamentalGroupoid X) ⟶ ⟨γ t₁⟩) := by
  obtain ⟨m0, m1, δ, hδ⟩ := mk_subpath_eq_mapVX V γ t₀ t₁ h
  simp only [AgrM, ← hδ]
  exact Functor.congr_hom hV δ

/-- Agreement propagates through a concatenation of paths. -/
theorem agrM_concat {m : ℕ} (p : Fin (m + 1) → X)
    (F : (k : Fin m) → Path (p k.castSucc) (p k.succ))
    (hF : ∀ k, AgrM Φ Ψ E (⟦F k⟧ : (⟨p k.castSucc⟩ : FundamentalGroupoid X) ⟶ ⟨p k.succ⟩)) :
    AgrM Φ Ψ E (⟦Path.concat p F⟧ : (⟨p 0⟩ : FundamentalGroupoid X) ⟶ ⟨p (Fin.last m)⟩) := by
  induction m with
  | zero =>
    have h0 : (⟦Path.concat p F⟧ : (⟨p 0⟩ : FundamentalGroupoid X) ⟶ ⟨p (Fin.last 0)⟩)
        = 𝟙 (⟨p 0⟩ : FundamentalGroupoid X) := by rw [Path.concat_zero]; rfl
    rw [h0]; exact agrM_id Φ Ψ E _
  | succ m ih =>
    have hsucc : (⟦Path.concat p F⟧ : (⟨p 0⟩ : FundamentalGroupoid X) ⟶ ⟨p (Fin.last (m + 1))⟩)
        = (((⟦Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)⟧ :
              (⟨p 0⟩ : FundamentalGroupoid X) ⟶ ⟨p (Fin.last m).castSucc⟩)
            ≫ (⟦F (Fin.last m)⟧ :
              (⟨p (Fin.last m).castSucc⟩ : FundamentalGroupoid X) ⟶ ⟨p (Fin.last m).succ⟩)) :
            (⟨p 0⟩ : FundamentalGroupoid X) ⟶ ⟨p (Fin.last (m + 1))⟩) := by
      rw [Path.concat_succ]; rfl
    rw [hsucc]
    exact agrM_comp Φ Ψ E
      (ih (p ∘ Fin.castSucc) (fun k => F k.castSucc) (fun k => hF k.castSucc))
      (hF (Fin.last m))

/-- Agreement on every homotopy class of paths, by subdivision + generation. -/
theorem agrM_mk (U V : Set X) (hUopen : IsOpen U) (hVopen : IsOpen V) (hUV : U ∪ V = univ)
    (hU : FundamentalGroupoid.map (inclUX U) ⋙ Φ = FundamentalGroupoid.map (inclUX U) ⋙ Ψ)
    (hV : FundamentalGroupoid.map (inclVX V) ⋙ Φ = FundamentalGroupoid.map (inclVX V) ⋙ Ψ)
    {a b : X} (γ : Path a b) :
    AgrM Φ Ψ E (⟦γ⟧ : (⟨a⟩ : FundamentalGroupoid X) ⟶ ⟨b⟩) := by
  obtain ⟨n, t, h0, h1, _, hcov, hgen⟩ :=
    exists_homotopic_concat_cover U V hUopen hVopen hUV γ
  have hcc : AgrM Φ Ψ E (⟦Path.concat (γ ∘ t) fun k => γ.subpath (t k.castSucc) (t k.succ)⟧
      : (⟨(γ ∘ t) 0⟩ : FundamentalGroupoid X) ⟶ ⟨(γ ∘ t) (Fin.last n)⟩) := by
    refine agrM_concat Φ Ψ E (γ ∘ t) _ ?_
    intro k
    rcases hcov k with hk | hk
    · exact agrM_piece_U Φ Ψ E U hU γ (t k.castSucc) (t k.succ) hk
    · exact agrM_piece_V Φ Ψ E V hV γ (t k.castSucc) (t k.succ) hk
  rw [hgen]
  exact agrM_cast Φ Ψ E _ _ _ hcc

/-- **Seifert–van Kampen, uniqueness half.**  A functor out of `π(X)` is determined by its
composites with the inclusion functors of an open cover `X = U ∪ V`. -/
theorem functor_ext_of_restrictions (U V : Set X) (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hUV : U ∪ V = univ)
    (hU : FundamentalGroupoid.map (inclUX U) ⋙ Φ = FundamentalGroupoid.map (inclUX U) ⋙ Ψ)
    (hV : FundamentalGroupoid.map (inclVX V) ⋙ Φ = FundamentalGroupoid.map (inclVX V) ⋙ Ψ) :
    Φ = Ψ := by
  refine CategoryTheory.Functor.ext (obj_eq_of_restrictions U V hUV Φ Ψ hU hV) ?_
  intro a b f
  induction f using Quotient.inductionOn with
  | h γ =>
    exact agrM_mk Φ Ψ (obj_eq_of_restrictions U V hUV Φ Ψ hU hV)
      U V hUopen hVopen hUV hU hV γ

end Rigidity.RET.VanKampen
