import InverseGalois.Rigidity.RET.Pi1.Etale.Fiber
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup

/-!
# The category of finite étale `K`-algebras and its fibre functor

This file assembles the *category-theoretic* substrate of the Grothendieck–Galois dictionary for a
field `K`: the category `FiniteEtaleAlgCat K` of finite étale `K`-algebras — realised as the full
subcategory of `CommAlgCat K` cut out by `Algebra.Etale K` — together with the **fibre functor**

>   `F : (FiniteEtaleAlgCat K)ᵒᵖ ⥤ FintypeCat`,     `F(A) = (A →ₐ[K] Ω)`

into finite sets, for a fixed field `Ω ⊇ K`.  The *opposite* category is the geometric one: an étale
`K`-algebra `A` is the coordinate ring of a finite étale cover `Spec A → Spec K`, and a morphism of
covers is an algebra map in the reverse direction, so covers form `(FiniteEtaleAlgCat K)ᵒᵖ` and the
fibre functor is covariant on it.  A `K`-point `A →ₐ[K] Ω` is a geometric point of the cover, and the
map on fibres induced by a cover morphism is precomposition.

The object-level content — that this functor takes finite values (`finite_algHom_of_etale`), that its
values carry the `Ω ≃ₐ[K] Ω`-action whose orbits are the connected components (`Fiber.lean`), and
that it is faithful and reflects connectedness — lives in `Etale/Fiber.lean`.  This file packages
that content as an honest `CategoryTheory.Functor`, the object onto which the `PreGaloisCategory` /
`FiberFunctor` axioms and the fundamental-group identification `Aut F ≅ Gal(Ω/K)` will attach.
-/

open CategoryTheory

namespace Rigidity.RET.Etale

universe u

variable (K : Type u) [Field K]

/-- The property of being a finite étale `K`-algebra, as an `ObjectProperty` on `CommAlgCat K`. -/
def isFiniteEtale : ObjectProperty (CommAlgCat.{u} K) := fun A => Algebra.Etale K A

/-- **The category of finite étale `K`-algebras.**  The full subcategory of `CommAlgCat K` on the
finite étale algebras.  Its opposite `(FiniteEtaleAlgCat K)ᵒᵖ` is the Galois category of finite étale
covers of `Spec K`. -/
abbrev FiniteEtaleAlgCat : Type (u + 1) := (isFiniteEtale K).FullSubcategory

namespace FiniteEtaleAlgCat

instance etale (A : FiniteEtaleAlgCat K) : Algebra.Etale K A.obj := A.property

/-- The `K`-algebra map underlying a morphism of finite étale `K`-algebras. -/
abbrev homAlg {A B : FiniteEtaleAlgCat K} (f : A ⟶ B) : A.obj →ₐ[K] B.obj :=
  ((isFiniteEtale K).ι.map f).hom

@[simp]
lemma homAlg_id (A : FiniteEtaleAlgCat K) : homAlg K (𝟙 A) = AlgHom.id K A.obj := by
  simp [homAlg]

@[simp]
lemma homAlg_comp {A B C : FiniteEtaleAlgCat K} (f : A ⟶ B) (g : B ⟶ C) :
    homAlg K (f ≫ g) = (homAlg K g).comp (homAlg K f) := by
  simp [homAlg]

variable (Ω : Type u) [Field Ω] [Algebra K Ω]

/-- The fibre of a finite étale `K`-algebra `A` is a finite type, via `finite_algHom_of_etale`. -/
noncomputable instance fibreFintype (A : FiniteEtaleAlgCat K) : Fintype (A.obj →ₐ[K] Ω) :=
  @Fintype.ofFinite _ (finite_algHom_of_etale)

/-- **The fibre functor** `F : (FiniteEtaleAlgCat K)ᵒᵖ ⥤ FintypeCat`, `F(A) = (A →ₐ[K] Ω)`.  On a
morphism of covers — an algebra map `φ : B.obj →ₐ[K] A.obj` in the *opposite* direction — it acts by
precomposition `g ↦ g ∘ φ`, sending a geometric point of the source cover to one of the target.  This
is the algebraic incarnation of "take the fibre of a cover over the geometric point `Spec Ω`". -/
noncomputable def fibreFunctor : (FiniteEtaleAlgCat K)ᵒᵖ ⥤ FintypeCat.{u} where
  obj A := FintypeCat.of (A.unop.obj →ₐ[K] Ω)
  map {A B} f := FintypeCat.homMk (fun g => g.comp (homAlg K f.unop))
  map_id A := by
    apply FintypeCat.hom_ext
    intro g
    show g.comp (homAlg K (𝟙 A.unop)) = g
    rw [homAlg_id]
    exact AlgHom.comp_id g
  map_comp {A B C} f h := by
    apply FintypeCat.hom_ext
    intro g
    show g.comp (homAlg K (f ≫ h).unop) = (g.comp (homAlg K f.unop)).comp (homAlg K h.unop)
    rw [unop_comp, homAlg_comp]
    exact (AlgHom.comp_assoc g (homAlg K f.unop) (homAlg K h.unop)).symm

/-- The monodromy action of `Ω ≃ₐ[K] Ω` on the values of the fibre functor: on `F(A) = (A →ₐ[K] Ω)`
it is post-composition (`fibreMulAction`).  These are the actions whose orbits are the connected
components of a cover. -/
noncomputable instance fibreMulActionObj (X : (FiniteEtaleAlgCat K)ᵒᵖ) :
    MulAction (Ω ≃ₐ[K] Ω) ((fibreFunctor K Ω).obj X) :=
  fibreMulAction

/-- **The Galois group acts naturally on the fibres.**  For every morphism of covers `f`, the
post-composition action of `Ω ≃ₐ[K] Ω` commutes with the induced map `F.map f` (which is
pre-composition): `F.map f (σ • x) = σ • F.map f x`.  This `IsNaturalSMul` witness is the naturality
half of exhibiting `Ω ≃ₐ[K] Ω` as the fundamental group of the fibre functor — it yields the
canonical `toAut : (Ω ≃ₐ[K] Ω) →* Aut F`. -/
instance : PreGaloisCategory.IsNaturalSMul (fibreFunctor K Ω) (Ω ≃ₐ[K] Ω) where
  naturality σ {X Y} f x := by
    show (σ.toAlgHom.comp x).comp (homAlg K f.unop)
        = σ.toAlgHom.comp (x.comp (homAlg K f.unop))
    exact AlgHom.comp_assoc _ _ _

/-- `K` itself, as an object of the category of finite étale `K`-algebras — the coordinate ring of
the base point `Spec K`, i.e. the trivial one-sheeted cover. -/
abbrev base : FiniteEtaleAlgCat K :=
  ⟨CommAlgCat.of K K, inferInstanceAs (Algebra.Etale K K)⟩

/-- **`K` is the initial object** of `FiniteEtaleAlgCat K`: into any finite étale `K`-algebra there is
a unique `K`-algebra map out of `K` (the structure map).  This is `CommAlgCat.isInitialSelf`
transported to the full subcategory. -/
noncomputable def baseIsInitial : Limits.IsInitial (base K) := by
  haveI : ∀ A : FiniteEtaleAlgCat K, Unique (base K ⟶ A) := by
    intro A
    refine { default := ObjectProperty.homMk (CommAlgCat.isInitialSelf.to A.obj), uniq := ?_ }
    intro m
    apply ObjectProperty.hom_ext
    exact CommAlgCat.isInitialSelf.hom_ext _ _
  exact Limits.IsInitial.ofUnique _

/-- **The terminal object of the Galois category `(FiniteEtaleAlgCat K)ᵒᵖ` is `op K`.**  Dually to
`baseIsInitial`: the base point is the terminal cover.  This is the `PreGaloisCategory` field G1
(`hasTerminal`). -/
noncomputable def opBaseIsTerminal : Limits.IsTerminal (Opposite.op (base K)) :=
  Limits.terminalOpOfInitial (baseIsInitial K)

instance : Limits.HasTerminal (FiniteEtaleAlgCat K)ᵒᵖ :=
  (opBaseIsTerminal K).hasTerminal

end FiniteEtaleAlgCat

end Rigidity.RET.Etale
