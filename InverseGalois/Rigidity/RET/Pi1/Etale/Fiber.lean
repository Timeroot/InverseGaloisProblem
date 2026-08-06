/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The fibre of a finite étale algebra

For the Grothendieck–Galois dictionary between finite covers and finite field extensions, the
**fibre functor** sends a finite étale `K`-algebra `A` to the finite set of `K`-algebra
embeddings `A →ₐ[K] Ω` into a fixed algebraically closed field `Ω ⊇ K`.  This file establishes the
fibre's basic invariant — its cardinality equals the `K`-dimension of `A` — which is the algebraic
shadow of "the degree of a cover equals the number of sheets".

The engine is the structure theorem for étale algebras over a field
(`Algebra.Etale.iff_exists_algEquiv_prod`: a finite étale `K`-algebra is a finite product of finite
separable field extensions), combined with the classical embedding count
(`AlgHom.card`: a finite separable extension has exactly `[E : K]` embeddings into an algebraically
closed field).  The bridge between them is the fact that an algebra map out of a finite product of
rings into a *field* factors through exactly one projection — `reassemble_bijective` below — which is
the ring-theoretic heart of this file.

## Main results

* `natCard_algHom_pi` — `Nat.card ((Π i, L i) →ₐ[K] Ω) = ∑ i, Nat.card (L i →ₐ[K] Ω)` when `Ω` is a
  field: an algebra map out of a finite product into a field factors through a unique projection.
* `natCard_algHom_eq_finrank_of_etale` — the fibre count of a finite étale algebra:
  `Nat.card (A →ₐ[K] Ω) = Module.finrank K A`.
-/

open scoped BigOperators

namespace Rigidity.RET.Etale

section PiFactor

variable {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {L : ι → Type*} [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

omit [Fintype ι] [DecidableEq ι] in
private theorem evalAlgHom_apply (i : ι) (x : Π j, L j) :
    Pi.evalAlgHom K L i x = x i := rfl

/-- The orthogonal idempotents of a finite product of rings: `e i = (0, …, 1, …, 0)`. -/
private def idem (i : ι) : (Π j, L j) := Pi.single i 1

omit [Fintype ι] in
private theorem idem_mul_self (i : ι) : (idem i : Π j, L j) * idem i = idem i := by
  ext k
  rcases eq_or_ne k i with hk | hk
  · subst hk; simp [idem]
  · simp [idem, Pi.single_eq_of_ne hk]

private theorem sum_idem : (∑ i, (idem i : Π j, L j)) = 1 := by
  have := Finset.univ_sum_single (1 : Π j, L j)
  simpa [idem, Pi.one_apply] using this

omit [Fintype ι] in
/-- An `f`-image of an orthogonal idempotent is an idempotent of the field `Ω`, hence `0` or `1`. -/
private theorem f_idem_eq (f : (Π j, L j) →ₐ[K] Ω) (i : ι) :
    f (idem i) = 0 ∨ f (idem i) = 1 := by
  have hsq : f (idem i) * f (idem i) = f (idem i) := by
    rw [← map_mul, idem_mul_self]
  have hz : f (idem i) * (f (idem i) - 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

/-- The sum of the `f`-images of the orthogonal idempotents is `1`. -/
private theorem sum_f_idem (f : (Π j, L j) →ₐ[K] Ω) :
    (∑ i, f (idem i)) = 1 := by
  rw [← map_sum, sum_idem, map_one]

/-- Some idempotent has image `1`: not all images can vanish (they sum to `1`). -/
private theorem exists_f_idem_one (f : (Π j, L j) →ₐ[K] Ω) :
    ∃ i, f (idem i) = 1 := by
  by_contra h
  push_neg at h
  have hz : ∀ i, f (idem i) = 0 := by
    intro i
    rcases f_idem_eq f i with h0 | h1
    · exact h0
    · exact absurd h1 (h i)
  have hsum : (∑ i, f (idem i)) = 0 := by simp [hz]
  rw [sum_f_idem] at hsum
  exact one_ne_zero hsum

omit [Fintype ι] in
/-- Multiplying by an idempotent picks out one coordinate: `x * e i = single i (x i)`. -/
private theorem mul_idem (x : Π j, L j) (i : ι) :
    x * idem i = Pi.single i (x i) := by
  ext k
  rcases eq_or_ne k i with hk | hk
  · subst hk; simp [idem]
  · simp [idem, Pi.single_eq_of_ne hk]

omit [Fintype ι] in
/-- The key factoring identity: `f x = f (single j (x j))` at a distinguished index `j`. -/
private theorem f_eq_single (f : (Π j, L j) →ₐ[K] Ω) {j : ι} (hj : f (idem j) = 1)
    (x : Π k, L k) : f x = f (Pi.single j (x j)) := by
  have hmul : f x * f (idem j) = f (Pi.single j (x j)) := by
    rw [← map_mul, mul_idem]
  rw [hj, mul_one] at hmul
  exact hmul

/-- The `K`-algebra map `L j →ₐ[K] Ω` obtained by restricting `f` along the `j`-th inclusion
`y ↦ single j y`.  It is unital precisely because `f (single j 1) = f (idem j) = 1`. -/
private def restrict (f : (Π j, L j) →ₐ[K] Ω) {j : ι} (hj : f (idem j) = 1) :
    L j →ₐ[K] Ω where
  toFun y := f (Pi.single j y)
  map_one' := by simpa only [idem] using hj
  map_mul' y y' := by
    show f (Pi.single j (y * y')) = f (Pi.single j y) * f (Pi.single j y')
    rw [← map_mul]
    congr 1
    ext k
    rcases eq_or_ne k j with hk | hk
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  map_zero' := by simp
  map_add' y y' := by
    show f (Pi.single j (y + y')) = f (Pi.single j y) + f (Pi.single j y')
    rw [← map_add, ← Pi.single_add]
  commutes' r := by
    show f (Pi.single j (algebraMap K (L j) r)) = algebraMap K Ω r
    have hx := f_eq_single f hj (algebraMap K (Π i, L i) r)
    rw [f.commutes] at hx
    rw [show (algebraMap K (Π i, L i) r) j = algebraMap K (L j) r from rfl] at hx
    exact hx.symm

/-- Reassembling: `⟨i, g⟩ ↦ g ∘ (projection to `L i`)`. -/
def reassemble (p : Σ i, (L i →ₐ[K] Ω)) : (Π i, L i) →ₐ[K] Ω :=
  p.2.comp (Pi.evalAlgHom K L p.1)

omit [Fintype ι] in
/-- Restricting `f` at a distinguished index and reassembling recovers `f`. -/
private theorem reassemble_restrict (f : (Π j, L j) →ₐ[K] Ω) {j : ι} (hj : f (idem j) = 1) :
    reassemble (⟨j, restrict f hj⟩ : Σ i, (L i →ₐ[K] Ω)) = f := by
  ext x
  show f (Pi.single j (x j)) = f x
  exact (f_eq_single f hj x).symm

/-- **Algebra maps out of a finite product into a field factor through a unique projection.**

Reassembly `⟨i, g⟩ ↦ g ∘ (projection to `L i`)` is a bijection from `Σ i, (L i →ₐ[K] Ω)` onto
`(Π i, L i) →ₐ[K] Ω`.  Injectivity: the idempotents `single i 1` pin down the index, then
surjectivity of the projection pins down the map; surjectivity: select the unique coordinate `j`
with `f (single j 1) = 1` and restrict `f` there. -/
private theorem reassemble_bijective :
    Function.Bijective (reassemble (K := K) (L := L) (Ω := Ω)) := by
  constructor
  · rintro ⟨i, g⟩ ⟨i', g'⟩ h
    have hidx : i = i' := by
      by_contra hne
      have h1 := congrArg (fun φ => φ (idem i)) h
      simp only [reassemble, AlgHom.comp_apply, evalAlgHom_apply, idem, Pi.single_eq_same,
        map_one, Pi.single_eq_of_ne (Ne.symm hne), map_zero] at h1
      exact one_ne_zero h1
    subst hidx
    have hg : g = g' := by
      ext y
      have h2 := congrArg (fun φ => φ (Pi.single i y)) h
      simpa only [reassemble, AlgHom.comp_apply, evalAlgHom_apply, Pi.single_eq_same] using h2
    rw [hg]
  · intro f
    exact ⟨⟨(exists_f_idem_one f).choose, restrict f (exists_f_idem_one f).choose_spec⟩,
           reassemble_restrict f (exists_f_idem_one f).choose_spec⟩

/-- The fibre of a finite product is the disjoint union of the factors' fibres. -/
theorem natCard_algHom_pi [∀ i, Finite ((L i) →ₐ[K] Ω)] :
    Nat.card ((Π i, L i) →ₐ[K] Ω) = ∑ i, Nat.card ((L i) →ₐ[K] Ω) := by
  rw [← Nat.card_sigma]
  exact (Nat.card_eq_of_bijective _ reassemble_bijective).symm

end PiFactor

section Etale

variable {K : Type*} [Field K]
variable {A : Type*} [CommRing A] [Algebra K A]
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]

omit [IsAlgClosed Ω] in
/-- **The fibre of a finite étale algebra is finite.**  For a finite étale `K`-algebra `A` and a
field `Ω ⊇ K`, there are only finitely many `K`-embeddings `A →ₐ[K] Ω`.  This is the finiteness
underlying "a finite étale cover has finitely many sheets", and is what lets the fibre functor land
in `FintypeCat`. -/
theorem finite_algHom_of_etale [Algebra.Etale K A] : Finite (A →ₐ[K] Ω) := by
  obtain ⟨I, _, L, _, _, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  classical
  haveI : Fintype I := Fintype.ofFinite I
  haveI : ∀ i, Module.Finite K (L i) := fun i => (hL i).1
  haveI : ∀ i, Algebra.IsSeparable K (L i) := fun i => (hL i).2
  haveI : ∀ i, Finite ((L i) →ₐ[K] Ω) := fun i => inferInstance
  haveI : Finite ((Π i, L i) →ₐ[K] Ω) := Finite.of_surjective _ reassemble_bijective.surjective
  exact Finite.of_equiv _
    (show ((Π i, L i) →ₐ[K] Ω) ≃ (A →ₐ[K] Ω) from
      { toFun := fun f => f.comp e.toAlgHom
        invFun := fun f => f.comp e.symm.toAlgHom
        left_inv := fun f => by ext a; simp
        right_inv := fun f => by ext a; simp })

/-- **The fibre count of a finite étale algebra equals its dimension.**

`Nat.card (A →ₐ[K] Ω) = [A : K]` for a finite étale `K`-algebra `A` and an algebraically closed
`Ω ⊇ K`.  This is the algebraic incarnation of "the number of sheets of a cover equals its degree".
It follows from the structure theorem `A ≃ₐ Π i, L i` (finite product of finite separable field
extensions), the product-factoring `natCard_algHom_pi`, and the classical embedding count
`AlgHom.card` for each separable factor. -/
theorem natCard_algHom_eq_finrank_of_etale [Algebra.Etale K A] :
    Nat.card (A →ₐ[K] Ω) = Module.finrank K A := by
  obtain ⟨I, _, L, _, _, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  classical
  haveI : Fintype I := Fintype.ofFinite I
  haveI hFD : ∀ i, FiniteDimensional K (L i) := fun i => (hL i).1
  haveI : ∀ i, Module.Finite K (L i) := fun i => (hL i).1
  haveI : ∀ i, Algebra.IsSeparable K (L i) := fun i => (hL i).2
  haveI : ∀ i, Finite ((L i) →ₐ[K] Ω) := fun i => inferInstance
  -- transport the fibre and the dimension across `e : A ≃ₐ Π i, L i`
  have hcard : Nat.card (A →ₐ[K] Ω) = Nat.card ((Π i, L i) →ₐ[K] Ω) :=
    Nat.card_congr
      { toFun := fun f => f.comp e.symm.toAlgHom
        invFun := fun f => f.comp e.toAlgHom
        left_inv := fun f => by ext a; simp
        right_inv := fun f => by ext a; simp }
  have hrank : Module.finrank K A = Module.finrank K (Π i, L i) :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  rw [hcard, hrank, natCard_algHom_pi, Module.finrank_pi_fintype K]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Nat.card_eq_fintype_card, AlgHom.card]

end Etale

section GaloisAction

variable {K : Type*} [Field K]
variable {A : Type*} [CommRing A] [Algebra K A]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- The Galois group `Ω ≃ₐ[K] Ω` acts on the fibre `A →ₐ[K] Ω` by post-composition
`σ • f = σ ∘ f`.  This is the action whose orbits are the connected components of the cover, and
whose transitivity on `A →ₐ[K] Ω` (for `A` a finite separable field extension) expresses that `A` is
a *connected* object of the Galois category — the algebraic shadow of the monodromy action of the
fundamental group on a fibre. -/
instance fibreMulAction : MulAction (Ω ≃ₐ[K] Ω) (A →ₐ[K] Ω) where
  smul σ f := σ.toAlgHom.comp f
  one_smul f := by ext a; exact AlgEquiv.one_apply (R := K) (f a)
  mul_smul σ τ f := by ext a; exact AlgEquiv.mul_apply σ τ (f a)

@[simp]
theorem fibre_smul_apply (σ : Ω ≃ₐ[K] Ω) (f : A →ₐ[K] Ω) (a : A) :
    (σ • f) a = σ (f a) := rfl

end GaloisAction

section Transitivity

variable {K : Type*} [Field K]
variable {E : Type*} [Field E] [Algebra K E]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Normal K Ω]

/-- **The monodromy action on the fibre of a field is transitive.**  For a field extension `E / K`
and a normal extension `Ω / K` (e.g. an algebraic closure), the group `Ω ≃ₐ[K] Ω` acts transitively
on the fibre `E →ₐ[K] Ω`: any two `K`-embeddings of `E` into `Ω` differ by an automorphism of `Ω`.
This is the algebraic form of the statement that a *field* is a **connected** object of the Galois
category of finite étale `K`-algebras — its fibre is a single orbit under the fundamental group. -/
theorem fibre_isPretransitive : MulAction.IsPretransitive (Ω ≃ₐ[K] Ω) (E →ₐ[K] Ω) := by
  refine ⟨fun f g => ?_⟩
  -- The range of an embedding of a field is a field.
  letI : Field f.range := inferInstanceAs <| Field (AlgHom.fieldRange f)
  letI : Field g.range := inferInstanceAs <| Field (AlgHom.fieldRange g)
  -- Corestrict each embedding to an isomorphism onto its (field) image.
  let ef : E ≃ₐ[K] f.range := AlgEquiv.ofInjectiveField f
  let eg : E ≃ₐ[K] g.range := AlgEquiv.ofInjectiveField g
  -- The induced isomorphism between the two subfields, then lift it to an automorphism of `Ω`.
  let χ : f.range ≃ₐ[K] g.range := ef.symm.trans eg
  refine ⟨χ.liftNormal Ω, ?_⟩
  ext x
  show χ.liftNormal Ω (f x) = g x
  have hf : algebraMap f.range Ω (ef x) = f x :=
    AlgEquiv.ofInjective_apply f f.toRingHom.injective x
  have hg : algebraMap g.range Ω (eg x) = g x :=
    AlgEquiv.ofInjective_apply g g.toRingHom.injective x
  have hχ : χ (ef x) = eg x := by
    simp only [χ, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  have key := χ.liftNormal_commutes Ω (ef x)
  rw [hf, hχ, hg] at key
  exact key

end Transitivity

section Connected

variable {K : Type*} [Field K]
variable {E : Type*} [Field E] [Algebra K E]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- **The fibre of a field is nonempty.**  Any algebraic field extension `E / K` admits a
`K`-embedding into an algebraically closed extension `Ω`.  Together with `fibre_isPretransitive`
this says the fibre of a field is a *single, nonempty* orbit — the precise sense in which a field is
a connected object of the Galois category of finite étale `K`-algebras. -/
theorem fibre_nonempty [Algebra.IsAlgebraic K E] [IsAlgClosed Ω] :
    Nonempty (E →ₐ[K] Ω) :=
  ⟨IsAlgClosed.lift⟩

/-- **The fibre of a normal object is a torsor under its automorphism group.**  For a normal
algebraic extension `E / K` and an algebraically closed `Ω ⊇ K`, the fibre `E →ₐ[K] Ω` is in
bijection with the Galois group `Gal(E/K) = E ≃ₐ[K] E`; in particular it has exactly `|Aut_K E|`
points.  Fixing a base embedding `E ↪ Ω` trivialises the torsor — any other embedding differs from
it by a unique `K`-automorphism of `E`.  This is the object-level heart of the identification of the
fundamental group `Aut F` with the Galois group. -/
theorem natCard_fibre_eq_card_aut_of_normal [Normal K E] [Algebra.IsAlgebraic K E]
    [IsAlgClosed Ω] : Nat.card (E →ₐ[K] Ω) = Nat.card (E ≃ₐ[K] E) := by
  obtain ⟨f₀⟩ : Nonempty (E →ₐ[K] Ω) := fibre_nonempty
  letI : Algebra E Ω := f₀.toRingHom.toAlgebra
  haveI : IsScalarTower K E Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => (f₀.commutes x).symm)
  exact Nat.card_congr (Normal.algHomEquivAut (F := K) (K₁ := Ω) (E := E))

end Connected

section OrbitDecomposition

variable {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {L : ι → Type*} [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

omit [Fintype ι] [DecidableEq ι] in
/-- **The product-fibre bijection is Galois-equivariant.**  The bijection
`Σ i, (L i →ₐ[K] Ω) ≃ ((Π i, L i) →ₐ[K] Ω)` of `reassemble` intertwines the `Ω ≃ₐ[K] Ω`-action
(which acts on the second component of the sigma, fixing the index) with the post-composition action
on the fibre of the product.  Consequently the fundamental-group orbits on the fibre of `Π i, L i`
are exactly the fibres of the individual factors: the connected components of the cover are the field
factors of the finite étale algebra. -/
theorem reassemble_smul (σ : Ω ≃ₐ[K] Ω) (p : Σ i, (L i →ₐ[K] Ω)) :
    σ • reassemble p = reassemble (⟨p.1, σ • p.2⟩ : Σ i, (L i →ₐ[K] Ω)) := by
  ext x
  rfl

end OrbitDecomposition

section ReflectConnected

variable {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- **The fibre functor reflects connectedness.**  If the fibre of a finite product of algebraic
field extensions is a *single* orbit under `Ω ≃ₐ[K] Ω` (with `Ω` algebraically closed), then there
is at most one factor.  Combined with `reassemble_smul`, whose orbits are indexed by the factors, a
transitive fibre forces the finite étale algebra to be connected — the converse of
`fibre_isPretransitive`. -/
theorem subsingleton_of_isPretransitive [∀ i, Algebra.IsAlgebraic K (L i)] [IsAlgClosed Ω]
    (h : MulAction.IsPretransitive (Ω ≃ₐ[K] Ω) ((Π i, L i) →ₐ[K] Ω)) :
    Subsingleton ι := by
  refine ⟨fun i j => ?_⟩
  obtain ⟨fi⟩ : Nonempty (L i →ₐ[K] Ω) := fibre_nonempty
  obtain ⟨fj⟩ : Nonempty (L j →ₐ[K] Ω) := fibre_nonempty
  obtain ⟨σ, hσ⟩ := h.exists_smul_eq
    (reassemble (⟨i, fi⟩ : Σ i, (L i →ₐ[K] Ω)))
    (reassemble (⟨j, fj⟩ : Σ i, (L i →ₐ[K] Ω)))
  rw [reassemble_smul] at hσ
  exact congrArg Sigma.fst (reassemble_bijective.injective hσ)

end ReflectConnected

section EtaleConnected

variable {K : Type*} [Field K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- **Precomposition by a `K`-algebra map is Galois-equivariant on fibres.**  A map `ψ : A →ₐ[K] B`
induces `(B →ₐ[K] Ω) → (A →ₐ[K] Ω)`, `f ↦ f ∘ ψ`, which commutes with the post-composition action of
`Ω ≃ₐ[K] Ω` — the fibre functor is a functor of `Gal(Ω/K)`-sets. -/
def precompActionHom {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (ψ : A →ₐ[K] B) :
    (B →ₐ[K] Ω) →ₑ[(id : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω))] (A →ₐ[K] Ω) where
  toFun f := f.comp ψ
  map_smul' _ _ := by ext _; rfl

/-- **A finite étale algebra with a transitive fibre is connected.**  If `A ≃ₐ[K] Π i, L i` is the
decomposition of a finite étale algebra into field factors and the fibre `A →ₐ[K] Ω` is a single
orbit under `Ω ≃ₐ[K] Ω` (with `Ω` algebraically closed), then the index set is a subsingleton: `A`
has (up to isomorphism) a single field factor.  This is the reflect-connectedness statement at the
level of the étale algebra itself. -/
theorem subsingleton_of_algEquiv_pi_of_isPretransitive
    {A : Type*} [CommRing A] [Algebra K A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    [∀ i, Algebra.IsAlgebraic K (L i)] [IsAlgClosed Ω]
    (e : A ≃ₐ[K] (Π i, L i))
    (h : MulAction.IsPretransitive (Ω ≃ₐ[K] Ω) (A →ₐ[K] Ω)) :
    Subsingleton ι := by
  have hsurj : Function.Surjective ⇑(precompActionHom (Ω := Ω) e.symm.toAlgHom) :=
    fun g => ⟨g.comp e.toAlgHom, by ext a; exact congrArg g (e.apply_symm_apply a)⟩
  have hB : MulAction.IsPretransitive (Ω ≃ₐ[K] Ω) ((Π i, L i) →ₐ[K] Ω) :=
    MulAction.IsPretransitive.of_surjective_map hsurj h
  exact subsingleton_of_isPretransitive hB

end EtaleConnected

section Faithful

variable {K : Type*} [Field K]
variable {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]

/-- **The fibre functor separates points of a finite étale algebra.**  For a finite étale
`K`-algebra `A` and an algebraically closed `Ω ⊇ K`, every nonzero `a : A` is detected by some
`K`-embedding `f : A →ₐ[K] Ω` (`f a ≠ 0`).  Structurally: decompose `A ≃ₐ Π i, L i` into field
factors, pick a coordinate on which `a` is nonzero, and post-compose the projection with a
`K`-embedding of that factor into `Ω`.  This joint injectivity of the fibre is what makes the fibre
functor faithful. -/
theorem separating_of_etale [Algebra.Etale K A] {a : A} (ha : a ≠ 0) :
    ∃ f : A →ₐ[K] Ω, f a ≠ 0 := by
  obtain ⟨I, _, L, _, _, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  haveI : ∀ i, Module.Finite K (L i) := fun i => (hL i).1
  haveI : ∀ i, Algebra.IsAlgebraic K (L i) := fun i => Algebra.IsAlgebraic.of_finite K (L i)
  -- `e a ≠ 0`, so some coordinate of `e a` is nonzero.
  have hea : e a ≠ 0 := by
    rw [← map_zero e]; exact fun hh => ha (e.injective hh)
  obtain ⟨i, hi⟩ : ∃ i, (e a) i ≠ 0 := by
    by_contra h; push_neg at h; exact hea (funext h)
  -- Embed the `i`-th field factor into the algebraically closed `Ω`.
  let φ : L i →ₐ[K] Ω := IsAlgClosed.lift
  refine ⟨φ.comp ((Pi.evalAlgHom K L i).comp e.toAlgHom), ?_⟩
  show φ ((e a) i) ≠ 0
  exact (map_ne_zero_iff φ φ.toRingHom.injective).mpr hi

/-- **The fibre functor is faithful.**  Two `K`-algebra maps `ψ₁, ψ₂ : A →ₐ[K] B` into a finite
étale algebra `B` that induce the same map on fibres — i.e. `f ∘ ψ₁ = f ∘ ψ₂` for every embedding
`f : B →ₐ[K] Ω` into an algebraically closed `Ω` — are equal.  This is faithfulness of the fibre
functor `A ↦ (A →ₐ[K] Ω)`: morphisms of finite étale algebras are determined by their effect on
fibres, one of the defining properties of a fibre functor on a Galois category. -/
theorem faithful_of_etale [Algebra.Etale K B] {ψ₁ ψ₂ : A →ₐ[K] B}
    (h : ∀ f : B →ₐ[K] Ω, f.comp ψ₁ = f.comp ψ₂) : ψ₁ = ψ₂ := by
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, ψ₁ a ≠ ψ₂ a := by
    by_contra h'; push_neg at h'; exact hne (AlgHom.ext h')
  obtain ⟨f, hf⟩ := separating_of_etale (K := K) (Ω := Ω) (sub_ne_zero.mpr ha)
  have e1 : f (ψ₁ a) = f (ψ₂ a) := congrArg (fun g => g a) (h f)
  exact hf (by rw [map_sub, e1, sub_self])

end Faithful

end Rigidity.RET.Etale
