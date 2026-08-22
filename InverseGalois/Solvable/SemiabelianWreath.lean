/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.SemiabelianHall

/-!
# Wreath products of semiabelian groups

Dentzer's class of semiabelian groups is closed under the **regular wreath product**: if `D` and `Q`
are semiabelian, so is `D ≀ᵣ Q`.  The proof is an induction along the derivation of semiabelianness
of the base group `D`, the quotient group `Q` staying fixed.

* If `D` is trivial then the base functions `Q → D` carry no information and the projection
  `RegularWreathProduct.rightHom` identifies `D ≀ᵣ Q` with `Q`.
* If `D = A ⋊[φ] K` is a semidirect product of a semiabelian group `K` by a finite abelian group
  `A`, then inside `(A ⋊[φ] K) ≀ᵣ Q` the functions `Q → A`, viewed as wreath elements with trivial
  `Q`-component, form a normal abelian subgroup: it is the kernel of the map induced on base
  functions by `SemidirectProduct.rightHom`.  The map induced by `SemidirectProduct.inr` embeds
  `K ≀ᵣ Q`, semiabelian by induction, as a supplement of that kernel, because an element of
  `(A ⋊[φ] K) ≀ᵣ Q` is the product of its `A`-part and its `K`-part.
* A surjection `D₀ ↠ D` induces a surjection `D₀ ≀ᵣ Q ↠ D ≀ᵣ Q` by composing base functions, and
  semiabelianness passes to homomorphic images.

The construction inducing a homomorphism `D₁ ≀ᵣ Q →* D₂ ≀ᵣ Q` from one of the base groups is
recorded separately, since Mathlib's `RegularWreathProduct.congr` transports isomorphisms only.

Iterating the theorem shows that every iterated wreath product of a semiabelian group is
semiabelian.  Since a Sylow `p`-subgroup of a symmetric group on `p ^ n` letters is an iterated
wreath product of `n` copies of the cyclic group of order `p`, all such Sylow subgroups are
semiabelian, and hence — by the general theory — solvable and reachable by the wreath-product
approach to the inverse Galois problem.

## Main results

* `IsSemiabelian.regularWreathProduct` — **the regular wreath product of two semiabelian groups is
  semiabelian.**
* `IsSemiabelian.iteratedWreathProduct` — every iterated wreath product of a semiabelian group is
  semiabelian.
* `IsSemiabelian.sylow_perm` — a Sylow `p`-subgroup of the symmetric group on a set of size `p ^ n`
  is semiabelian.
* `SemiabelianWreath.mapLeft` — the homomorphism of wreath products induced by a homomorphism of
  base groups, together with its injectivity and surjectivity criteria.
-/

namespace SemiabelianWreath

variable {D₁ D₂ Q : Type*} [Group D₁] [Group D₂] [Group Q]

/-- The homomorphism `D₁ ≀ᵣ Q →* D₂ ≀ᵣ Q` induced by a homomorphism `f : D₁ →* D₂` of base groups:
it composes the base function with `f` and leaves the `Q`-component alone.  Multiplicativity holds
because the wreath multiplication multiplies base functions pointwise after translating the
argument, and translation commutes with composing by `f`. -/
def mapLeft (f : D₁ →* D₂) : D₁ ≀ᵣ Q →* D₂ ≀ᵣ Q where
  toFun w := ⟨fun q => f (w.left q), w.right⟩
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp

/-- The base function of `mapLeft f w` is the base function of `w` composed with `f`. -/
@[simp]
theorem mapLeft_left (f : D₁ →* D₂) (w : D₁ ≀ᵣ Q) (q : Q) :
    (mapLeft f w).left q = f (w.left q) := rfl

/-- The `Q`-component is unchanged by `mapLeft`. -/
@[simp]
theorem mapLeft_right (f : D₁ →* D₂) (w : D₁ ≀ᵣ Q) : (mapLeft f w).right = w.right := rfl

/-- An injective homomorphism of base groups induces an injective homomorphism of wreath products,
since base functions are compared pointwise. -/
theorem mapLeft_injective {f : D₁ →* D₂} (hf : Function.Injective f) :
    Function.Injective (mapLeft f : D₁ ≀ᵣ Q →* D₂ ≀ᵣ Q) := by
  intro a b h
  have hl : ∀ q, f (a.left q) = f (b.left q) := fun q =>
    congrFun (congrArg RegularWreathProduct.left h) q
  have hr : (mapLeft f a).right = (mapLeft f b).right := congrArg _ h
  exact RegularWreathProduct.ext (funext fun q => hf (hl q)) hr

/-- A surjective homomorphism of base groups induces a surjective homomorphism of wreath products:
a base function is lifted pointwise by a choice of preimages. -/
theorem mapLeft_surjective {f : D₁ →* D₂} (hf : Function.Surjective f) :
    Function.Surjective (mapLeft f : D₁ ≀ᵣ Q →* D₂ ≀ᵣ Q) := by
  intro w
  refine ⟨⟨fun q => Function.surjInv hf (w.left q), w.right⟩, ?_⟩
  exact RegularWreathProduct.ext (funext fun q => Function.surjInv_eq hf _) rfl

/-- A wreath product with trivial base group is its own quotient: the only base function is the
constant one, so the projection `RegularWreathProduct.rightHom` is bijective. -/
noncomputable def wreathEquivOfSubsingleton (D Q : Type*) [Group D] [Subsingleton D] [Group Q] :
    D ≀ᵣ Q ≃* Q :=
  MulEquiv.ofBijective RegularWreathProduct.rightHom
    ⟨fun a b h => by
        refine RegularWreathProduct.ext (funext fun q => Subsingleton.elim _ _) ?_
        exact h,
      fun q => ⟨RegularWreathProduct.inl q, rfl⟩⟩

variable {A K : Type*} [CommGroup A] [Group K]

/-- The base group of `A`s inside `(A ⋊[φ] K) ≀ᵣ Q`, described as the kernel of the map induced by
the projection `A ⋊[φ] K →* K`: an element lies in it exactly when its `Q`-component is trivial and
each value of its base function lies in the copy of `A`. -/
theorem mem_ker_mapLeft_rightHom_iff (φ : K →* MulAut A) (w : (A ⋊[φ] K) ≀ᵣ Q) :
    w ∈ (mapLeft (SemidirectProduct.rightHom : A ⋊[φ] K →* K) : (A ⋊[φ] K) ≀ᵣ Q →* K ≀ᵣ Q).ker ↔
      w.right = 1 ∧ ∀ q, (w.left q).right = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    exact ⟨congrArg RegularWreathProduct.right h,
      fun q => congrFun (congrArg RegularWreathProduct.left h) q⟩
  · rintro ⟨h1, h2⟩
    exact RegularWreathProduct.ext (funext fun q => h2 q) h1

end SemiabelianWreath

namespace IsSemiabelian

open SemiabelianWreath

/-- **The regular wreath product of two semiabelian groups is semiabelian.**  Induction on the
derivation of semiabelianness of the base group.  A trivial base group leaves the quotient group
itself; a semidirect base group `A ⋊[φ] K` makes `(A ⋊[φ] K) ≀ᵣ Q` generated by the normal abelian
group of base functions with values in `A` together with the embedded copy of `K ≀ᵣ Q`, since every
element factors as its `A`-part times its `K`-part; and a homomorphic image of the base group
induces a homomorphic image of the wreath product. -/
theorem regularWreathProduct {D Q : Type} [Group D] [Finite D] [Group Q] [Finite Q]
    (hD : IsSemiabelian D) (hQ : IsSemiabelian Q) : IsSemiabelian (D ≀ᵣ Q) := by
  induction hD with
  | of_subsingleton D => exact hQ.of_mulEquiv (wreathEquivOfSubsingleton D Q).symm
  | @semidirect A K _ _ _ _ φ _ ih =>
    refine of_normal_abelian_of_sup_eq_top
      (mapLeft (SemidirectProduct.rightHom : A ⋊[φ] K →* K) :
        (A ⋊[φ] K) ≀ᵣ Q →* K ≀ᵣ Q).ker
      (mapLeft (SemidirectProduct.inr : K →* A ⋊[φ] K) :
        K ≀ᵣ Q →* (A ⋊[φ] K) ≀ᵣ Q).range ?_ ?_ ?_
    · rintro ⟨x, hx⟩ ⟨y, hy⟩
      obtain ⟨hx1, hx2⟩ := (mem_ker_mapLeft_rightHom_iff φ x).mp hx
      obtain ⟨hy1, hy2⟩ := (mem_ker_mapLeft_rightHom_iff φ y).mp hy
      refine Subtype.ext (RegularWreathProduct.ext (funext fun q => ?_) ?_)
      · show x.left q * y.left (x.right⁻¹ * q) = y.left q * x.left (y.right⁻¹ * q)
        rw [hx1, hy1]
        refine SemidirectProduct.ext ?_ ?_
        · simp [hx2, hy2, mul_comm]
        · simp [hx2, hy2]
      · show x.right * y.right = y.right * x.right
        rw [hx1, hy1]
    · refine top_le_iff.mp fun w _ => ?_
      have hN : (⟨fun q => SemidirectProduct.inl (w.left q).left, 1⟩ : (A ⋊[φ] K) ≀ᵣ Q) ∈
          (mapLeft (SemidirectProduct.rightHom : A ⋊[φ] K →* K) :
            (A ⋊[φ] K) ≀ᵣ Q →* K ≀ᵣ Q).ker :=
        (mem_ker_mapLeft_rightHom_iff φ _).mpr ⟨rfl, fun _ => rfl⟩
      have hw : w = (⟨fun q => SemidirectProduct.inl (w.left q).left, 1⟩ : (A ⋊[φ] K) ≀ᵣ Q) *
          mapLeft (SemidirectProduct.inr : K →* A ⋊[φ] K)
            (⟨fun q => (w.left q).right, w.right⟩ : K ≀ᵣ Q) := by
        refine RegularWreathProduct.ext (funext fun q => ?_) ?_
        · show w.left q = SemidirectProduct.inl (w.left _).left *
            SemidirectProduct.inr (w.left _).right
          rw [inv_one, one_mul]
          exact (SemidirectProduct.inl_left_mul_inr_right _).symm
        · show w.right = 1 * w.right
          rw [one_mul]
      rw [hw]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hN)
        (Subgroup.mem_sup_right ⟨_, rfl⟩)
    · exact ih.of_mulEquiv (MonoidHom.ofInjective
        (mapLeft_injective (Q := Q) SemidirectProduct.inr_injective))
  | of_surjective f hf _ ih => exact ih.of_surjective (mapLeft f) (mapLeft_surjective hf)

/-- **Every iterated wreath product of a semiabelian group is semiabelian.**  The zeroth iterate is
trivial, and each further iterate is a regular wreath product of the previous one by the group
itself. -/
theorem iteratedWreathProduct {G : Type} [Group G] [Finite G]
    (hG : IsSemiabelian G) (n : ℕ) : IsSemiabelian (IteratedWreathProduct G n) := by
  induction n with
  | zero =>
    haveI : Subsingleton (IteratedWreathProduct G 0) :=
      ⟨fun a b => Subsingleton.elim (α := PUnit) a b⟩
    exact of_subsingleton _
  | succ n ih => exact ih.regularWreathProduct hG

/-- **A Sylow `p`-subgroup of the symmetric group on a set of size `p ^ n` is semiabelian.**  Such a
subgroup is the wreath product of `n` copies of the cyclic group of order `p`, which is abelian and
therefore semiabelian, so the iterated wreath product theorem applies. -/
theorem sylow_perm {p n : ℕ} [Fact p.Prime] {α : Type} [Finite α]
    (hα : Nat.card α = p ^ n) (P : Sylow p (Equiv.Perm α)) :
    IsSemiabelian ↥(P : Subgroup (Equiv.Perm α)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hG : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact ((of_commGroup (Multiplicative (ZMod p))).iteratedWreathProduct n).of_mulEquiv
    (Sylow.mulEquivIteratedWreathProduct p n α hα (Multiplicative (ZMod p)) hG P).symm

end IsSemiabelian
