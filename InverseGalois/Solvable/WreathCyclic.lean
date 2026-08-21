/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Solvable.Nilpotent
import InverseGalois.Solvable.Semiabelian
import InverseGalois.Solvable.WreathFunctor

/-!
# Wreath products by finite abelian groups reduce to cyclic ones

A finite abelian group is a finite product of finite cyclic groups, and wreathing by a product can
be replaced by wreathing twice: `(A₁ × A₂) ≀ᵣ H` is a quotient of `A₁ ≀ᵣ (A₂ ≀ᵣ H)`.  Iterating
over the cyclic factors expresses `A ≀ᵣ H` as a quotient of a tower of wreath products whose
bottom groups are all cyclic.  Consequently a realization theorem for wreath products never has to
treat any bottom group other than a cyclic one: from

`H` realizable and `C` finite cyclic ⟹ `C ≀ᵣ H` realizable

one gets the same statement with `C` replaced by an arbitrary finite abelian group, and therefore —
combining with the presentation of a semidirect product as a quotient of a wreath product — a
realization of every semiabelian group.

The induction uses only that the realization predicate is invariant under isomorphism and closed
under quotients, so it is carried out once for an abstract predicate and instantiated for
`IsInverseGalois` over `ℚ` and for `IsRegularInverseGalois` over `ℚ(T)`.

## Main results

* `RegularWreathProduct.mulEquivRightOfSubsingleton` — wreathing by the trivial group does nothing.
* `WreathReduction.wreath_commGroup` — the abstract reduction from finite abelian to cyclic bottom
  groups.
* `IsInverseGalois.wreath_of_isCyclic` and `IsRegularInverseGalois.wreath_of_isCyclic` — the two
  instances of that reduction.
* `IsSemiabelian.isInverseGalois_of_isCyclic` and
  `IsSemiabelian.isRegularInverseGalois_of_isCyclic` — every semiabelian group is realizable as
  soon as the wreath products with a finite cyclic bottom group are.
-/

namespace RegularWreathProduct

/-- **Wreathing by the trivial group changes nothing**: the coordinate function carries no
information, so the projection to the index group is an isomorphism. -/
def mulEquivRightOfSubsingleton (D Q : Type*) [Group D] [Subsingleton D] [Group Q] :
    D ≀ᵣ Q ≃* Q where
  toFun := rightHom
  invFun := inl
  left_inv _ := RegularWreathProduct.ext (funext fun _ ↦ Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  map_mul' := map_mul rightHom

end RegularWreathProduct

namespace WreathReduction

/-! ## The abstract induction

Both realization predicates are invariant under group isomorphism and closed under quotients.
That is all the induction below uses, so it is carried out once for an abstract predicate `IG`. -/

variable {IG : ∀ (G : Type) [Group G], Prop}

/-- **Wreathing by a product of finitely many cyclic groups**, indexed by `Fin n`.  Peeling the
first factor off turns `(∏ᵢ Aᵢ) ≀ᵣ H` into a quotient of `A₀ ≀ᵣ ((∏ᵢ₊₁ Aᵢ) ≀ᵣ H)`, and the inner
wreath product is handled by the induction hypothesis. -/
theorem wreath_fin
    (hequiv : ∀ {G H : Type} [Group G] [Group H], IG G → (G ≃* H) → IG H)
    (hsurj : ∀ {G H : Type} [Group G] [Group H], IG G → ∀ f : G →* H, Function.Surjective f → IG H)
    (hcyc : ∀ (C H : Type) [CommGroup C] [Finite C] [IsCyclic C] [Group H] [Finite H],
      IG H → IG (C ≀ᵣ H))
    (n : ℕ) :
    ∀ (A : Fin n → Type) [∀ i, CommGroup (A i)] [∀ i, Finite (A i)] [∀ i, IsCyclic (A i)]
      (H : Type) [Group H] [Finite H], IG H → IG ((∀ i, A i) ≀ᵣ H) := by
  induction n with
  | zero =>
    intro A _ _ _ H _ _ hH
    haveI : Subsingleton (∀ i : Fin 0, A i) := ⟨fun _ _ ↦ funext fun i ↦ i.elim0⟩
    exact hequiv hH (RegularWreathProduct.mulEquivRightOfSubsingleton _ H).symm
  | succ n ih =>
    intro A _ _ _ H _ _ hH
    have hrest : IG ((∀ i : Fin n, A i.succ) ≀ᵣ H) := ih (fun i ↦ A i.succ) H hH
    letI : Fintype ((∀ i : Fin n, A i.succ) ≀ᵣ H) := Fintype.ofFinite _
    have htower : IG (A 0 ≀ᵣ ((∀ i : Fin n, A i.succ) ≀ᵣ H)) := hcyc _ _ hrest
    have hpair : IG ((A 0 × ∀ i : Fin n, A i.succ) ≀ᵣ H) :=
      hsurj htower RegularWreathProduct.regroup RegularWreathProduct.regroup_surjective
    exact hequiv hpair
      (RegularWreathProduct.congr (SylowReduction.mulEquivPiFinSucc A).symm (MulEquiv.refl H))

/-- **A wreath product by a finite abelian group is reached from the cyclic ones.**  Splitting the
bottom group into cyclic factors by the structure theorem and reindexing them by `Fin n`, this is
`wreath_fin`. -/
theorem wreath_commGroup
    (hequiv : ∀ {G H : Type} [Group G] [Group H], IG G → (G ≃* H) → IG H)
    (hsurj : ∀ {G H : Type} [Group G] [Group H], IG G → ∀ f : G →* H, Function.Surjective f → IG H)
    (hcyc : ∀ (C H : Type) [CommGroup C] [Finite C] [IsCyclic C] [Group H] [Finite H],
      IG H → IG (C ≀ᵣ H))
    (A H : Type) [CommGroup A] [Finite A] [Group H] [Finite H] (hH : IG H) : IG (A ≀ᵣ H) := by
  obtain ⟨ι, hι, m, hm, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  letI := hι
  set eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with heι
  haveI : ∀ k : Fin (Fintype.card ι), NeZero (m (eι.symm k)) := fun k ↦
    ⟨by have := hm (eι.symm k); omega⟩
  have key : IG ((∀ k : Fin (Fintype.card ι), Multiplicative (ZMod (m (eι.symm k)))) ≀ᵣ H) :=
    wreath_fin hequiv hsurj hcyc _ _ H hH
  refine hequiv key (RegularWreathProduct.congr ?_ (MulEquiv.refl H))
  exact (e.trans (SylowReduction.mulEquivPiCongrLeft'
    (fun i ↦ Multiplicative (ZMod (m i))) eι)).symm

end WreathReduction

/-! ## The two instances, and the semiabelian consequence -/

/-- **A cyclic bottom group suffices, over `ℚ`.**  If every wreath product of a realizable finite
group by a finite cyclic group is realizable, then so is every wreath product by a finite abelian
group. -/
theorem IsInverseGalois.wreath_of_isCyclic
    (hcyc : ∀ (C H : Type) [CommGroup C] [Finite C] [IsCyclic C] [Group H] [Finite H],
      IsInverseGalois H → IsInverseGalois (C ≀ᵣ H))
    (A H : Type) [CommGroup A] [Finite A] [Group H] [Finite H] (hH : IsInverseGalois H) :
    IsInverseGalois (A ≀ᵣ H) :=
  WreathReduction.wreath_commGroup (IG := fun G _ ↦ IsInverseGalois G)
    (fun h e ↦ h.of_mulEquiv e) (fun h f hf ↦ h.of_surjective f hf) hcyc A H hH

/-- **A cyclic bottom group suffices, over `ℚ(T)`.**  The regular counterpart of
`IsInverseGalois.wreath_of_isCyclic`. -/
theorem IsRegularInverseGalois.wreath_of_isCyclic
    (hcyc : ∀ (C H : Type) [CommGroup C] [Finite C] [IsCyclic C] [Group H] [Finite H],
      IsRegularInverseGalois H → IsRegularInverseGalois (C ≀ᵣ H))
    (A H : Type) [CommGroup A] [Finite A] [Group H] [Finite H]
    (hH : IsRegularInverseGalois H) : IsRegularInverseGalois (A ≀ᵣ H) :=
  WreathReduction.wreath_commGroup (IG := fun G _ ↦ IsRegularInverseGalois G)
    (fun h e ↦ h.of_mulEquiv e) (fun h f hf ↦ h.of_surjective f hf) hcyc A H hH

/-- **Every semiabelian group is an inverse Galois group over `ℚ`**, given only that a wreath
product by a finite *cyclic* group preserves realizability. -/
theorem IsSemiabelian.isInverseGalois_of_isCyclic
    (hcyc : ∀ (C H : Type) [CommGroup C] [Finite C] [IsCyclic C] [Group H] [Finite H],
      IsInverseGalois H → IsInverseGalois (C ≀ᵣ H))
    {G : Type} [Group G] [Finite G] (hG : IsSemiabelian G) : IsInverseGalois G :=
  hG.isInverseGalois fun A H _ _ _ _ hH ↦ IsInverseGalois.wreath_of_isCyclic hcyc A H hH

/-- **Every semiabelian group is a regular inverse Galois group over `ℚ(T)`**, given only that a
wreath product by a finite *cyclic* group preserves regular realizability. -/
theorem IsSemiabelian.isRegularInverseGalois_of_isCyclic
    (hcyc : ∀ (C H : Type) [CommGroup C] [Finite C] [IsCyclic C] [Group H] [Finite H],
      IsRegularInverseGalois H → IsRegularInverseGalois (C ≀ᵣ H))
    {G : Type} [Group G] [Finite G] (hG : IsSemiabelian G) : IsRegularInverseGalois G :=
  hG.isRegularInverseGalois fun A H _ _ _ _ hH ↦
    IsRegularInverseGalois.wreath_of_isCyclic hcyc A H hH
