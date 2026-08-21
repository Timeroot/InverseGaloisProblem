/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.PrimePower
import InverseGalois.Solvable.Shafarevich.Main

/-!
# From abelian kernels to prime power kernels

The centre of a nontrivial finite `p`-group is nontrivial, and it is a characteristic subgroup, so
an action of a group `U` on a finite `p`-group `H` descends to the quotient `H ⧸ Z(H)`, which is
again a finite `p`-group but of strictly smaller order.  The induced map

`H ⋊ U →* (H ⧸ Z(H)) ⋊ U`

is surjective with kernel a copy of `Z(H)`, an abelian group.  Peeling off one central layer at a
time therefore expresses any split embedding problem with kernel of prime power order as a tower of
embedding problems with abelian kernel, which is the point at which class field theory enters
Shafarevich's proof.

## Main results

* `Shafarevich.quotientChar` — an automorphism of a group descends to the quotient by a
  characteristic subgroup.
* `Shafarevich.AbelianKernelEP` — the statement that every embedding problem over `ℚ` with finite
  abelian kernel is solvable.
* `Shafarevich.splitPrimePower_of_abelianKernel` — for an arbitrary quotient-closed realization
  predicate, split embedding problems with kernel of prime power order follow from embedding
  problems with abelian kernel.
* `Shafarevich.splitPrimePowerEP_of_abelianKernelEP` — its specialization to realizability
  over `ℚ`.
* `Shafarevich.isSolvable_isInverseGalois_of_abelianKernelEP` — every finite solvable group is a
  Galois group over `ℚ`, granted `AbelianKernelEP`.
* `Shafarevich.AbelianKernelEPRegular` and
  `Shafarevich.isSolvable_isRegularInverseGalois_of_abelianKernelEPRegular` — the regular analogues
  over `ℚ(T)`.
-/

namespace Shafarevich

open SemidirectProduct

/-! ## The induced action on a quotient by a characteristic subgroup -/

/-- **An automorphism of a group descends to the quotient by a characteristic subgroup.**

A characteristic subgroup is preserved by every automorphism, so every automorphism induces an
automorphism of the quotient, functorially. -/
def quotientChar {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [N.Characteristic] :
    MulAut G →* MulAut (G ⧸ N) where
  toFun e := QuotientGroup.congr N N e (Subgroup.characteristic_iff_map_eq.mp ‹_› e)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' _ _ := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

@[simp]
theorem quotientChar_mk {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [N.Characteristic]
    (e : MulAut G) (x : G) :
    quotientChar N e (QuotientGroup.mk x) = QuotientGroup.mk (e x) :=
  rfl

/-! ## Embedding problems with abelian kernel -/

/-- **Every embedding problem over `ℚ` with finite abelian kernel is solvable.**

If a finite group `W` is a Galois group over `ℚ` and `π : E →* W` is a surjection of finite groups
whose kernel is abelian, then `E` too is a Galois group over `ℚ`. -/
def AbelianKernelEP : Prop :=
  ∀ (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (π : E →* W),
    Function.Surjective π → IsMulCommutative ↥π.ker → IsInverseGalois W → IsInverseGalois E

/-- **Every embedding problem with finite abelian kernel is solvable regularly over `ℚ(T)`.**

The regular analogue of `AbelianKernelEP`. -/
def AbelianKernelEPRegular : Prop :=
  ∀ (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (π : E →* W),
    Function.Surjective π → IsMulCommutative ↥π.ker →
      IsRegularInverseGalois W → IsRegularInverseGalois E

/-! ## The reduction -/

/-- **Split embedding problems with kernel of prime power order reduce to embedding problems with
abelian kernel.**

The statement is for an arbitrary realization predicate `P` that is inherited by quotients.  The
argument is an induction on the order of the kernel `H`: if `H` is trivial the semidirect product
is its own outer factor, and otherwise the centre `Z` of `H` is a nontrivial characteristic
subgroup, so the action of `U` descends to `H ⧸ Z` and the induced surjection
`H ⋊ U →* (H ⧸ Z) ⋊ U` has abelian kernel while its target has a strictly smaller kernel. -/
theorem splitPrimePower_of_abelianKernel {P : ∀ (G : Type) [Group G], Prop}
    (hquot : IsQuotientClosed P)
    (h : ∀ (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (π : E →* W),
      Function.Surjective π → IsMulCommutative ↥π.ker → P W → P E)
    (H U : Type) [Group H] [Finite H] [Group U] [Finite U] (p : ℕ) [Fact p.Prime]
    (hp : IsPGroup p H) (φ : U →* MulAut H) (hU : P U) : P (H ⋊[φ] U) := by
  suffices key : ∀ (n : ℕ) (H U : Type) [Group H] [Finite H] [Group U] [Finite U],
      IsPGroup p H → ∀ φ : U →* MulAut H, Nat.card H ≤ n → P U → P (H ⋊[φ] U) from
    key (Nat.card H) H U hp φ le_rfl hU
  clear! H U
  intro n
  induction n with
  | zero =>
    intro H U _ _ _ _ _ _ hcard _
    exact absurd hcard (not_le.mpr Nat.card_pos)
  | succ n ih =>
    intro H U _ _ _ _ hp φ hcard hU
    rcases subsingleton_or_nontrivial H with hs | hs
    · haveI := hs
      exact hquot.of_mulEquiv (rightEquivOfSubsingleton φ).symm hU
    · haveI := hs
      -- The centre is a nontrivial characteristic subgroup.
      haveI hZnt : Nontrivial ↥(Subgroup.center H) := hp.center_nontrivial
      set φ' : U →* MulAut (H ⧸ Subgroup.center H) :=
        (quotientChar (Subgroup.center H)).comp φ
      have hnat : ∀ u : U, (QuotientGroup.mk' (Subgroup.center H)).comp (φ u).toMonoidHom
          = (φ' u).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H)) := by
        intro u
        ext x
        rfl
      set π : H ⋊[φ] U →* (H ⧸ Subgroup.center H) ⋊[φ'] U :=
        SemidirectProduct.map (QuotientGroup.mk' (Subgroup.center H)) (MonoidHom.id U) hnat
          with hπ
      -- The induced map is surjective.
      have hsurj : Function.Surjective π := by
        intro y
        obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) y.left
        exact ⟨⟨a, y.right⟩, SemidirectProduct.ext ha rfl⟩
      -- Its kernel consists of the images of the central elements.
      have hker : ∀ x : H ⋊[φ] U, x ∈ π.ker → x.left ∈ Subgroup.center H ∧ x.right = 1 := by
        intro x hx
        rw [MonoidHom.mem_ker] at hx
        refine ⟨?_, ?_⟩
        · have hl := congrArg SemidirectProduct.left hx
          simpa [hπ, QuotientGroup.eq_one_iff] using hl
        · have hr := congrArg SemidirectProduct.right hx
          simpa [hπ] using hr
      have hcomm : IsMulCommutative ↥π.ker := by
        refine ⟨⟨?_⟩⟩
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        obtain ⟨haZ, ha1⟩ := hker a ha
        obtain ⟨-, hb1⟩ := hker b hb
        refine Subtype.ext (SemidirectProduct.ext ?_ ?_)
        · show a.left * (φ a.right) b.left = b.left * (φ b.right) a.left
          rw [ha1, hb1]
          simpa using (Subgroup.mem_center_iff.mp haZ b.left).symm
        · show a.right * b.right = b.right * a.right
          rw [ha1, hb1, one_mul]
      -- The quotient is a smaller `p`-group.
      have hcard' : Nat.card (H ⧸ Subgroup.center H) ≤ n := by
        have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center H)
        have hZ : 1 < Nat.card ↥(Subgroup.center H) := Finite.one_lt_card
        have hqpos : 0 < Nat.card (H ⧸ Subgroup.center H) := Nat.card_pos
        have hlt : Nat.card (H ⧸ Subgroup.center H) < Nat.card H := by
          rw [hsplit]; nlinarith
        omega
      haveI : Finite (H ⋊[φ] U) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
      haveI : Finite ((H ⧸ Subgroup.center H) ⋊[φ'] U) :=
        Finite.of_equiv _ SemidirectProduct.equivProd.symm
      exact h _ _ π hsurj hcomm
        (ih (H ⧸ Subgroup.center H) U (hp.to_quotient _) φ' hcard' hU)

/-- **Split embedding problems over `ℚ` with kernel of prime power order reduce to embedding
problems with abelian kernel.** -/
theorem splitPrimePowerEP_of_abelianKernelEP (h : AbelianKernelEP) : SplitPrimePowerEP :=
  fun H U _ _ _ _ p _ hp φ hU =>
    splitPrimePower_of_abelianKernel isQuotientClosed_isInverseGalois
      (fun E W _ _ _ _ π hπ hker hW => h E W π hπ hker hW) H U p hp φ hU

/-- **Split embedding problems with kernel of prime power order reduce to embedding problems with
abelian kernel, regularly over `ℚ(T)`.** -/
theorem splitPrimePowerEPRegular_of_abelianKernelEPRegular (h : AbelianKernelEPRegular) :
    SplitPrimePowerEPRegular :=
  fun H U _ _ _ _ p _ hp φ hU =>
    splitPrimePower_of_abelianKernel isQuotientClosed_isRegularInverseGalois
      (fun E W _ _ _ _ π hπ hker hW => h E W π hπ hker hW) H U p hp φ hU

/-! ## Shafarevich's theorem, granted embedding problems with abelian kernel -/

/-- **Shafarevich's theorem, granted the solvability of embedding problems with abelian kernel.**

If every embedding problem over `ℚ` with finite abelian kernel is solvable, then every finite
solvable group is a Galois group over `ℚ`. -/
theorem isSolvable_isInverseGalois_of_abelianKernelEP (h : AbelianKernelEP)
    (G : Type) [Group G] [Finite G] [IsSolvable G] : IsInverseGalois G :=
  isSolvable_isInverseGalois_of_splitPrimePowerEP (splitPrimePowerEP_of_abelianKernelEP h) G

/-- **The regular form of Shafarevich's theorem, granted the solvability of embedding problems with
abelian kernel.**

If every embedding problem with finite abelian kernel is solvable regularly over `ℚ(T)`, then every
finite solvable group is the Galois group of a regular extension of `ℚ(T)`. -/
theorem isSolvable_isRegularInverseGalois_of_abelianKernelEPRegular (h : AbelianKernelEPRegular)
    (G : Type) [Group G] [Finite G] [IsSolvable G] : IsRegularInverseGalois G :=
  isSolvable_isRegularInverseGalois_of_splitPrimePowerEP
    (splitPrimePowerEPRegular_of_abelianKernelEPRegular h) G

end Shafarevich
