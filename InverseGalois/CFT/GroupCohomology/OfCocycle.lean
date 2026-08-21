import Mathlib

/-!
# The group extension attached to a multiplicative `2`-cocycle

Let `G` be a group acting on an abelian group `M` by group automorphisms, and let
`f : G × G → M` satisfy the multiplicative `2`-cocycle condition
`f (g * h, j) * f (g, h) = g • f (h, j) * f (g, h * j)`.

This file constructs the group extension `1 → M → E → G → 1` classified by `f`. The underlying
type of `E` is `M × G` and the multiplication is twisted by `f`; associativity of the
multiplication is exactly the cocycle condition. This is one half of the dictionary between
`groupCohomology.H2` and equivalence classes of group extensions.

## Main definitions

* `groupCohomology.ofMulCocycle₂ hf`: the group whose underlying type is `M × G` and whose
  multiplication is `(m₁, g₁) * (m₂, g₂) = (m₁ * g₁ • m₂ * f (g₁, g₂), g₁ * g₂)`.
* `groupCohomology.ofMulCocycle₂.inlHom`, `groupCohomology.ofMulCocycle₂.sndHom`: the
  inclusion `M →* ofMulCocycle₂ hf` and the projection `ofMulCocycle₂ hf →* G`.
* `groupCohomology.ofMulCocycle₂.toGroupExtension hf`: the resulting extension of `G` by `M`.
* `groupCohomology.ofMulCocycle₂.splittingOfCoboundary`: the splitting of the extension
  produced by an explicit trivialisation of `f` as a coboundary.
* `groupCohomology.ofMulCocycle₂.equivOfCoboundary`: cohomologous cocycles give equivalent
  extensions.

## Main results

* `groupCohomology.ofMulCocycle₂.inl_conj` and
  `groupCohomology.ofMulCocycle₂.conjAct_inl`: the conjugation action of the extension on `M`
  recovers the given action of `G` on `M`.
* `groupCohomology.ofMulCocycle₂.nonempty_splitting_of_isMulCoboundary₂`: a cocycle which is a
  coboundary gives a split extension.
* `groupCohomology.ofMulCocycle₂.nonempty_splitting_of_H2π_eq_zero`: a cocycle whose class in
  `groupCohomology.H2` vanishes gives a split extension.
-/

namespace groupCohomology

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M] {f f' : G × G → M}

/-- The group extension of `G` by `M` attached to a multiplicative `2`-cocycle `f`. Its
underlying type is `M × G`; the multiplication, unit and inverse are twisted by `f`. -/
structure ofMulCocycle₂ (hf : IsMulCocycle₂ f) where
  /-- The component in the abelian group `M`. -/
  fst : M
  /-- The component in the quotient group `G`. -/
  snd : G

namespace ofMulCocycle₂

variable {hf : IsMulCocycle₂ f}

@[ext]
theorem ext {x y : ofMulCocycle₂ hf} (h₁ : x.fst = y.fst) (h₂ : x.snd = y.snd) : x = y := by
  cases x; cases y; simp_all

@[simp]
theorem mk_fst (m : M) (g : G) : (mk m g : ofMulCocycle₂ hf).fst = m := rfl

@[simp]
theorem mk_snd (m : M) (g : G) : (mk m g : ofMulCocycle₂ hf).snd = g := rfl

instance : Mul (ofMulCocycle₂ hf) :=
  ⟨fun x y ↦ ⟨x.fst * x.snd • y.fst * f (x.snd, y.snd), x.snd * y.snd⟩⟩

instance : One (ofMulCocycle₂ hf) := ⟨⟨(f (1, 1))⁻¹, 1⟩⟩

instance : Inv (ofMulCocycle₂ hf) :=
  ⟨fun x ↦ ⟨(f (1, 1))⁻¹ * (f (x.snd⁻¹, x.snd))⁻¹ * (x.snd⁻¹ • x.fst)⁻¹, x.snd⁻¹⟩⟩

@[simp]
theorem mul_fst (x y : ofMulCocycle₂ hf) :
    (x * y).fst = x.fst * x.snd • y.fst * f (x.snd, y.snd) := rfl

@[simp]
theorem mul_snd (x y : ofMulCocycle₂ hf) : (x * y).snd = x.snd * y.snd := rfl

@[simp]
theorem one_fst : (1 : ofMulCocycle₂ hf).fst = (f (1, 1))⁻¹ := rfl

@[simp]
theorem one_snd : (1 : ofMulCocycle₂ hf).snd = 1 := rfl

@[simp]
theorem inv_fst (x : ofMulCocycle₂ hf) :
    x⁻¹.fst = (f (1, 1))⁻¹ * (f (x.snd⁻¹, x.snd))⁻¹ * (x.snd⁻¹ • x.fst)⁻¹ := rfl

@[simp]
theorem inv_snd (x : ofMulCocycle₂ hf) : x⁻¹.snd = x.snd⁻¹ := rfl

/-- A rearrangement lemma in a commutative group, used to deduce associativity of the
multiplication on `ofMulCocycle₂ hf` from the cocycle condition. -/
private theorem assoc_aux {m a b F₁ F₂ C F₃ : M} (h : F₂ * F₁ = C * F₃) :
    m * a * F₁ * b * F₂ = m * (a * b * C) * F₃ := by
  apply Additive.ofMul.injective
  replace h := congrArg Additive.ofMul h
  simp only [ofMul_mul] at h ⊢
  linear_combination (norm := abel) h

instance instGroup : Group (ofMulCocycle₂ hf) :=
  Group.ofLeftAxioms
    (fun x y z ↦ by
      refine ext ?_ (mul_assoc _ _ _)
      simp only [mul_fst, mul_snd, smul_mul', mul_smul]
      exact assoc_aux (hf x.snd y.snd z.snd))
    (fun x ↦ by
      refine ext ?_ (one_mul _)
      simp only [mul_fst, one_fst, one_snd, one_smul,
        map_one_fst_of_isMulCocycle₂ hf x.snd]
      rw [mul_comm, mul_inv_cancel_left])
    (fun x ↦ by
      refine ext ?_ (inv_mul_cancel _)
      simp only [mul_fst, inv_fst, inv_snd, one_fst]
      simp [mul_assoc])

/-- The inclusion of `M` into the extension attached to a multiplicative `2`-cocycle `f`. -/
def inlHom (hf : IsMulCocycle₂ f) : M →* ofMulCocycle₂ hf where
  toFun m := ⟨m * (f (1, 1))⁻¹, 1⟩
  map_one' := by ext <;> simp
  map_mul' m₁ m₂ := by
    refine ext ?_ (by simp)
    simp only [mul_fst, one_smul, smul_mul', map_one_fst_of_isMulCocycle₂ hf 1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

@[simp]
theorem inlHom_apply (m : M) : inlHom hf m = ⟨m * (f (1, 1))⁻¹, 1⟩ := rfl

/-- The projection from the extension attached to a multiplicative `2`-cocycle `f` onto `G`. -/
def sndHom (hf : IsMulCocycle₂ f) : ofMulCocycle₂ hf →* G where
  toFun := snd
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem sndHom_apply (x : ofMulCocycle₂ hf) : sndHom hf x = x.snd := rfl

/-- The group extension `1 → M → ofMulCocycle₂ hf → G → 1` attached to a multiplicative
`2`-cocycle `f`. -/
def toGroupExtension (hf : IsMulCocycle₂ f) : GroupExtension M (ofMulCocycle₂ hf) G where
  inl := inlHom hf
  rightHom := sndHom hf
  inl_injective m₁ m₂ h := by
    simpa using congrArg fst h
  range_inl_eq_ker_rightHom := by
    ext x
    simp only [MonoidHom.mem_range, MonoidHom.mem_ker, sndHom_apply]
    constructor
    · rintro ⟨m, rfl⟩
      rfl
    · intro hx
      exact ⟨x.fst * f (1, 1), by refine ext ?_ hx.symm; simp [mul_assoc]⟩
  rightHom_surjective g := ⟨⟨1, g⟩, rfl⟩

@[simp]
theorem toGroupExtension_inl_apply (m : M) :
    (toGroupExtension hf).inl m = ⟨m * (f (1, 1))⁻¹, 1⟩ := rfl

@[simp]
theorem toGroupExtension_rightHom_apply (x : ofMulCocycle₂ hf) :
    (toGroupExtension hf).rightHom x = x.snd := rfl

/-- Conjugating `inl n` by an element `x` of the extension gives `inl (x.snd • n)`: the
extension induces the action of `G` on `M` that we started with. -/
theorem inl_conj (x : ofMulCocycle₂ hf) (n : M) :
    x * (toGroupExtension hf).inl n * x⁻¹ = (toGroupExtension hf).inl (x.snd • n) := by
  have key := smul_map_inv_div_map_inv_of_isMulCocycle₂ hf x.snd
  rw [map_one_snd_of_isMulCocycle₂ hf x.snd, div_eq_div_iff_mul_eq_mul] at key
  refine ext ?_ (by simp)
  simp only [mul_fst, mul_snd, toGroupExtension_inl_apply, mk_fst, inv_fst, inv_snd,
    smul_mul', smul_inv', mul_one, map_one_snd_of_isMulCocycle₂ hf x.snd, ← mul_smul,
    mul_inv_cancel, one_smul]
  apply Additive.ofMul.injective
  replace key := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at key ⊢
  linear_combination (norm := abel) -key

/-- The conjugation action of the extension on `M` is the given action of `G` on `M`. -/
theorem conjAct_inl (x : ofMulCocycle₂ hf) (n : M) :
    (toGroupExtension hf).conjAct x n = x.snd • n :=
  (toGroupExtension hf).inl_injective <| by
    rw [GroupExtension.inl_conjAct_comm, inl_conj]

/-- If a `2`-cocycle `f` is the coboundary of `b : G → M`, the extension it defines splits,
with splitting `g ↦ ((b g)⁻¹, g)`. -/
def splittingOfCoboundary (hf : IsMulCocycle₂ f) (b : G → M)
    (hb : ∀ g h : G, g • b h / b (g * h) * b g = f (g, h)) :
    (toGroupExtension hf).Splitting where
  __ := MonoidHom.mk' (fun g ↦ (⟨(b g)⁻¹, g⟩ : ofMulCocycle₂ hf)) fun g h ↦ by
    refine ext ?_ rfl
    simp only [mul_fst, smul_inv', ← hb g h, div_eq_mul_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rightInverse_rightHom _ := rfl

/-- A `2`-cocycle satisfying the multiplicative `2`-coboundary condition defines a split
extension. -/
theorem nonempty_splitting_of_isMulCoboundary₂ (hf : IsMulCocycle₂ f)
    (hb : IsMulCoboundary₂ f) : Nonempty (toGroupExtension hf).Splitting :=
  ⟨splittingOfCoboundary hf hb.choose hb.choose_spec⟩

/-- Cohomologous `2`-cocycles define equivalent group extensions. The equivalence is
`(m, g) ↦ (m * (b g)⁻¹, g)`. -/
def equivOfCoboundary (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f') (b : G → M)
    (hb : ∀ g h : G, f' (g, h) = g • b h / b (g * h) * b g * f (g, h)) :
    (toGroupExtension hf).Equiv (toGroupExtension hf') where
  toFun x := ⟨x.fst * (b x.snd)⁻¹, x.snd⟩
  invFun x := ⟨x.fst * b x.snd, x.snd⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by
    refine ext ?_ rfl
    simp only [mul_fst, mul_snd, smul_mul', smul_inv', hb x.snd y.snd, div_eq_mul_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  inl_comm := by
    funext m
    refine ext ?_ rfl
    show m * (f (1, 1))⁻¹ * (b 1)⁻¹ = m * (f' (1, 1))⁻¹
    simp only [hb 1 1, one_smul, mul_one, div_eq_mul_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rightHom_comm := rfl

end ofMulCocycle₂

section Universe

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M] {f : G × G → M}

/-- If the class of a multiplicative `2`-cocycle `f` in `H²(G, M)` vanishes, the group
extension attached to `f` splits. -/
theorem ofMulCocycle₂.nonempty_splitting_of_H2π_eq_zero (hf : IsMulCocycle₂ f)
    (h : H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hf) = 0) :
    Nonempty (ofMulCocycle₂.toGroupExtension hf).Splitting :=
  ofMulCocycle₂.nonempty_splitting_of_isMulCoboundary₂ hf <|
    isMulCoboundary₂_of_mem_coboundaries₂ _ ((H2π_eq_zero_iff _).1 h)

end Universe

end groupCohomology
