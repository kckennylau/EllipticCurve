/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import EllipticCurve.ProjectiveSpace.Graded.AlgHom
import EllipticCurve.ProjectiveSpace.Graded.RingEquiv

/-! # Graded ring isomorphisms
We define `GradedAlgEquiv 𝒜 ℬ` to mean isomorphisms of graded `R`-algebras, with notation
`𝒜 ≃ₐᵍ[R] ℬ`.

When possible, instead of parametrizing results over `(e : 𝒜 ≃ₐᵍ[R] ℬ)`, you should parametrize
over `[GradedEquivLike E 𝒜 ℬ] [AlgEquivClass E R A B] (e : E)`.
-/

variable {R A B C D ι S T U V : Type*}

/-- A graded `R`-algebra isomorphism between `𝒜` and `ℬ`. -/
structure GradedAlgEquiv (R : Type*) {A B ι S T : Type*} [Semiring A] [Semiring B]
    [CommSemiring S] [Algebra S A] [CommSemiring T] [Algebra T B]
    [CommSemiring R] [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B]
    [IsScalarTower R S A] [IsScalarTower R T B]
    [DecidableEq ι] [AddMonoid ι]
    (𝒜 : ι → Submodule S A) (ℬ : ι → Submodule T B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    extends A ≃ₐ[R] B, 𝒜 ≃+*ᵍ ℬ

@[inherit_doc]
notation:25 𝒜 " ≃ₐᵍ[" R "] " ℬ => GradedAlgEquiv R 𝒜 ℬ

/-- The underlying algebra isomorphism. -/
add_decl_doc GradedAlgEquiv.toAlgEquiv

/-- The underlying graded ring isomorphism. -/
add_decl_doc GradedAlgEquiv.toGradedRingEquiv

namespace GradedAlgEquiv

section Semiring
variable [Semiring A] [Semiring B] [Semiring C] [Semiring D]
  [CommSemiring S] [Algebra S A] [CommSemiring T] [Algebra T B]
  [CommSemiring U] [Algebra U C] [CommSemiring V] [Algebra V D]
  [CommSemiring R] [Algebra R S] [Algebra R T] [Algebra R U] [Algebra R V]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  [IsScalarTower R S A] [IsScalarTower R T B] [IsScalarTower R U C] [IsScalarTower R V D]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → Submodule S A} {ℬ : ι → Submodule T B}
  {𝒞 : ι → Submodule U C} {𝒟 : ι → Submodule V D}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞] [GradedAlgebra 𝒟]

/-- Turn an element of a type `E` satisfying `GradedEquivLike E 𝒜 ℬ` and `AlgEquivClass E R A B`
into an actual `GradedAlgEquiv`. This is declared as the default coercion from `E` to
`𝒜 ≃ₐᵍ[R] ℬ`. -/
@[coe]
def ofClass {E : Type*} [GradedEquivLike E 𝒜 ℬ] [AlgEquivClass E R A B] (e : E) : 𝒜 ≃ₐᵍ[R] ℬ :=
  { (e : 𝒜 ≃+*ᵍ ℬ), (e : 𝒜 →ₐᵍ[R] ℬ) with }

instance {E : Type*} [GradedEquivLike E 𝒜 ℬ] [AlgEquivClass E R A B] : CoeTC E (𝒜 ≃ₐᵍ[R] ℬ) :=
  ⟨ofClass⟩

section coe

instance : GradedEquivLike (𝒜 ≃ₐᵍ[R] ℬ) 𝒜 ℬ where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    cases e
    cases f
    congr 1
    exact AlgEquiv.ext (congr($h₁ ·))
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  map_mem_iff e {_ _} := map_mem_iff e.toGradedRingEquiv

instance : AlgEquivClass (𝒜 ≃ₐᵍ[R] ℬ) R A B where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes

/-- Two graded ring isomorphisms agree if they are defined by the same underlying function. -/
@[ext]
theorem ext {f g : 𝒜 ≃ₐᵍ[R] ℬ} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Consider using `congr(f $h)`. -/
protected theorem congr_arg {f : 𝒜 ≃ₐᵍ[R] ℬ} {x x' : A} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

/-- Consider using `congr($h x)`. -/
protected theorem congr_fun {f g : 𝒜 ≃ₐᵍ[R] ℬ} (h : f = g) (x : A) : f x = g x :=
  DFunLike.congr_fun h x

@[simp] theorem coe_mk (e h) : ⇑(⟨e, h⟩ : 𝒜 ≃ₐᵍ[R] ℬ) = e := rfl

@[simp]
theorem mk_coe (e : 𝒜 ≃ₐᵍ[R] ℬ) (e' h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨e, e', h₁, h₂⟩, h₃, h₄, h₅⟩, h₆⟩ : 𝒜 ≃ₐᵍ[R] ℬ) = e := ext fun _ => rfl

@[simp] theorem toGRingEquiv_eq_coe (f : 𝒜 ≃ₐᵍ[R] ℬ) : f.toGradedRingEquiv = ↑f := rfl

@[simp] theorem toAlgEquiv_eq_coe (f : 𝒜 ≃ₐᵍ[R] ℬ) : f.toAlgEquiv = ↑f := rfl

@[simp] theorem coe_toEquiv (f : 𝒜 ≃ₐᵍ[R] ℬ) : ⇑(f : A ≃ B) = f := rfl

@[simp] theorem coe_toAddEquiv (f : 𝒜 ≃ₐᵍ[R] ℬ) : ⇑(f : A ≃+ B) = f := rfl

@[simp, norm_cast]
theorem coe_toMulEquiv (f : 𝒜 ≃ₐᵍ[R] ℬ) : ⇑(f : A ≃* B) = f := rfl

@[simp] theorem coe_toRingEquiv (f : 𝒜 ≃ₐᵍ[R] ℬ) : ⇑(f : A ≃+* B) = f := rfl

@[simp] theorem coe_toAlgEquiv (f : 𝒜 ≃ₐᵍ[R] ℬ) : ⇑(f : A ≃ₐ[R] B) = f := rfl

@[simp] theorem coe_toGRingEquiv (f : 𝒜 ≃ₐᵍ[R] ℬ) : ⇑(f : 𝒜 ≃+*ᵍ ℬ) = f := rfl

@[simp] theorem coe_toGRingHom (f : 𝒜 ≃ₐᵍ[R] ℬ) : ⇑(f : 𝒜 →+*ᵍ ℬ) = f := rfl

@[simp] theorem coe_toGAlgHom (f : 𝒜 ≃ₐᵍ[R] ℬ) : ⇑(f : 𝒜 →ₐᵍ[R] ℬ) = f := rfl

theorem coe_injective : Function.Injective ((↑) : (𝒜 ≃ₐᵍ[R] ℬ) → A → B) :=
  DFunLike.coe_injective'

theorem coe_gRingHom_injective : Function.Injective ((↑) : (𝒜 ≃ₐᵍ[R] ℬ) → 𝒜 →+*ᵍ ℬ) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_ringHom_injective : Function.Injective ((↑) : (𝒜 ≃ₐᵍ[R] ℬ) → A →+* B) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_monoidHom_injective : Function.Injective ((↑) : (𝒜 ≃ₐᵍ[R] ℬ) → A →* B) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (𝒜 ≃ₐᵍ[R] ℬ) → A →+ B) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_ringEquiv_injective : Function.Injective ((↑) : (𝒜 ≃ₐᵍ[R] ℬ) → A ≃+* B) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_mulEquiv_injective : Function.Injective ((↑) : (𝒜 ≃ₐᵍ[R] ℬ) → A ≃* B) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_addEquiv_injective : Function.Injective ((↑) : (𝒜 ≃ₐᵍ[R] ℬ) → A ≃+ B) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_equiv_injective : Function.Injective ((↑) : (𝒜 ≃ₐᵍ[R] ℬ) → A ≃ B) :=
  fun _ _ h ↦ coe_injective congr($h)

end coe

section map
variable (e : 𝒜 ≃ₐᵍ[R] ℬ)

/-- A graded ring isomorphism preserves zero. -/
protected theorem map_zero : e 0 = 0 :=
  map_zero e

/-- A graded ring isomorphism preserves one. -/
protected theorem map_one : e 1 = 1 :=
  map_one e

/-- A graded ring isomorphism preserves addition. -/
protected theorem map_add (x y : A) : e (x + y) = e x + e y :=
  map_add e x y

/-- A graded ring isomorphism preserves multiplication. -/
protected theorem map_mul (x y : A) : e (x * y) = e x * e y :=
  map_mul e x y

protected theorem map_pow (x : A) (n : ℕ) : e (x ^ n) = e x ^ n :=
  map_pow e x n

protected theorem map_eq_zero_iff (x : A) : e x = 0 ↔ x = 0 :=
  e.toRingEquiv.map_eq_zero_iff

protected theorem map_ne_zero_iff (x : A) : e x ≠ 0 ↔ x ≠ 0 :=
  e.toRingEquiv.map_ne_zero_iff

protected theorem map_eq_one_iff (x : A) : e x = 1 ↔ x = 1 :=
  e.toRingEquiv.map_eq_one_iff

protected theorem map_ne_one_iff (x : A) : e x ≠ 1 ↔ x ≠ 1 :=
  e.toRingEquiv.map_ne_one_iff

end map

section bijective

protected theorem bijective (e : 𝒜 ≃ₐᵍ[R] ℬ) : Function.Bijective e :=
  EquivLike.bijective e

protected theorem injective (e : 𝒜 ≃ₐᵍ[R] ℬ) : Function.Injective e :=
  EquivLike.injective e

protected theorem surjective (e : 𝒜 ≃ₐᵍ[R] ℬ) : Function.Surjective e :=
  EquivLike.surjective e

end bijective

section symm

/-- The inverse of a graded ring isomorphism is a graded ring isomorphism. -/
@[symm] protected def symm (e : 𝒜 ≃ₐᵍ[R] ℬ) : ℬ ≃ₐᵍ[R] 𝒜 :=
  { e.toAlgEquiv.symm, e.toGradedRingEquiv.symm with }

@[simp] theorem invFun_eq_symm (f : 𝒜 ≃ₐᵍ[R] ℬ) : EquivLike.inv f = f.symm := rfl

@[simp] theorem symm_symm (e : 𝒜 ≃ₐᵍ[R] ℬ) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (GradedAlgEquiv.symm : (𝒜 ≃ₐᵍ[R] ℬ) → ℬ ≃ₐᵍ[R] 𝒜) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem mk_coe' (e : 𝒜 ≃ₐᵍ[R] ℬ) (f h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨f, ⇑e, h₁, h₂⟩, h₃, h₄, h₅⟩, h₆⟩ : ℬ ≃ₐᵍ[R] 𝒜) = e.symm :=
  symm_bijective.injective <| ext fun _ ↦ rfl

/-- Auxiliary definition to avoid looping in `dsimp` with `RingEquiv.symm_mk`. -/
protected def symm_mk.aux (f : B → A) (g h₁ h₂ h₃ h₄ h₅ h₆) :=
  (mk (R := R) (𝒜 := ℬ) (ℬ := 𝒜) ⟨⟨f, g, h₁, h₂⟩, h₃, h₄, h₅⟩ h₆).symm

@[simp]
theorem symm_mk (f : B → A) (g h₁ h₂ h₃ h₄ h₅ h₆) :
    (mk ⟨⟨f, g, h₁, h₂⟩, h₃, h₄, h₅⟩ h₆).symm =
      { symm_mk.aux (R := R) (𝒜 := 𝒜) (ℬ := ℬ) f g h₁ h₂ h₃ h₄ h₅ h₆ with
        toFun := g
        invFun := f } :=
  rfl

@[simp] theorem coe_toEquiv_symm (e : 𝒜 ≃ₐᵍ[R] ℬ) : (e.symm : B ≃ A) = (e : A ≃ B).symm := rfl

@[simp]
theorem coe_toMulEquiv_symm (e : 𝒜 ≃ₐᵍ[R] ℬ) : (e.symm : B ≃* A) = (e : A ≃* B).symm := rfl

@[simp]
theorem coe_toAddEquiv_symm (e : 𝒜 ≃ₐᵍ[R] ℬ) : (e.symm : B ≃+ A) = (e : A ≃+ B).symm := rfl

@[simp]
theorem coe_toRingEquiv_symm (e : 𝒜 ≃ₐᵍ[R] ℬ) : (e.symm : B ≃* A) = (e : A ≃* B).symm := rfl

@[simp]
theorem apply_symm_apply (e : 𝒜 ≃ₐᵍ[R] ℬ) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : 𝒜 ≃ₐᵍ[R] ℬ) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

theorem image_eq_preimage (e : 𝒜 ≃ₐᵍ[R] ℬ) (s : Set A) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s

theorem symm_apply_eq (e : 𝒜 ≃ₐᵍ[R] ℬ) {x : B} {y : A} :
    e.symm x = y ↔ x = e y := Equiv.symm_apply_eq _

theorem eq_symm_apply (e : 𝒜 ≃ₐᵍ[R] ℬ) {x : B} {y : A} :
    y = e.symm x ↔ e y = x := Equiv.eq_symm_apply _

end symm

section Simps

/-- See Note [custom simps projection] -/
def Simps.apply (e : 𝒜 ≃ₐᵍ[R] ℬ) : A → B := ⇑e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : 𝒜 ≃ₐᵍ[R] ℬ) : B → A := ⇑e.symm

initialize_simps_projections GradedAlgEquiv (toFun → apply, invFun → symm_apply)

end Simps

section refl

variable (R 𝒜) in
/-- The identity map as a graded ring isomorphism. -/
@[simps!] protected def refl : 𝒜 ≃ₐᵍ[R] 𝒜 :=
  { AlgEquiv.refl, GradedRingEquiv.refl 𝒜 with }

@[simp] theorem symm_refl : (GradedAlgEquiv.refl R 𝒜).symm = .refl R 𝒜 := rfl

@[simp] theorem coe_refl : ⇑(GradedAlgEquiv.refl R 𝒜) = id := rfl

@[simp] theorem coe_toRingEquiv_refl : (GradedAlgEquiv.refl R 𝒜 : A ≃+* A) = .refl A := rfl

@[simp] theorem coe_addEquiv_refl : (GradedAlgEquiv.refl R 𝒜 : A ≃+ A) = AddEquiv.refl A := rfl

@[simp] theorem coe_mulEquiv_refl : (GradedAlgEquiv.refl R 𝒜 : A ≃* A) = MulEquiv.refl A := rfl

@[simp] theorem toEquiv_refl : GradedAlgEquiv.refl R 𝒜 = Equiv.refl A := rfl

@[simp]
theorem coe_gRingHom_refl : (GradedAlgEquiv.refl R 𝒜 : 𝒜 →+*ᵍ 𝒜) = .id 𝒜 := rfl

@[simp] theorem coe_ringHom_refl : (GradedAlgEquiv.refl R 𝒜 : A →+* A) = .id A := rfl

@[simp] theorem coe_monoidHom_refl : (GradedAlgEquiv.refl R 𝒜 : A →* A) = .id A := rfl

@[simp] theorem coe_addMonoidHom_refl : (GradedAlgEquiv.refl R 𝒜 : A →+ A) = .id A := rfl

end refl

section trans
variable (e₁ : 𝒜 ≃ₐᵍ[R] ℬ) (e₂ : ℬ ≃ₐᵍ[R] 𝒞)

/-- The composition of two graded ring isomorphisms. -/
@[trans, simps! apply] protected def trans (e₁ : 𝒜 ≃ₐᵍ[R] ℬ) (e₂ : ℬ ≃ₐᵍ[R] 𝒞) : 𝒜 ≃ₐᵍ[R] 𝒞 :=
  { e₁.toAlgEquiv.trans e₂.toAlgEquiv, e₁.toGradedRingEquiv.trans e₂.toGradedRingEquiv with }

@[simp] theorem coe_trans : ⇑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

theorem symm_trans_apply (a : C) : (e₁.trans e₂).symm a = e₁.symm (e₂.symm a) := rfl

@[simp] theorem symm_trans : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm := rfl

@[simp] theorem coe_ringEquiv_trans : (e₁.trans e₂ : A ≃+* C) = (e₁ : A ≃+* B).trans ↑e₂ := rfl

@[simp] theorem coe_mulEquiv_trans : (e₁.trans e₂ : A ≃* C) = (e₁ : A ≃* B).trans ↑e₂ := rfl

@[simp] theorem coe_addEquiv_trans : (e₁.trans e₂ : A ≃+ C) = (e₁ : A ≃+ B).trans ↑e₂ := rfl

@[simp] theorem coe_gRingHom_trans : (e₁.trans e₂ : 𝒜 →+*ᵍ 𝒞) = (e₂ : ℬ →+*ᵍ 𝒞).comp ↑e₁ := rfl

@[simp] theorem coe_ringHom_trans : (e₁.trans e₂ : A →+* C) = (e₂ : B →+* C).comp ↑e₁ := rfl

@[simp] theorem coe_monoidHom_trans : (e₁.trans e₂ : A →* C) = (e₂ : B →* C).comp ↑e₁ := rfl

@[simp] theorem coe_addMonoidHom_trans : (e₁.trans e₂ : A →+ C) = (e₂ : B →+ C).comp ↑e₁ := rfl

@[simp] theorem self_trans_symm : e₁.trans e₁.symm = .refl R 𝒜 :=
  coe_equiv_injective e₁.toEquiv.self_trans_symm

@[simp] theorem symm_trans_self : e₁.symm.trans e₁ = .refl R ℬ :=
  coe_equiv_injective e₁.toEquiv.symm_trans_self

end trans

section ofBijective

variable {F : Type*} [GradedFunLike F 𝒜 ℬ] [AlgHomClass F R A B]

/-- Produce a graded ring isomorphism from a bijective graded ring homomorphism. -/
noncomputable def ofBijective (f : F) (hf : Function.Bijective f) : 𝒜 ≃ₐᵍ[R] ℬ :=
  { AlgEquiv.ofBijective (f : A →ₐ[R] B) hf, GradedRingEquiv.ofBijective f hf with }

variable (f : F) (hf : Function.Bijective f)

@[simp] theorem coe_ofBijective : ⇑(ofBijective f hf) = f := rfl

@[simp] theorem coe_toGAlgHom_ofBijective : (ofBijective f hf : 𝒜 →ₐᵍ[R] ℬ) = f := rfl

theorem ofBijective_apply (x : A) : ofBijective f hf x = f x := rfl

@[simp]
lemma ofBijective_symm_comp (f : 𝒜 →ₐᵍ[R] ℬ) (hf : Function.Bijective f) :
    ((ofBijective f hf).symm : ℬ →ₐᵍ[R] 𝒜).comp f = .id R 𝒜 :=
  GradedAlgHom.ext fun _ ↦ (ofBijective f hf).injective <| apply_symm_apply ..

@[simp]
lemma comp_ofBijective_symm (f : 𝒜 →ₐᵍ[R] ℬ) (hf : Function.Bijective f) :
    f.comp ((ofBijective f hf).symm : ℬ →ₐᵍ[R] 𝒜) = .id R ℬ :=
  GradedAlgHom.ext fun _ ↦ (ofBijective f hf).symm.injective <| apply_symm_apply ..

@[simp]
theorem comp_symm (e : 𝒜 ≃ₐᵍ[R] ℬ) : (e : 𝒜 →ₐᵍ[R] ℬ).comp (e.symm : ℬ →ₐᵍ[R] 𝒜) = .id R ℬ :=
  GradedAlgHom.ext e.apply_symm_apply

@[simp]
theorem symm_comp (e : 𝒜 ≃ₐᵍ[R] ℬ) : (e.symm : ℬ →ₐᵍ[R] 𝒜).comp (e : 𝒜 →ₐᵍ[R] ℬ) = .id R 𝒜 :=
  GradedAlgHom.ext e.symm_apply_apply

end ofBijective

/-- Construct a mutually-inverse pair of graded ring homomorphisms into a graded ring isomorphism.
-/
def ofGRingHom (f : 𝒜 →ₐᵍ[R] ℬ) (g : ℬ →ₐᵍ[R] 𝒜) (h₁ : g.comp f = GradedRingHom.id 𝒜)
    (h₂ : f.comp g = GradedRingHom.id ℬ) : 𝒜 ≃ₐᵍ[R] ℬ where
  __ := f
  __ := RingEquiv.ofRingHom f.toRingHom g.toRingHom congr($h₂) congr($h₁)

@[simp] lemma coe_ofGRingHom (f : 𝒜 →ₐᵍ[R] ℬ) (g h₁ h₂) :
    ⇑(ofGRingHom f g h₁ h₂ : 𝒜 ≃ₐᵍ[R] ℬ) = f := rfl

@[simp] lemma toGRingHom_ofGRingHom (f : 𝒜 →ₐᵍ[R] ℬ) (g h₁ h₂) :
    (ofGRingHom f g h₁ h₂ : 𝒜 →ₐᵍ[R] ℬ) = f := rfl

@[simp] lemma toMonoidHom_ofGRingHom (f : 𝒜 →ₐᵍ[R] ℬ) (g h₁ h₂) :
    (ofGRingHom f g h₁ h₂ : A →* B) = f := rfl

@[simp] lemma toAddMonoidHom_ofGRingHom (f : 𝒜 →ₐᵍ[R] ℬ) (g h₁ h₂) :
    (ofGRingHom f g h₁ h₂ : A →+ B) = f := rfl

@[simp] lemma symm_ofGRingHom (f : 𝒜 →ₐᵍ[R] ℬ) (g h₁ h₂) :
    (ofGRingHom f g h₁ h₂).symm = ofGRingHom g f h₂ h₁ := rfl

end Semiring

section Ring
variable [Ring A] [Ring B]
  [CommSemiring S] [Algebra S A] [CommSemiring T] [Algebra T B]
  [CommSemiring R] [Algebra R S] [Algebra R T]
  [Algebra R A] [Algebra R B]
  [IsScalarTower R S A] [IsScalarTower R T B]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → Submodule S A} {ℬ : ι → Submodule T B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (e : 𝒜 ≃ₐᵍ[R] ℬ) (x y : A)

protected theorem map_neg : e (-x) = -e x :=
  map_neg e x

protected theorem map_sub : e (x - y) = e x - e y :=
  map_sub e x y

protected theorem map_neg_one : e (-1) = -1 :=
  e.toAlgEquiv.map_neg_one

protected theorem map_eq_neg_one_iff {x : A} : e x = -1 ↔ x = -1 :=
  e.toAlgEquiv.map_eq_neg_one_iff

end Ring

end GradedAlgEquiv
