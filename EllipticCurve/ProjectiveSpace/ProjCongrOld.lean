/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.ProjectiveSpace.TensorProduct.ProjMap

/-! # Isomorphism of Graded Algebras and Induced Isomorphism of Proj
-/

universe u

section arbitrary_index

variable {R₁ R₂ R₃ A₁ A₂ A₃ ι : Type*}
  [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing A₁] [CommRing A₂] [CommRing A₃]
  [Algebra R₁ A₁] [Algebra R₂ A₂] [Algebra R₃ A₃]

structure GradedAlgEquiv (𝒜₁ : ι → Submodule R₁ A₁) (𝒜₂ : ι → Submodule R₂ A₂)
    extends RingEquiv A₁ A₂, GradedAlgHom 𝒜₁ 𝒜₂

@[inherit_doc] notation 𝒜 " ≃ᵍᵃ " ℬ => GradedAlgEquiv 𝒜 ℬ

namespace GradedAlgEquiv

variable {𝒜₁ : ι → Submodule R₁ A₁} {𝒜₂ : ι → Submodule R₂ A₂} {𝒜₃ : ι → Submodule R₃ A₃}

instance (priority := 100) : EquivLike (𝒜₁ ≃ᵍᵃ 𝒜₂) A₁ A₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by
    cases e₁
    cases e₂
    congr
    exact RingEquiv.toRingHom_injective <| RingHom.ext (congr($h₁ ·))

instance (priority := 100) : RingEquivClass (𝒜₁ ≃ᵍᵃ 𝒜₂) A₁ A₂ where
  map_mul f := f.map_mul
  map_add f := f.map_add

@[simp] lemma coe_toRingEquiv (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) : (e.toRingEquiv : A₁ → A₂) = e := rfl

@[simp] lemma coe_toGradedAlgHom (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) : (e.toGradedAlgHom : A₁ → A₂) = e := rfl

@[ext]
theorem ext {f g : 𝒜₁ ≃ᵍᵃ 𝒜₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[refl]
def refl : 𝒜₁ ≃ᵍᵃ 𝒜₁ where
  __ := RingEquiv.refl A₁
  map_one' := rfl
  map_zero' := rfl
  map_mem' _ _ := id

@[trans] protected def trans (e₁₂ : 𝒜₁ ≃ᵍᵃ 𝒜₂) (e₂₃ : 𝒜₂ ≃ᵍᵃ 𝒜₃) : 𝒜₁ ≃ᵍᵃ 𝒜₃ where
  __ := RingEquiv.trans e₁₂.toRingEquiv e₂₃
  map_one' := by simp
  map_zero' := by simp
  map_mem' i x := e₂₃.map_mem ∘ e₁₂.map_mem

@[simp] lemma trans_apply (e₁₂ : 𝒜₁ ≃ᵍᵃ 𝒜₂) (e₂₃ : 𝒜₂ ≃ᵍᵃ 𝒜₃) (x : A₁) :
    (e₁₂.trans e₂₃) x = e₂₃ (e₁₂ x) := rfl

variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂]

@[symm]
protected def symm
    (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) : 𝒜₂ ≃ᵍᵃ 𝒜₁ where
  __ := RingEquiv.symm e
  map_one' := e.symm_apply_eq.mpr e.map_one.symm
  map_zero' := e.symm_apply_eq.mpr e.map_zero.symm
  map_mem' i x hx := by
    change e.toRingEquiv.symm x ∈ 𝒜₁ i
    classical
    rw [← DirectSum.sum_support_decompose 𝒜₁ (e.toRingEquiv.symm x : A₁)]
    refine sum_mem fun j hj ↦ ?_
    rw [DFinsupp.mem_support_iff, ne_eq, ← ZeroMemClass.coe_eq_zero, ← ne_eq,
      ← e.map_ne_zero_iff, coe_toRingEquiv, ← coe_toGradedAlgHom,
      e.toGradedAlgHom.map_coe_decompose, coe_toGradedAlgHom, ← coe_toRingEquiv, e.apply_symm_apply,
      DirectSum.decompose_of_mem _ hx, DirectSum.of_apply] at hj
    by_cases h : i = j
    · subst h; exact Subtype.prop _
    · rw [dif_neg h] at hj
      exact (hj rfl).elim

@[simp] lemma apply_symm_apply (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) (x : A₂) : e (e.symm x) = x := e.right_inv x

@[simp] lemma self_trans_symm (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) : e.trans e.symm = GradedAlgEquiv.refl :=
  ext e.left_inv

@[simp] lemma symm_trans_self (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) : e.symm.trans e = GradedAlgEquiv.refl :=
  ext e.right_inv

end GradedAlgEquiv

end arbitrary_index


section irrelevant

variable {R₁ R₂ ι : Type*} {A₁ A₂ : Type u}
  [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂] [Algebra R₁ A₁] [Algebra R₂ A₂]
  [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
  (𝒜₁ : ι → Submodule R₁ A₁) (𝒜₂ : ι → Submodule R₂ A₂)
  [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂] (e : 𝒜₁ ≃ᵍᵃ 𝒜₂)

theorem GradedAlgEquiv.admissible :
    HomogeneousIdeal.irrelevant 𝒜₂ ≤ (HomogeneousIdeal.irrelevant 𝒜₁).map e.toGradedAlgHom := by
  intro x hx
  rw [← e.apply_symm_apply x]
  refine Ideal.mem_map_of_mem _ (?_ : _ ∈ HomogeneousIdeal.irrelevant 𝒜₁)
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hx ⊢
  rw [← coe_toGradedAlgHom e.symm, ← e.symm.map_coe_decompose, hx, map_zero]

end irrelevant


namespace AlgebraicGeometry.Proj

open CategoryTheory HomogeneousIdeal

notation:max 𝒜"₊" => irrelevant 𝒜

variable {R₁ R₂ R₃ : Type*} {A₁ A₂ A₃ : Type u}
  [CommRing R₁] [CommRing R₂] [CommRing R₃]
  [CommRing A₁] [CommRing A₂] [CommRing A₃] [Algebra R₁ A₁] [Algebra R₂ A₂] [Algebra R₃ A₃]
  (𝒜₁ : ℕ → Submodule R₁ A₁) (𝒜₂ : ℕ → Submodule R₂ A₂) (𝒜₃ : ℕ → Submodule R₃ A₃)

-- MOVE
variable {𝒜₁ 𝒜₂ 𝒜₃} (f₂₃ : 𝒜₂ →ᵍᵃ 𝒜₃) (f₁₂ : 𝒜₁ →ᵍᵃ 𝒜₂)
def _root_.GradedAlgHom.comp : 𝒜₁ →ᵍᵃ 𝒜₃ where
  __ := f₂₃.toRingHom.comp f₁₂
  map_mem' _ _ := f₂₃.map_mem ∘ f₁₂.map_mem

def _root_.GradedAlgHom.id : 𝒜₁ →ᵍᵃ 𝒜₁ where
  __ := RingHom.id A₁
  map_mem' _ _ h := h

@[simp] lemma _root_.GradedAlgHom.id_apply (x : A₁) : (GradedAlgHom.id : 𝒜₁ →ᵍᵃ 𝒜₁) x = x := rfl

@[simp] lemma _root_.GradedAlgHom.comp_apply (x : A₁) :
    (f₂₃.comp f₁₂) x = f₂₃ (f₁₂ x) := rfl

@[simp] lemma _root_.GradedAlgEquiv.trans_toGradedAlgHom
    (e₁₂ : 𝒜₁ ≃ᵍᵃ 𝒜₂) (e₂₃ : 𝒜₂ ≃ᵍᵃ 𝒜₃) :
    (e₁₂.trans e₂₃).toGradedAlgHom = e₂₃.toGradedAlgHom.comp e₁₂.toGradedAlgHom :=
  rfl

@[simp] lemma _root_.GradedAlgEquiv.refl_toGradedAlgHom (𝒜 : ℕ → Submodule R₁ A₁) :
    (GradedAlgEquiv.refl : 𝒜 ≃ᵍᵃ 𝒜).toGradedAlgHom = GradedAlgHom.id := rfl

variable [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂] [GradedAlgebra 𝒜₃]

lemma _root_.HomogeneousIdeal.map_comp (P : HomogeneousIdeal 𝒜₁) :
    P.map (f₂₃.comp f₁₂) = (P.map f₁₂).map f₂₃ :=
  HomogeneousIdeal.ext (Ideal.map_map _ _).symm

variable {f₂₃ f₁₂} in
theorem _root_.GradedAlgHom.comp_admissible (h₁₂ : 𝒜₂₊ ≤ 𝒜₁₊.map f₁₂) (h₂₃ : 𝒜₃₊ ≤ 𝒜₂₊.map f₂₃) :
    𝒜₃₊ ≤ 𝒜₁₊.map (f₂₃.comp f₁₂) :=
  h₂₃.trans <| by rw [map_comp]; exact Ideal.map_mono h₁₂

theorem _root_.GradedAlgHom.id_admissible :
    𝒜₁₊ ≤ 𝒜₁₊.map (GradedAlgHom.id : 𝒜₁ →ᵍᵃ 𝒜₁) :=
  le_of_eq <| HomogeneousIdeal.ext (Ideal.map_id _).symm

theorem map_comp (h₁₂) (h₂₃) :
    map (f₂₃.comp f₁₂) (GradedAlgHom.comp_admissible h₁₂ h₂₃) = map f₂₃ h₂₃ ≫ map f₁₂ h₁₂ := by
  refine (mapAffineOpenCover _ (GradedAlgHom.comp_admissible h₁₂ h₂₃)).openCover.hom_ext _ _
    fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_X, Scheme.AffineOpenCover.openCover_f,
    mapAffineOpenCover_f]
  rw [awayι_comp_map _ _ _ _ s.2.2]
  simp only [GradedAlgHom.comp_apply]
  rw [awayι_comp_map_assoc _ _ _ _ (f₁₂.map_mem s.2.2), awayι_comp_map _ _ _ _ s.2.2,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  ext x
  obtain ⟨n, a, ha, rfl⟩ := x.mk_surjective _ s.2.2
  simp

theorem map_id : map .id GradedAlgHom.id_admissible = 𝟙 (Proj 𝒜₁) := by
  refine (affineOpenCover _).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [affineOpenCover, openCoverOfISupEqTop, Scheme.AffineOpenCover.openCover_X,
    Scheme.AffineOpenCover.openCover_f, Category.comp_id]
  conv_lhs => exact awayι_comp_map .id _ _ _ s.2.2
  generalize_proofs h₁ h₂ h₃
  have : HomogeneousLocalization.Away.map GradedAlgHom.id h₁ = RingHom.id _ := by
    ext x
    obtain ⟨n, a, ha, rfl⟩ := x.mk_surjective _ h₂
    simp
  rw [this, CommRingCat.ofHom_id, Spec.map_id]
  exact Category.id_comp _

@[simps] protected noncomputable def congr (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) : Proj 𝒜₁ ≅ Proj 𝒜₂ where
  hom := Proj.map _ e.symm.admissible
  inv := Proj.map _ e.admissible
  hom_inv_id := by
    rw [← map_comp]
    generalize_proofs
    generalize he : e.symm.toGradedAlgHom.comp e.toGradedAlgHom = e' at *
    rw [← GradedAlgEquiv.trans_toGradedAlgHom, e.self_trans_symm,
      GradedAlgEquiv.refl_toGradedAlgHom] at he
    subst he
    rw [map_id]
  inv_hom_id := by
    rw [← map_comp]
    generalize_proofs
    generalize he : e.toGradedAlgHom.comp e.symm.toGradedAlgHom = e' at *
    rw [← GradedAlgEquiv.trans_toGradedAlgHom, e.symm_trans_self,
      GradedAlgEquiv.refl_toGradedAlgHom] at he
    subst he
    rw [map_id]

end AlgebraicGeometry.Proj
