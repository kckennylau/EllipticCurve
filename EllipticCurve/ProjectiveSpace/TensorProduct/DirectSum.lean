/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.LinearAlgebra.DirectSum.TensorProduct

-- #30322

section Lemmas

variable {R : Type*} [Semiring R]
variable {ι : Type*}
variable {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

namespace DirectSum

@[simp] lemma id_symm_apply {M : Type*} {ι : Type*} [AddCommMonoid M] [Unique ι] (x : M) :
    (DirectSum.id M ι).symm x = of _ default x :=
  rfl

@[simp] lemma id_apply {M : Type*} {ι : Type*} [AddCommMonoid M] [Unique ι] (x : ⨁ _ : ι, M) :
    DirectSum.id M ι x = x default := by
  rw [← AddEquiv.eq_symm_apply, id_symm_apply, eq_comm]
  induction x using DirectSum.induction_on <;> simp [Unique.eq_default, *]

@[simp] lemma lid_apply {M : Type*} {ι : Type*} [AddCommMonoid M] [Module R M] [Unique ι]
    (x : ⨁ _ : ι, M) : DirectSum.lid R M ι x = x default :=
  DirectSum.id_apply x

@[simp] lemma lid_symm_apply {M : Type*} {ι : Type*} [AddCommMonoid M] [Module R M] [Unique ι]
    (x : M) : (DirectSum.lid R M ι).symm x = lof R _ _ default x :=
  DirectSum.id_symm_apply x

variable {κ : Type*}

-- We need to try very hard to avoid dependent type "issues".
lemma lequivCongrLeft_lof [DecidableEq ι] [DecidableEq κ] {e : ι ≃ κ}
    {i : ι} {k : κ} (hik : i = e.symm k)
    (x : M i) (y : M (e.symm k)) (hxy : cast congr(M $hik) x = y) :
    lequivCongrLeft R e (lof R ι M i x) = lof R _ _ k y := by
  subst hik hxy
  ext j
  simp_rw [lequivCongrLeft_apply, lof_eq_of, of_apply]
  by_cases eq : k = j
  · subst eq
    rw [dif_pos rfl, dif_pos rfl]
    rfl
  · rw [dif_neg (by aesop), dif_neg eq]

lemma lequivCongrLeft_symm_lof [DecidableEq ι] [DecidableEq κ] {h : ι ≃ κ}
    {k : κ} {x : M (h.symm k)} :
    (lequivCongrLeft R h).symm (lof R κ (fun k => M (h.symm k)) k x) = lof R ι M (h.symm k) x := by
  rw [LinearEquiv.symm_apply_eq]
  symm
  exact lequivCongrLeft_lof rfl _ _ rfl

variable {R : Type*} [Semiring R]
variable {ι : Type*} [dec_ι : DecidableEq ι]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable (A : ι → Submodule R M)

@[simp] lemma coeLinearMap_lof (i : ι) (x : A i) :
    DirectSum.coeLinearMap A (lof R ι (fun i ↦ A i) i x) = x :=
  coeLinearMap_of A i x

end DirectSum

end Lemmas


section Ring

namespace TensorProduct

open TensorProduct

open DirectSum

open LinearMap

attribute [local ext] TensorProduct.ext

variable (R : Type*) [CommSemiring R] (S) [Semiring S] [Algebra R S]
variable {ι₁ : Type*} {ι₂ : Type*}
variable [DecidableEq ι₁] [DecidableEq ι₂]
variable (M₁ : ι₁ → Type*) (M₁' : Type*) (M₂ : ι₂ → Type*) (M₂' : Type*)
variable [∀ i₁, AddCommMonoid (M₁ i₁)] [AddCommMonoid M₁']
variable [∀ i₂, AddCommMonoid (M₂ i₂)] [AddCommMonoid M₂']
variable [∀ i₁, Module R (M₁ i₁)] [Module R M₁'] [∀ i₂, Module R (M₂ i₂)] [Module R M₂']
variable [∀ i₁, Module S (M₁ i₁)] [∀ i₁, IsScalarTower R S (M₁ i₁)]
variable [Module S M₁'] [IsScalarTower R S M₁']

-- TO REPLACE
/-- Tensor products distribute over a direct sum on the left . -/
def directSumLeft' : (⨁ i₁, M₁ i₁) ⊗[R] M₂' ≃ₗ[S] ⨁ i, M₁ i ⊗[R] M₂' :=
  TensorProduct.AlgebraTensorModule.congr 1 (DirectSum.lid _ _).symm ≪≫ₗ
  TensorProduct.directSum R S M₁ (fun _ : Unit ↦ M₂') ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.prodUnique _ _)

-- TO REPLACE
/-- Tensor products distribute over a direct sum on the right. -/
def directSumRight' : (M₁' ⊗[R] ⨁ i, M₂ i) ≃ₗ[S] ⨁ i, M₁' ⊗[R] M₂ i :=
  TensorProduct.AlgebraTensorModule.congr (DirectSum.lid _ _).symm 1 ≪≫ₗ
  TensorProduct.directSum R S (fun _ : Unit ↦ M₁') M₂ ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.uniqueProd _ _)

variable {M₁ M₁' M₂ M₂'}

@[simp]
theorem directSumLeft_tmul_lof' (i : ι₁) (x : M₁ i) (y : M₂') :
    directSumLeft' R S M₁ M₂' (DirectSum.lof S _ _ i x ⊗ₜ[R] y) =
    DirectSum.lof S _ _ i (x ⊗ₜ[R] y) := by
  simpa [directSumLeft'] using lequivCongrLeft_lof (by simp) _ _ rfl

@[simp]
theorem directSumLeft_tmul_of' (i : ι₁) (x : M₁ i) (y : M₂') :
    directSumLeft' R S M₁ M₂' (DirectSum.of _ i x ⊗ₜ[R] y) =
    DirectSum.lof S _ _ i (x ⊗ₜ[R] y) :=
  directSumLeft_tmul_lof' ..

@[simp]
theorem directSumLeft_symm_lof_tmul' (i : ι₁) (x : M₁ i) (y : M₂') :
    (directSumLeft' R S M₁ M₂').symm (DirectSum.lof S _ _ i (x ⊗ₜ[R] y)) =
      DirectSum.lof S _ _ i x ⊗ₜ[R] y := by
  rw [LinearEquiv.symm_apply_eq, directSumLeft_tmul_lof']

@[simp]
theorem directSumLeft_symm_of_tmul' (i : ι₁) (x : M₁ i) (y : M₂') :
    (directSumLeft' R S M₁ M₂').symm (DirectSum.of _ i (x ⊗ₜ[R] y)) =
      DirectSum.lof S _ _ i x ⊗ₜ[R] y :=
  directSumLeft_symm_lof_tmul' ..

@[simp]
theorem directSumRight_tmul_lof' (x : M₁') (i : ι₂) (y : M₂ i) :
    directSumRight' R S M₁' M₂ (x ⊗ₜ[R] DirectSum.lof R _ _ i y) =
    DirectSum.lof S _ _ i (x ⊗ₜ[R] y) := by
  simpa [directSumRight'] using lequivCongrLeft_lof (by simp) _ _ rfl

@[simp]
theorem directSumRight_tmul_of' (x : M₁') (i : ι₂) (y : M₂ i) :
    directSumRight' R S M₁' M₂ (x ⊗ₜ[R] DirectSum.of _ i y) =
    DirectSum.lof S _ _ i (x ⊗ₜ[R] y) :=
  directSumRight_tmul_lof' ..

@[simp]
theorem directSumRight_symm_lof_tmul' (x : M₁') (i : ι₂) (y : M₂ i) :
    (directSumRight' R S M₁' M₂).symm (DirectSum.lof S _ _ i (x ⊗ₜ[R] y)) =
      x ⊗ₜ[R] DirectSum.lof R _ _ i y := by
  rw [LinearEquiv.symm_apply_eq, directSumRight_tmul_lof']

@[simp]
theorem directSumRight_symm_of_tmul' (x : M₁') (i : ι₂) (y : M₂ i) :
    (directSumRight' R S M₁' M₂).symm (DirectSum.of _ i (x ⊗ₜ[R] y)) =
      x ⊗ₜ[R] DirectSum.lof R _ _ i y :=
  directSumRight_symm_lof_tmul' ..

lemma directSumRight_comp_rTensor' (f : M₁' →ₗ[R] M₂') :
    (directSumRight' R R M₂' M₁).toLinearMap ∘ₗ f.rTensor _ =
      (lmap fun _ ↦ f.rTensor _) ∘ₗ directSumRight' R R M₁' M₁ := by
  ext; simp

end TensorProduct

end Ring
