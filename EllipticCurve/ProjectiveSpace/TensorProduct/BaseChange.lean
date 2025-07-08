/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.Lemmas
import EllipticCurve.ProjectiveSpace.TensorProduct.SymmetricMap
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base Change for Symmetric Multilinear Maps

In this file we contruct the base change for symmetric multilinear maps.

## Main definitions

* `SymmetricMap.baseChange`: the base change of a symmetric multilinear map `M [Σ^ι]→ₗ[R] N` to
  `(A ⊗[R] M) [Σ^ι]→ₗ[A] (A ⊗[R] N)`.

-/

open TensorProduct Function Equiv Perm

variable {R M N ι A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Restrict a multilinear map on `Fin (n + 1)` to a multilinear map on `Fin n` along a chosen
`p : M₁ (Fin.last n)`. -/
def MultilinearMap.restrictFin {n : ℕ} {M₁ : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
    (f : MultilinearMap R M₁ N) (p : M₁ (Fin.last n)) :
      MultilinearMap R (fun i : Fin n ↦ M₁ i.castSucc) N where
  toFun w := f (Fin.lastCases p w)
  map_update_add' w i x y := by simp
  map_update_smul' w i x y := by simp

/-- `restrictFin` as linear map. -/
def MultilinearMap.restrictFinₗ {n : ℕ} {M₁ : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)] (f : MultilinearMap R M₁ N) :
      M₁ (Fin.last n) →ₗ[R] MultilinearMap R (fun i : Fin n ↦ M₁ i.castSucc) N where
  toFun p := f.restrictFin p
  map_add' x y := ext fun v ↦ by simp [restrictFin, Fin.lastCases_update_left x 0,
    Fin.lastCases_update_left y 0, Fin.lastCases_update_left (x + y) 0]
  map_smul' r x := ext fun v ↦ by simp [restrictFin, Fin.lastCases_update_left x 0,
    Fin.lastCases_update_left (r • x) 0]

/-- The induction step. -/
noncomputable def MultilinearMap.baseChangeFinAux {n : ℕ} {M₁ : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
    (ih : MultilinearMap R (fun i : Fin n ↦ M₁ i.castSucc) N →ₗ[R]
      MultilinearMap A (fun i : Fin n ↦ A ⊗[R] M₁ i.castSucc) (A ⊗[R] N))
    (f : MultilinearMap R M₁ N) (v : (i : Fin n) → A ⊗[R] M₁ i.castSucc) :
      M₁ (Fin.last n) →ₗ[R] (A ⊗[R] N) where
  toFun p := ih (f.restrictFinₗ p) v
  map_add' x y := by simp
  map_smul' r x := by simp

noncomputable def MultilinearMap.baseChangeFin : ∀ (n : ℕ) (M₁ : Fin n → Type*)
    [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)],
    MultilinearMap R M₁ N →ₗ[R] MultilinearMap A (fun i ↦ A ⊗[R] M₁ i) (A ⊗[R] N)
  | 0 => fun _ _ _ ↦
    { toFun f := MultilinearMap.constOfIsEmpty A _ (1 ⊗ₜ f default)
      map_add' _ _ := ext fun v ↦ by simp [tmul_add]
      map_smul' _ _ := ext fun v ↦ by simp }
  | (n+1) => fun M₁ _ _ ↦ by
    refine
    { toFun f :=
      { toFun v := LinearMap.liftBaseChangeEquiv A
          (baseChangeFinAux (baseChangeFin n fun i ↦ M₁ i.castSucc) f fun i ↦ v i.castSucc)
          (v (Fin.last n))
        map_update_add' v i := ?_
        map_update_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
    · refine i.lastCases (by simp) fun i x y ↦ ?_
      have := @Fin.lastCases_update_right_symm
      conv => enter [1,1,2,3]; exact funext (fun i : Fin n ↦
        Fin.lastCases_update_right_symm _ _ _ _ i.castSucc)
/-
-- todo: need to rewrite the "right_symm" one
fun i_1 ↦ update v i.castSucc (x + y) i_1.castSucc
update (fun i ↦ Fin.lastCases p v i) i.castSucc x j = Fin.lastCases p (update v i x) j
-/
def baseChange {R M N ι : Type*} (A : Type*) [CommSemiring R] [Ring A] [Algebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M [Σ^ι]→ₗ[R] N) : (A ⊗[R] M) [Σ^ι]→ₗ[A] (A ⊗[R] N) where
  toFun v := _
