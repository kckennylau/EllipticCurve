/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.LinearAlgebra.TensorProduct.Tower

-- #30322

variable {R A M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  [Semiring A] [Algebra R A]

open TensorProduct

@[simp] lemma _root_.LinearEquiv.baseChange_tmul {e : M ≃ₗ[R] N} (a : A) (m : M) :
    (e.baseChange R A) (a ⊗ₜ m) = a ⊗ₜ e m :=
  rfl

@[simp] lemma _root_.LinearEquiv.baseChange_symm_tmul {e : M ≃ₗ[R] N} (a : A) (n : N) :
    (e.baseChange R A).symm (a ⊗ₜ n) = a ⊗ₜ e.symm n :=
  rfl

namespace Submodule

variable (p : Submodule R M) (A)

/-- Given an `R`-submodule `p` of `M`, and `R`-algebra `A`, we obtain an `A`-submodule of
`A ⊗[R] M` by `p.baseChange A`. This is then the surjective `A`-linear map
`A ⊗[R] M → p.baseChange A`. -/
def toBaseChange : A ⊗[R] p →ₗ[A] p.baseChange A :=
  LinearMap.rangeRestrict _

@[simp] lemma toBaseChange_apply_tmul_coe (a : A) (x : p) :
    (p.toBaseChange A (a ⊗ₜ x) : A ⊗[R] M) = a ⊗ₜ (x : M) := rfl

lemma toBaseChange_surjective : Function.Surjective (p.toBaseChange A) :=
  LinearMap.surjective_rangeRestrict _

/-- This version enables better pattern matching via the tactic `obtain`. -/
lemma toBaseChange_surjective' {y : A ⊗[R] M} (hy : y ∈ p.baseChange A) :
    ∃ x : A ⊗[R] p, p.toBaseChange A x = y := by
  obtain ⟨x, hx⟩ := toBaseChange_surjective A p ⟨y, hy⟩
  exact ⟨x, congr($hx)⟩

end Submodule
