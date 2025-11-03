/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import EllipticCurve.ProjectiveSpace.TensorProduct.DirectSum
import EllipticCurve.ProjectiveSpace.TensorProduct.Submodule
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-! # Decomposition of tensor product
In this file we show that if `ℳ` is a graded `R`-module, and `S` is any `R`-algebra, then
`S ⊗[R] ℳ` (which is actually `fun i ↦ (ℳ i).baseChange S`) is a graded `S`-module with the same
grading.
-/

open TensorProduct LinearMap

section Lemmas

namespace DirectSum

variable {ι R M σ : Type*}
variable [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]
variable (ℳ : ι → Submodule R M)
variable [Decomposition ℳ]

@[simp] lemma decompose_symm_lof (i : ι) (x : ℳ i) :
    (decompose ℳ).symm (lof R _ _ i x) = x :=
  congr($(decomposeLinearEquiv_symm_comp_lof ℳ i) x)

@[simp] lemma decompose_apply_coe (i : ι) (x : ℳ i) :
    decompose ℳ x = lof R _ _ i x :=
  (Equiv.eq_symm_apply _).mp (decompose_symm_lof ..).symm

end DirectSum

end Lemmas


namespace DirectSum

variable {ι R M S : Type*} [DecidableEq ι]
  [CommSemiring R] [AddCommMonoid M] [Module R M]
  (ℳ : ι → Submodule R M) [Decomposition ℳ]
  [CommSemiring S] [Algebra R S]

instance Decomposition.baseChange : Decomposition fun i ↦ (ℳ i).baseChange S :=
  .ofLinearMap _ (lmap (ℳ ·|>.toBaseChange S) ∘ₗ
    (directSumRight' R S S fun i ↦ ℳ i).toLinearMap ∘ₗ
    ((decomposeLinearEquiv ℳ).baseChange R S)) pf1 pf2 where
  pf1 := by
    simp_rw [← comp_assoc]
    rw [← LinearEquiv.eq_comp_toLinearMap_symm]
    ext
    simp
  pf2 := by
    ext : 1
    rw [← LinearMap.cancel_right ((ℳ _).toBaseChange_surjective S)]
    ext : 3
    simp

theorem toBaseChange_injective (i : ι) : Function.Injective ((ℳ i).toBaseChange S) := fun x y h ↦ by
  have := (Function.Bijective.of_comp_iff (lmap (ℳ ·|>.toBaseChange S))
    (by rw [← LinearEquiv.coe_trans]; exact LinearEquiv.bijective _)).1
    (decompose (M := S ⊗[R] M) fun i ↦ (ℳ i).baseChange S).bijective
  refine of_injective (β := fun i ↦ S ⊗[R] ℳ i) i <| this.injective ?_
  simpa using congr(of (fun i ↦ (ℳ i).baseChange S) i $h)

theorem toBaseChange_bijective (i : ι) : Function.Bijective ((ℳ i).toBaseChange S) :=
  ⟨toBaseChange_injective ℳ i, (ℳ i).toBaseChange_surjective S⟩

namespace IsInternal

omit [Decomposition ℳ]

theorem baseChange (hm : IsInternal ℳ) : IsInternal fun i ↦ (ℳ i).baseChange S :=
  haveI := hm.chooseDecomposition
  Decomposition.isInternal _

nonrec theorem toBaseChange_bijective (hm : IsInternal ℳ) (i : ι) :
    Function.Bijective ((ℳ i).toBaseChange S) :=
  haveI := hm.chooseDecomposition
  toBaseChange_bijective ℳ i

theorem toBaseChange_injective (hm : IsInternal ℳ) (i : ι) :
    Function.Injective ((ℳ i).toBaseChange S) :=
  (toBaseChange_bijective ℳ hm i).injective

end IsInternal

end DirectSum
