/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import EllipticCurve.ProjectiveSpace.Graded.Admissible
import EllipticCurve.ProjectiveSpace.TensorProduct.GradedAlgebra

/-! # The map to tensor product is admissible -/

variable {ι R A : Type*} [CommSemiring R]
  [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
  [Semiring A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
  (S : Type*) [CommSemiring S] [Algebra R S]

open TensorProduct

theorem GradedRingHom.Admissible.includeRight :
    Admissible (GradedAlgebra.includeRight 𝒜 S) := .mk <| by
  refine (HomogeneousIdeal.irrelevant_le _).mpr fun i hi x hx ↦ ?_
  obtain ⟨a, ha⟩ := Submodule.toBaseChange_surjective _ _ ⟨x, hx⟩
  replace ha := congr(($ha).val); subst ha
  simp only [HomogeneousIdeal.toIdeal_map, HomogeneousIdeal.toIdeal_irrelevant,
    Submodule.mem_toAddSubmonoid]
  induction a with
  | zero => simp
  | add => simp [*, add_mem]
  | tmul s a =>
    rw [Submodule.toBaseChange_apply_tmul_coe, tmul_eq_smul_one_tmul,
      ← algebraMap_smul (S ⊗[R] A), smul_eq_mul]
    exact Ideal.mul_mem_left _ _ <| Ideal.mem_map_of_mem _ <|
      HomogeneousIdeal.mem_irrelevant_of_mem _ hi a.2
