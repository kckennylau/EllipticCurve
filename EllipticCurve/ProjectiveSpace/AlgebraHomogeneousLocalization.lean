/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! # Algebra Structure on Homogeneous Localization

In this file we show that if `A` is a graded `R`-algebra then `HomogeneousLocalization 𝒜 S` is
an `R`-algebra.
-/

variable {ι R₀ R A : Type*}

section Semiring

variable [CommSemiring R₀] [CommSemiring R] [Semiring A]
  [Algebra R₀ R] [Algebra R A] [Algebra R₀ A] [IsScalarTower R₀ R A]
  [DecidableEq ι] [AddMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

instance : Algebra R₀ (𝒜 0) where
  algebraMap := (algebraMap R (𝒜 0)).comp (algebraMap R₀ R)
  commutes' r x := Algebra.commutes' (algebraMap R₀ R r) x
  smul_def' r x := Subtype.ext <| by
    rw [← IsScalarTower.algebraMap_smul R, Algebra.smul_def]
    rfl

@[simp] lemma algebraMap_to_zero (r : R₀) : (algebraMap R₀ (𝒜 0) r : A) = algebraMap R₀ A r :=
  (IsScalarTower.algebraMap_apply R₀ R A r).symm

end Semiring

section Ring

namespace HomogeneousLocalization

variable [CommRing R₀] [CommRing R] [CommRing A]
  [Algebra R₀ R] [Algebra R A] [Algebra R₀ A] [IsScalarTower R₀ R A]
  [DecidableEq ι] [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
  (S : Submonoid A)

@[simp]
lemma val_fromZeroRingHom (r : R) :
    (fromZeroRingHom 𝒜 S (algebraMap _ _ r)).val = algebraMap _ _ r :=
  rfl

instance : Algebra R₀ (HomogeneousLocalization 𝒜 S) where
  algebraMap := (fromZeroRingHom 𝒜 S).comp (algebraMap R₀ (𝒜 0))
  commutes' r x := mul_comm ..
  smul_def' r x := by ext; rw [val_smul, val_mul, Algebra.smul_def, RingHom.comp_apply,
    IsScalarTower.algebraMap_apply R₀ R (𝒜 0), val_fromZeroRingHom,
    ← IsScalarTower.algebraMap_apply]

instance : IsScalarTower R₀ (𝒜 0) (HomogeneousLocalization 𝒜 S) :=
  .of_algebraMap_eq' rfl

instance : IsScalarTower R₀ R (HomogeneousLocalization 𝒜 S) :=
  .of_algebraMap_eq' rfl

instance : IsScalarTower R (𝒜 0) (Localization S) :=
  .of_algebraMap_eq' rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    IsScalarTower R (HomogeneousLocalization 𝒜 S) (Localization S) :=
  .of_algebraMap_eq' rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    IsScalarTower (𝒜 0) (HomogeneousLocalization 𝒜 S) (Localization S) :=
  .of_algebraMap_eq' rfl

@[simp] lemma algebraMap_eq' :
    algebraMap R₀ (HomogeneousLocalization 𝒜 S) = (fromZeroRingHom 𝒜 S).comp (algebraMap _ _) := rfl

theorem algebraMap_apply' {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) (f : R) :
    algebraMap R (HomogeneousLocalization 𝒜 S) f = mk ⟨0, algebraMap _ _ f, 1, one_mem _⟩ := rfl

theorem val_sum {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {𝒜 : ι → Submodule R A}
      {x : Submonoid A} [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜]
      {σ : Type*} {S : Finset σ} {f : σ → HomogeneousLocalization 𝒜 x} :
    (∑ s ∈ S, f s).val = ∑ s ∈ S, (f s).val :=
  map_sum (algebraMap (HomogeneousLocalization 𝒜 x) _) _ _

theorem val_prod {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {𝒜 : ι → Submodule R A}
      {x : Submonoid A} [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜]
      {σ : Type*} {S : Finset σ} {f : σ → HomogeneousLocalization 𝒜 x} :
    (∏ s ∈ S, f s).val = ∏ s ∈ S, (f s).val :=
  map_prod (algebraMap (HomogeneousLocalization 𝒜 x) _) _ _

namespace Away

theorem mk_smul {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] {f d hf n x} (hx) {r : R} :
    r • Away.mk 𝒜 (f:=f) hf (d:=d) n x hx = .mk 𝒜 hf n (r • x) (Submodule.smul_mem _ _ hx) := rfl

theorem algebraMap_apply {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f : A) (d hf) (r : R) :
    algebraMap R (Away 𝒜 f) r = .mk 𝒜 (d:=d) hf 0 (algebraMap R A r)
      (by rw [zero_nsmul]; exact SetLike.algebraMap_mem_graded ..) := by
  ext; simp [fromZeroRingHom]

/-- If `f = g`, then `Away 𝒜 f ≅ Away 𝒜 g`. -/
@[simps! apply] noncomputable
def congr {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f g : A)
      {d : ι} (hf : f ∈ 𝒜 d) (h : f = g) :
    Away 𝒜 f ≃ₐ[R] Away 𝒜 g := by
  refine .ofRingEquiv (f := .ofRingHom (awayMap 𝒜 (SetLike.one_mem_graded ..) (by simp [h]))
    (awayMap 𝒜 (SetLike.one_mem_graded ..) (by simp [h]))
    (RingHom.ext fun x ↦ ?_) (RingHom.ext fun x ↦ ?_)) (fun x ↦ ?_)
  · subst h; rcases Away.mk_surjective 𝒜 hf x with ⟨n, a, ha, rfl⟩; simp
  · subst h; rcases Away.mk_surjective 𝒜 hf x with ⟨n, a, ha, rfl⟩; simp
  · subst h; ext; simp [awayMap_fromZeroRingHom]

lemma congr_mk {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f g : A)
      {d : ι} (hf : f ∈ 𝒜 d) (h : f = g) (n x hx) :
    congr 𝒜 f g hf h (.mk 𝒜 hf n x hx) = .mk 𝒜 (by rwa [← h]) n x hx := by
  simp_rw [congr_apply, awayMap_mk, one_pow, mul_one, add_zero]

@[simp] lemma congr_symm {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f g : A)
      {d : ι} (hf : f ∈ 𝒜 d) (h : f = g) :
    (congr 𝒜 f g hf h).symm = congr 𝒜 g f (by rwa [← h]) h.symm :=
  rfl

end Away

end HomogeneousLocalization

end Ring
