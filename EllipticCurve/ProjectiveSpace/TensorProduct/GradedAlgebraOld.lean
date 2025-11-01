/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

-- import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Tensor Product of Graded Algebra

In this file we show that if `A` is a graded `R`-algebra then `S ⊗[R] A` is a graded `S`-algebra.
-/

universe u v w

open DirectSum TensorProduct

@[simps!] def DirectSum.baseChangeLEquiv {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (S : Type*) [Semiring S] [Algebra R S] :
    S ⊗[R] (⨁ i, M i) ≃ₗ[S] ⨁ i, S ⊗[R] M i where
  __ := directSumRight R S M
  map_smul' s x := by
    change directSumRight R S M (s • x) = s • directSumRight R S M x
    induction x with
    | zero => simp only [smul_zero, map_zero]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul s₂ m => induction m using DirectSum.induction_on with
      | zero => simp only [tmul_zero, smul_zero, map_zero]
      | add m₁ m₂ hm₁ hm₂ => simp only [tmul_add, smul_add, map_add, hm₁, hm₂]
      | of i m => rw [← lof_eq_of R, smul_tmul', directSumRight_tmul_lof, directSumRight_tmul_lof,
          lof_eq_of, lof_eq_of, ← of_smul, smul_tmul']

theorem TensorProduct.congr_cast {R : Type*} [CommSemiring R] {ι : Type*}
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    {S : Type*} [AddCommMonoid S] [Module R S]
    {i j : ι} (h : i = j) :
    congr (.refl R S) (.cast h) = .cast (M := fun i ↦ S ⊗[R] M i) h := by
  subst h
  exact LinearEquiv.toLinearMap_injective <| ext' fun x y ↦ by simp

namespace GradedMonoid

theorem extₗ (R : Type*) [CommSemiring R] {ι : Type*}
    {A : ι → Type*} [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    {x y : GradedMonoid fun i ↦ A i}
    (h₁ : x.fst = y.fst) (h₂ : LinearEquiv.cast (R := R) h₁ x.snd = y.snd) : x = y := by
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  dsimp only at h₁; subst h₁
  dsimp only at h₂; subst h₂
  rfl

@[simp] lemma gone {ι : Type*} [Zero ι] {A : ι → Type*} [GOne A] :
    GOne.one (A := A) = 1 :=
  rfl

@[simp] lemma one_gmul {ι : Type*} [AddMonoid ι]
    {A : ι → Type*} [GMonoid A] {i : ι} (x : A i) :
    GMul.mul (1 : A 0) x = cast (by rw [zero_add]) x :=
  eq_cast_iff_heq.mpr (Sigma.ext_iff.mp (GMonoid.one_mul ⟨_, x⟩)).2

@[simp] lemma gmul_one {ι : Type*} [AddMonoid ι]
    {A : ι → Type*} [GMonoid A] {i : ι} (x : A i) :
    GMul.mul x (1 : A 0) = cast (by rw [add_zero]) x :=
  eq_cast_iff_heq.mpr (Sigma.ext_iff.mp (GMonoid.mul_one ⟨_, x⟩)).2

@[simp] lemma gmul_assoc {ι : Type*} [AddMonoid ι]
    {A : ι → Type*} [GMonoid A] {i j k : ι} (x : A i) (y : A j) (z : A k) :
    GMul.mul (GMul.mul x y) z = cast (by rw [add_assoc]) (GMul.mul x (GMul.mul y z)) :=
  eq_cast_iff_heq.mpr (Sigma.ext_iff.mp (GMonoid.mul_assoc ⟨_, x⟩ ⟨_, y⟩ ⟨_, z⟩)).2

lemma gmul_comm {ι : Type*} [AddCommMonoid ι]
    {A : ι → Type*} [GCommMonoid A] {i j : ι} (x : A i) (y : A j) :
    GMul.mul x y = cast (by rw [add_comm]) (GMul.mul y x) :=
  eq_cast_iff_heq.mpr (Sigma.ext_iff.mp (GCommMonoid.mul_comm ⟨_, x⟩ ⟨_, y⟩)).2

instance GOne.tensorProduct {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddMonoid ι]
    (A : ι → Type*) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GSemiring A]
    (S : Type*) [AddCommMonoidWithOne S] [Module R S] :
    GOne fun i ↦ S ⊗[R] A i where
  one := 1

instance GMonoid.tensorProduct {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddMonoid ι]
    (A : ι → Type*) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GSemiring A] [GAlgebra R A]
    (S : Type*) [Semiring S] [Algebra R S] :
    GMonoid fun i ↦ S ⊗[R] A i where
  __ := GOne.tensorProduct A S
  mul x y := map₂ (LinearMap.mul R S) (gMulLHom R A) x y
  one_mul x := by
    refine extₗ R (by simp) ?_
    simp only [fst_mul, fst_one, snd_mul, snd_one, gone, Algebra.TensorProduct.one_def,
      map₂_apply_tmul]
    rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply]
    nth_rw 2 [← LinearMap.id_apply (R := R) x.snd]
    congr 1
    exact ext' (by simp_rw [← congr_cast]; simp)
  mul_one x := by
    refine extₗ R (by simp) ?_
    simp only [fst_mul, fst_one, snd_mul, snd_one, gone, Algebra.TensorProduct.one_def]
    rw [← LinearMap.flip_apply, ← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply]
    nth_rw 2 [← LinearMap.id_apply (R := R) x.snd]
    congr 1
    exact ext' (by simp_rw [← congr_cast]; simp)
  mul_assoc x y z := by
    refine extₗ R (by simp [add_assoc]) ?_
    simp only [fst_mul, snd_mul]
    induction x.snd using TensorProduct.induction_on with
    | zero => simp [-LinearEquiv.cast_apply]
    | add x₁ x₂ hx₁ hx₂ => simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
    | tmul s₁ a =>
      induction y.snd using TensorProduct.induction_on with
      | zero => simp [-LinearEquiv.cast_apply]
      | add y₁ y₂ hy₁ hy₂ => simp only [map_add, LinearMap.add_apply, hy₁, hy₂]
      | tmul s₂ b =>
        induction z.snd using TensorProduct.induction_on with
        | zero => simp [-LinearEquiv.cast_apply]
        | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
        | tmul s₃ c => rw [← congr_cast]; simp [_root_.mul_assoc]
  gnpow_zero' x := extₗ R (by simp) (by simp [GradedMonoid.mk, gnpowRec])
  gnpow_succ' n x := extₗ R (by simp) (by simp [GradedMonoid.mk, gnpowRec])

@[simp] lemma gmul_tensor_product {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddMonoid ι]
    (A : ι → Type*) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GSemiring A] [GAlgebra R A]
    (S : Type*) [Semiring S] [Algebra R S]
    {i j : ι} (x : S ⊗[R] A i) (y : S ⊗[R] A j) :
    GMul.mul (A := fun i ↦ S ⊗[R] A i) x y = map₂ (LinearMap.mul R S) (gMulLHom R A) x y :=
  rfl

instance GCommMonoid.tensorProduct {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    (A : ι → Type*) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GCommSemiring A] [GAlgebra R A]
    (S : Type*) [CommSemiring S] [Algebra R S] :
    GCommMonoid fun i ↦ S ⊗[R] A i where
  __ := GMonoid.tensorProduct A S
  mul_comm x y := by
    refine extₗ R (by simp [add_comm]) ?_
    simp only [fst_mul, snd_mul, gmul_tensor_product]
    induction x.snd using TensorProduct.induction_on with
    | zero => simp [-LinearEquiv.cast_apply]
    | add x₁ x₂ hx₁ hx₂ => simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
    | tmul s₁ a =>
      induction y.snd using TensorProduct.induction_on with
      | zero => simp [-LinearEquiv.cast_apply]
      | add y₁ y₂ hy₁ hy₂ => simp only [map_add, LinearMap.add_apply, hy₁, hy₂]
      | tmul s₂ b => rw [← congr_cast]; simp [gmul_comm a, _root_.mul_comm s₁]

end GradedMonoid

namespace DirectSum

instance GCommSemiring.tensorProduct {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    (A : ι → Type*) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GCommSemiring A] [GAlgebra R A]
    (S : Type*) [CommSemiring S] [Algebra R S] :
    GCommSemiring fun i ↦ S ⊗[R] A i where
  __ := GradedMonoid.GCommMonoid.tensorProduct A S
  natCast n := n
  natCast_zero := by simp
  natCast_succ n := by simp
  mul_zero := by simp
  zero_mul := by simp
  mul_add := by simp
  add_mul := by simp

instance GAlgebra.tensorProduct {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    (A : ι → Type*) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GCommSemiring A] [GAlgebra R A]
    (S : Type*) [CommSemiring S] [Algebra R S] :
    GAlgebra S fun i ↦ S ⊗[R] A i where
  toFun := (TensorProduct.mk R S (A 0)).flip 1
  map_one := rfl
  map_mul x y := GradedMonoid.extₗ R (by simp [GradedMonoid.mk])
    (by rw [← congr_cast]; simp [GradedMonoid.mk])
  commutes s x := by
    refine GradedMonoid.extₗ R (by simp [GradedMonoid.mk]) ?_
    simp_rw [← congr_cast, GradedMonoid.snd_mul, GradedMonoid.gmul_tensor_product, GradedMonoid.mk,
      GradedMonoid.fst_mul]
    rw [← LinearMap.flip_apply (m := x.snd), ← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply]
    congr 1
    ext; simp [_root_.mul_comm]
  smul_def s x := by
    refine GradedMonoid.extₗ R (by simp [GradedMonoid.mk]) ?_
    simp only [AddMonoidHom.coe_coe, LinearMap.flip_apply, mk_apply, GradedMonoid.fst_mul,
      GradedMonoid.fst_smul, GradedMonoid.snd_smul, GradedMonoid.snd_mul,
      GradedMonoid.gmul_tensor_product, GradedMonoid.mk]
    induction x.snd using TensorProduct.induction_on with
    | zero => simp [-LinearEquiv.cast_apply]
    | add x₁ x₂ hx₁ hx₂ => simp only [smul_add, map_add, hx₁, hx₂]
    | tmul r a => rw [← congr_cast]; simp [smul_tmul']

end DirectSum

def DirectSum.baseChangeAlgEquiv {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A : ι → Type*} [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GCommSemiring A] [GAlgebra R A]
    {S : Type*} [CommSemiring S] [Algebra R S] :
    S ⊗[R] DirectSum ι A ≃ₐ[S] ⨁ i, S ⊗[R] A i where
  __ := directSumRight R S A
  map_mul' x y := by
    dsimp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x₁ x₂ hx₁ hx₂ => simp only [add_mul, map_add, hx₁, hx₂]
    | tmul s₁ a₁ =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ hy₁ hy₂ => simp only [mul_add, map_add, hy₁, hy₂]
      | tmul s₂ a₂ =>
        induction a₁ using DirectSum.induction_on with
        | zero => simp
        | add a₁ b₁ ha₁ hb₁ => simp only [tmul_add, add_mul, map_add, ha₁, hb₁]
        | of i a₁ =>
          induction a₂ using DirectSum.induction_on with
          | zero => simp
          | add a₂ b₂ ha₂ hb₂ => simp only [tmul_add, mul_add, map_add, ha₂, hb₂]
          | of j a₂ => simp_rw [Algebra.TensorProduct.tmul_mul_tmul, of_mul_of,
              ← lof_eq_of R, directSumRight_tmul_lof, lof_eq_of, of_mul_of,
              GradedMonoid.gmul_tensor_product]; simp
  commutes' s := by
    dsimp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    rw [DirectSum.one_def, ← lof_eq_of R, directSumRight_tmul_lof, algebraMap_apply]
    rfl

def DirectSum.lequivOfComponents {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A₁ : ι → Type*} [∀ i, AddCommMonoid (A₁ i)] [∀ i, Module R (A₁ i)]
    {A₂ : ι → Type*} [∀ i, AddCommMonoid (A₂ i)] [∀ i, Module R (A₂ i)]
    (e : ∀ i, A₁ i ≃ₗ[R] A₂ i) :
    DirectSum ι A₁ ≃ₗ[R] DirectSum ι A₂ :=
  .ofLinear (toModule _ _ _ (fun i ↦ lof R ι A₂ i ∘ₗ e i))
    (toModule _ _ _ (fun i ↦ lof R ι A₁ i ∘ₗ (e i).symm))
    (by ext; simp)
    (by ext; simp)

def DirectSum.algEquivOfComponents {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A₁ : ι → Type*} [∀ i, AddCommMonoid (A₁ i)] [∀ i, Module R (A₁ i)]
    {A₂ : ι → Type*} [∀ i, AddCommMonoid (A₂ i)] [∀ i, Module R (A₂ i)]
    [GCommSemiring A₁] [GAlgebra R A₁]
    [GCommSemiring A₂] [GAlgebra R A₂]
    (e : ∀ i, A₁ i ≃ₗ[R] A₂ i)
    (one : e 0 1 = 1)
    (mul : ∀ {i j} (x : A₁ i) (y : A₁ j), e (i + j) (GradedMonoid.GMul.mul x y) =
      GradedMonoid.GMul.mul (e i x) (e j y)) :
    DirectSum ι A₁ ≃ₐ[R] DirectSum ι A₂ :=
  .ofAlgHom (toAlgebra _ _ (fun i ↦ lof R ι A₂ i ∘ₗ e i) (by simp [one, lof_eq_of])
      fun xi xj ↦ by simp [mul, lof_eq_of, of_mul_of])
    (toAlgebra _ _ (fun i ↦ lof R ι A₁ i ∘ₗ (e i).symm) (by simp [← one, lof_eq_of])
      fun xi xj ↦ by simp [lof_eq_of, of_mul_of, ← (e _).symm_apply_eq.mpr (mul _ _).symm])
    (by ext; simp [lof_eq_of])
    (by ext; simp [lof_eq_of])

def Submodule.toBaseChange {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (S : Type*) [Semiring S] [Algebra R S]
    (N : Submodule R M) : S ⊗[R] N →ₗ[S] N.baseChange S :=
  LinearMap.rangeRestrict _

@[simp] lemma Submodule.toBaseChange_tmul_coe {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (S : Type*) [Semiring S] [Algebra R S]
    (N : Submodule R M) (s : S) (n : N) :
    Submodule.toBaseChange S N (s ⊗ₜ[R] n) = s ⊗ₜ[R] (n : M) :=
  rfl

lemma Submodule.toBaseChange_surjective {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (S : Type*) [Semiring S] [Algebra R S]
    (N : Submodule R M) :
    Function.Surjective (Submodule.toBaseChange S N) :=
  LinearMap.surjective_rangeRestrict _

lemma Function.Bijective.of_comp_of_surjective {α β γ : Sort*} {f : β → γ} {g : α → β}
    (hfg : Function.Bijective (f ∘ g)) (hg : Function.Surjective g) : Function.Bijective f :=
  ⟨.of_comp_right hfg.injective hg, .of_comp hfg.surjective⟩

private theorem DirectSum.IsInternal.baseChange_aux {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι]
    {A : Type*} [AddCommMonoid A] [Module R A]
    {𝒜 : ι → Submodule R A} (internal : IsInternal 𝒜)
    (S : Type*) [Semiring S] [Algebra R S] :
    (IsInternal fun i ↦ (𝒜 i).baseChange S) ∧ ∀ i, Function.Injective ((𝒜 i).toBaseChange S) := by
  have := internal.chooseDecomposition
  let e := (baseChangeLEquiv (R := R) (fun i ↦ 𝒜 i) S).symm ≪≫ₗ
    (decomposeLinearEquiv 𝒜).symm.baseChange R S
  let e₁ : (⨁ i, S ⊗[R] 𝒜 i) →ₗ[S] ⨁ i, (𝒜 i).baseChange S :=
    lmap fun i ↦ (𝒜 i).toBaseChange S
  let e₂ : (⨁ i, (𝒜 i).baseChange S) →ₗ[S] S ⊗[R] A :=
    toModule _ _ _ fun i ↦ Submodule.subtype _
  have he : e₂ ∘ₗ e₁ = e := by
    ext
    simp only [AlgebraTensorModule.curry_apply, curry_apply,
      LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, lmap_lof,
      toModule_lof, Submodule.subtype_apply, Submodule.toBaseChange_tmul_coe, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, baseChangeLEquiv_symm_apply, e₂, e₁, e]
    rw [lof_eq_of S, ← lof_eq_of R, directSumRight_symm_lof_tmul]
    simp [LinearEquiv.baseChange, lof_eq_of]
  have he' : e₂ ∘ e₁ = e := congr($he)
  have he₂ : Function.Bijective e₂ :=
    .of_comp_of_surjective (g := e₁) (he' ▸ e.bijective)
      ((lmap_surjective _).mpr fun _ ↦ LinearMap.surjective_rangeRestrict _)
  have he₁ : Function.Injective e₁ := .of_comp (f := e₂) (he' ▸ e.injective)
  exact ⟨he₂, fun i x y h ↦ of_injective (β := fun i ↦ S ⊗[R] 𝒜 i) i <| he₁ <| by simp [e₁, h]⟩

theorem DirectSum.IsInternal.baseChange {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι]
    {A : Type*} [AddCommMonoid A] [Module R A]
    {𝒜 : ι → Submodule R A} (internal : IsInternal 𝒜)
    (S : Type*) [Semiring S] [Algebra R S] :
    IsInternal fun i ↦ (𝒜 i).baseChange S :=
  (internal.baseChange_aux S).1

theorem DirectSum.IsInternal.toBaseChange_bijective {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι]
    {A : Type*} [AddCommMonoid A] [Module R A]
    {𝒜 : ι → Submodule R A} (internal : IsInternal 𝒜)
    (S : Type*) [Semiring S] [Algebra R S] (i : ι) :
    Function.Bijective (Submodule.toBaseChange S (𝒜 i)) :=
  ⟨(internal.baseChange_aux S).2 i, (𝒜 i).toBaseChange_surjective S⟩

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
  (S : Type*) [CommRing S] [Algebra R S]

namespace GradedAlgebra

open TensorProduct Submodule DirectSum

instance : SetLike.GradedMonoid (fun n ↦ (𝒜 n).baseChange S) where
  one_mem := by
    rw [Algebra.TensorProduct.one_def]
    exact tmul_mem_baseChange_of_mem _ (SetLike.one_mem_graded _)
  mul_mem {i j} := by
    suffices h : (𝒜 i).baseChange S * (𝒜 j).baseChange S ≤ (𝒜 (i + j)).baseChange S from
      fun _ _ hx hy ↦ h (mul_mem_mul hx hy)
    rw [baseChange_eq_span, baseChange_eq_span, span_mul_span, span_le, Set.mul_subset_iff]
    rintro - ⟨x, hx, rfl⟩ - ⟨y, hy, rfl⟩
    simp only [mk_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    exact tmul_mem_baseChange_of_mem _ (SetLike.mul_mem_graded hx hy)

-- def tensorProductAlgEquiv : S ⊗[R] A ≃ₐ[S] ⨁ i, (𝒜 i).baseChange S :=
--   (Algebra.TensorProduct.congr AlgEquiv.refl (DirectSum.decomposeAlgEquiv 𝒜)).trans <|
--     (baseChangeAlgEquiv (R := R) (S := S) (A := fun i ↦ 𝒜 i)).trans <|
--       algEquivOfComponents (fun i ↦ .ofBijective ((𝒜 i).toBaseChange S) _)  _  _

noncomputable def baseChangeLEquiv (n : ι) : S ⊗[R] 𝒜 n ≃ₗ[S] (𝒜 n).baseChange S :=
  LinearEquiv.ofBijective _ ((Decomposition.isInternal 𝒜).toBaseChange_bijective S n)

noncomputable instance : GradedAlgebra (fun n ↦ (𝒜 n).baseChange S) :=
  ((Decomposition.isInternal 𝒜).baseChange S).gradedAlgebra

/- where
  one_mem := by
    rw [Algebra.TensorProduct.one_def]
    exact tmul_mem_baseChange_of_mem _ (SetLike.one_mem_graded _)
  mul_mem {i j} := by
    suffices h : (𝒜 i).baseChange S * (𝒜 j).baseChange S ≤ (𝒜 (i + j)).baseChange S from
      fun _ _ hx hy ↦ h (mul_mem_mul hx hy)
    rw [baseChange_eq_span, baseChange_eq_span, span_mul_span, span_le, Set.mul_subset_iff]
    rintro - ⟨x, hx, rfl⟩ - ⟨y, hy, rfl⟩
    simp only [mk_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    exact tmul_mem_baseChange_of_mem _ (SetLike.mul_mem_graded hx hy)
  decompose' := _ -/

end GradedAlgebra
