/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.ProjectiveSpace.TensorProduct.GradedAlgebra
import EllipticCurve.ProjectiveSpace.TensorProduct.ProjMap
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.GradedAlgebra.Basic

/-! # Proj of Tensor Product

In this file we show `Proj (S ⊗[R] 𝒜) ≅ Spec S ×_R Proj 𝒜` where `𝒜` is a graded `R`-algebra.
-/

universe u₁ u₂ u v

open TensorProduct in
def AlgHom.liftBaseChange {R S A B : Type*}
    [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f : A →ₐ[R] B) :
    S ⊗[R] A →ₐ[S] B :=
  .ofLinearMap (.liftBaseChange S f) (by simp [Algebra.TensorProduct.one_def]) fun x y ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x₁ x₂ hx₁ hx₂ => simp [add_mul, hx₁, hx₂]
    | tmul s₁ a₁ => induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ hy₁ hy₂ => simp [mul_add, hy₁, hy₂]
      | tmul s₂ a₂ => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_smul, smul_comm s₁]

@[simp] lemma AlgHom.liftBaseChange_tmul {R S A B : Type*}
    [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f : A →ₐ[R] B) (s : S) (a : A) :
    f.liftBaseChange (s ⊗ₜ a) = s • f a := rfl

open TensorProduct in
@[ext high] theorem Algebra.TensorProduct.ext_ring {R S A B : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [CommSemiring S] [Algebra R S] [Algebra S B] [IsScalarTower R S B]
    {f g : S ⊗[R] A →ₐ[S] B}
    (h : (AlgHom.restrictScalars R f).comp Algebra.TensorProduct.includeRight =
      (AlgHom.restrictScalars R g).comp Algebra.TensorProduct.includeRight) :
    f = g :=
  ext (Subsingleton.elim _ _) h

section degree

noncomputable def DirectSum.degree {ι M σ : Type*} [Zero M] [SetLike σ M] [ZeroMemClass σ M]
    [Zero ι] (ℳ : ι → σ) (x : M) : ι :=
  open Classical in if h : x ≠ 0 ∧ ∃ i, x ∈ ℳ i then h.2.choose else 0

namespace DirectSum

variable {ι M σ : Type*} [SetLike σ M] (ℳ : ι → σ)

theorem degree_of_mem [AddCommMonoid M] [DecidableEq ι] [Zero ι] [AddSubmonoidClass σ M]
    [Decomposition ℳ] (x : M) (i : ι) (hx₀ : x ≠ 0) (hxi : x ∈ ℳ i) : degree ℳ x = i := by
  rw [degree, dif_pos ⟨hx₀, _, hxi⟩]
  generalize_proofs h
  exact degree_eq_of_mem_mem _ h.choose_spec hxi hx₀

theorem mem_degree [AddCommMonoid M] [DecidableEq ι] [Zero ι] [AddSubmonoidClass σ M]
    [Decomposition ℳ] (x : M) (hx : SetLike.IsHomogeneousElem ℳ x) : x ∈ ℳ (degree ℳ x) := by
  by_cases hx₀ : x = 0
  · rw [hx₀]; exact zero_mem _
  obtain ⟨i, hxi⟩ := hx
  rwa [degree_of_mem ℳ x i hx₀ hxi]

theorem decompose_of_homogeneous [AddCommMonoid M] [DecidableEq ι] [Zero ι] [AddSubmonoidClass σ M]
    [Decomposition ℳ] (x : M) (hx : SetLike.IsHomogeneousElem ℳ x) :
    decompose ℳ x = of (fun i ↦ ℳ i) (degree ℳ x) (⟨x, mem_degree ℳ x hx⟩ : ℳ _) :=
  decompose_of_mem ℳ _

theorem degree_mul [Semiring M] [AddSubmonoidClass σ M] [DecidableEq ι] [AddMonoid ι]
    [GradedRing ℳ] (x y : M) (hx : SetLike.IsHomogeneousElem ℳ x)
    (hy : SetLike.IsHomogeneousElem ℳ y) (hxy : x * y ≠ 0) :
    degree ℳ (x * y) = degree ℳ x + degree ℳ y :=
  degree_of_mem _ _ _ hxy <| SetLike.mul_mem_graded (mem_degree _ _ hx) (mem_degree _ _ hy)

theorem coe_apply_congr [AddCommMonoid M] [AddSubmonoidClass σ M]
    {x : ⨁ i, ℳ i} {i j : ι} (h : i = j) : (x i : M) = x j := by
  subst h; rfl

end DirectSum

end degree

open DirectSum in
noncomputable def HomogeneousLocalization.proj₀ {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
    (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (S : Submonoid A) (homog : S ≤ SetLike.homogeneousSubmonoid 𝒜) :
    Localization S →ₗ[HomogeneousLocalization 𝒜 S] HomogeneousLocalization 𝒜 S where
  toFun x := x.liftOn (fun a s ↦ .mk ⟨degree 𝒜 s.1, decompose 𝒜 a _,
    ⟨s, mem_degree _ _ (homog s.2)⟩, s.2⟩) fun {a₁ a₂} {s₁ s₂} h ↦ by
      ext
      simp_rw [val_mk, Localization.mk_eq_mk_iff]
      rw [Localization.r_iff_exists] at h ⊢
      obtain ⟨s, hs⟩ := h
      refine ⟨s, ?_⟩
      have hs' := congr((decompose 𝒜 $hs (degree 𝒜 (s : A) +
        (degree 𝒜 (s₁ : A) + degree 𝒜 (s₂ : A))) : A))
      simp_rw [decompose_mul, decompose_of_homogeneous _ _ (homog s.2),
        decompose_of_homogeneous _ _ (homog s₁.2), decompose_of_homogeneous _ _ (homog s₂.2),
        coe_of_mul_apply_add, coe_apply_congr _ (add_comm (degree 𝒜 (s₁ : A)) _),
        coe_of_mul_apply_add] at hs'
      exact hs'
  map_add' x y := Localization.induction_on₂ x y fun c d ↦ by
    ext
    by_cases hs₀ : 0 ∈ S
    · subsingleton [IsLocalization.uniqueOfZeroMem hs₀]
    have ne_zero {x} (hx : x ∈ S) : (x : A) ≠ 0 := fun hx₀ ↦ hs₀ <| hx₀ ▸ hx
    simp_rw [val_add, Localization.add_mk, Localization.liftOn_mk, val_mk,
      Localization.add_mk, decompose_add, add_apply, Submonoid.coe_mul, decompose_mul,
      Submodule.coe_add, Subtype.coe_eta]
    rw [degree_mul _ _ _ (homog c.2.2) (homog d.2.2) (ne_zero (c.2 * d.2).2),
      decompose_of_homogeneous _ _ (homog c.2.2),
      decompose_of_homogeneous _ _ (homog d.2.2),
      coe_of_mul_apply_add, coe_apply_congr _ (add_comm (degree 𝒜 (c.2 : A)) _),
      coe_of_mul_apply_add]
    rfl
  map_smul' r x := Localization.induction_on x fun d ↦ by
    obtain ⟨c, rfl⟩ := mk_surjective r
    ext
    by_cases hs₀ : 0 ∈ S
    · subsingleton [IsLocalization.uniqueOfZeroMem hs₀]
    have ne_zero {x} (hx : x ∈ S) : (x : A) ≠ 0 := fun hx₀ ↦ hs₀ <| hx₀ ▸ hx
    rw [RingHom.id_apply, Algebra.smul_def, smul_eq_mul, val_mul, algebraMap_apply, val_mk]
    simp_rw [Localization.mk_mul, Localization.liftOn_mk, val_mk, Localization.mk_mul,
      decompose_mul, decompose_coe, Subtype.coe_eta, Submonoid.coe_mul]
    rw [degree_mul _ _ _ ⟨_, c.den.2⟩ (homog d.2.2) (ne_zero <| S.mul_mem c.den_mem d.2.2),
      degree_of_mem _ _ _ (ne_zero c.den_mem) c.den.2,
      coe_of_mul_apply_add]

theorem HomogeneousLocalization.proj₀_mk {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
    (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (S : Submonoid A) (homog : S ≤ SetLike.homogeneousSubmonoid 𝒜)
    (a : A) (s : S) :
    HomogeneousLocalization.proj₀ 𝒜 S homog (Localization.mk a s) =
    HomogeneousLocalization.mk ⟨DirectSum.degree 𝒜 (s : A), DirectSum.decompose 𝒜 a _,
      ⟨s, DirectSum.mem_degree _ _ (homog s.2)⟩, s.2⟩ := rfl

@[simp] lemma HomogeneousLocalization.proj₀_val {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
    (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (S : Submonoid A) (homog : S ≤ SetLike.homogeneousSubmonoid 𝒜)
    (x : HomogeneousLocalization 𝒜 S) :
    HomogeneousLocalization.proj₀ 𝒜 S homog x.val = x := by
  ext
  by_cases hs₀ : 0 ∈ S
  · subsingleton [IsLocalization.uniqueOfZeroMem hs₀]
  induction x using Quotient.inductionOn' with
  | h c =>
    simp_rw [val, Quotient.liftOn'_mk'', NumDenSameDeg.embedding, proj₀_mk, mk,
      Quotient.liftOn'_mk'', NumDenSameDeg.embedding]
    rw [DirectSum.decompose_of_mem _ c.num.2, DirectSum.coe_of_apply, if_pos]
    rw [DirectSum.degree_of_mem _ _ _ (mt (· ▸ c.den_mem) hs₀) c.den.2]

noncomputable def HomogeneousLocalization.Away.proj₀ {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
    (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i : ι} {f : A} (hf : f ∈ 𝒜 i) :
    Localization.Away (f : A) →ₗ[HomogeneousLocalization.Away 𝒜 f]
      HomogeneousLocalization.Away 𝒜 f :=
  HomogeneousLocalization.proj₀ _ _ <| Submonoid.powers_le.mpr ⟨_, hf⟩

theorem HomogeneousLocalization.Away.proj₀_mk {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
    (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i : ι} {f : A} (hf : f ∈ 𝒜 i) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • i)) :
    proj₀ 𝒜 hf (.mk a ⟨f ^ n, n, rfl⟩) = .mk _ hf n a ha :=
  proj₀_val _ _ _ (Away.mk _ hf _ _ _)

theorem HomogeneousLocalization.Away.proj₀_mk' {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
    (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i : ι} {f : A} (hf : f ∈ 𝒜 i) (n : ℕ) (a : 𝒜 (n • i)) :
    proj₀ 𝒜 hf (.mk a ⟨f ^ n, n, rfl⟩) = .lof _ hf n a :=
  proj₀_mk _ _ _ _ _

open TensorProduct in
/-- `(S ⊗[R] A)[(1 ⊗ₜ W)⁻¹] ≅ (S ⊗[R] A)[W⁻¹]`. -/
noncomputable def IsLocalization.tensorEquiv (R S A A₁ SA₁ : Type*)
    [CommSemiring R] [CommSemiring S] [CommSemiring A] [CommSemiring A₁] [CommSemiring SA₁]
    [Algebra R S] [Algebra R A] (W₁ : Submonoid A) (W₂ : Submonoid (S ⊗[R] A))
    (hw : W₁.map Algebra.TensorProduct.includeRight = W₂)
    [Algebra A A₁] [IsLocalization W₁ A₁]
    [Algebra R A₁] [IsScalarTower R A A₁]
    [Algebra (S ⊗[R] A) SA₁] [IsLocalization W₂ SA₁]
    [Algebra R SA₁] [Algebra S SA₁] [IsScalarTower R S SA₁] [IsScalarTower S (S ⊗[R] A) SA₁]
    [IsScalarTower R (S ⊗[R] A) SA₁] :
    SA₁ ≃ₐ[S] S ⊗[R] A₁ :=
  .ofAlgHom
  (IsLocalization.liftAlgHom
    (M := W₂)
    (f := Algebra.TensorProduct.map (1 : S →ₐ[S] S) (Algebra.algHom R A A₁)) <| by
      rw [← hw]
      rintro ⟨_, w, hw, rfl⟩
      exact (IsLocalization.map_units _ ⟨w, hw⟩).map Algebra.TensorProduct.includeRight)
  (AlgHom.liftBaseChange <| IsLocalization.liftAlgHom (M := W₁)
    (f := (Algebra.algHom _ _ _).comp (Algebra.TensorProduct.includeRight (R := R) (A := S)))
    fun w ↦ IsLocalization.map_units (M := W₂) SA₁ ⟨_, hw ▸ ⟨_, w.2, rfl⟩⟩)
  (Algebra.TensorProduct.ext_ring <| IsLocalization.algHom_ext W₁ <| by ext; simp [Algebra.algHom])
  (IsLocalization.algHom_ext W₂ <| by ext; simp [Algebra.algHom])

open TensorProduct in
/-- `(S ⊗[R] A)[(1 ⊗ₜ W)⁻¹] ≅ S ⊗[R] A[W⁻¹]`. -/
noncomputable def Localization.tensorEquiv (R S : Type*) {A : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring A]
    [Algebra R S] [Algebra R A] (W : Submonoid A) :
    Localization (W.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) ≃ₐ[S]
    S ⊗[R] Localization W :=
  IsLocalization.tensorEquiv R S A _ _ W _ rfl

open TensorProduct in
/-- `(S ⊗[R] A)[(1 ⊗ₜ f)⁻¹] ≅ S ⊗[R] A[f⁻¹]`. -/
noncomputable def Localization.Away.tensorEquiv (R S : Type*) {A : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring A]
    [Algebra R S] [Algebra R A] (f : A) :
    Away (1 ⊗ₜ[R] f : S ⊗[R] A) ≃ₐ[S] S ⊗[R] Away f :=
  IsLocalization.tensorEquiv R S A _ _ (.powers f) (.powers (1 ⊗ₜ f)) (by simp)

@[simp] lemma Localization.Away.tensorEquiv_mk {R S : Type*} {A : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring A]
    [Algebra R S] [Algebra R A] (f : A) (s : S) (a : A) (n : ℕ) :
    tensorEquiv R S f (.mk (s ⊗ₜ a) ⟨1 ⊗ₜ (f ^ n), n, by simp⟩) = s ⊗ₜ .mk a ⟨f ^ n, n, rfl⟩ := by
  simp_rw [tensorEquiv, IsLocalization.tensorEquiv, AlgEquiv.ofAlgHom_apply,
    IsLocalization.liftAlgHom_apply, mk_eq_mk', IsLocalization.lift_mk',
    Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight]
  simp only [Algebra.algHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.map_tmul, AlgHom.one_apply, AlgHom.coe_mk, ← mk_one_eq_algebraMap,
    ← mk_eq_mk', RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_toMonoidHom,
    MonoidHom.restrict_apply, MonoidHom.coe_coe, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    mk_mul]
  congr 1
  exact mk_eq_mk_iff.mpr <| r_iff_exists.mpr ⟨1, by simp [mul_comm]⟩

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
  (S : Type u) [CommRing S] [Algebra R S]

namespace AlgebraicGeometry

open TensorProduct CategoryTheory Limits CommRingCat

noncomputable def Proj.toSpec : Proj 𝒜 ⟶ Spec(R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (ofHom (algebraMap R (𝒜 0)))

lemma baseChange_iSupEqTop :
    (HomogeneousIdeal.irrelevant fun n ↦ (𝒜 n).baseChange S).toIdeal ≤
    Ideal.span (Set.range fun f : (Proj.affineOpenCover 𝒜).I₀ ↦ 1 ⊗ₜ[R] f.2) := by
  intro x hx
  classical
  rw [← DirectSum.sum_support_decompose (fun n ↦ (𝒜 n).baseChange S) x]
  refine sum_mem fun i hi ↦ ?_
  have hi₀ : i ≠ 0 := fun hi₀ ↦ DFinsupp.mem_support_iff.mp hi (hi₀ ▸ by simpa using hx)
  generalize DirectSum.decompose (fun n ↦ (𝒜 n).baseChange S) x i = y
  obtain ⟨_, y, rfl⟩ := y
  obtain ⟨s, rfl⟩ := exists_finset y
  simp only [map_sum, LinearMap.baseChange_tmul, Submodule.subtype_apply]
  refine Ideal.sum_mem _ fun c hc ↦ ?_
  rw [← mul_one c.1, ← one_mul (c.2: A), ← Algebra.TensorProduct.tmul_mul_tmul]
  refine Ideal.mul_mem_left _ _ <| Ideal.subset_span ⟨⟨⟨i, pos_of_ne_zero hi₀⟩, _⟩, rfl⟩

set_option maxHeartbeats 999999 in
-- I don't know why
noncomputable def awayBaseChange {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) :
    HomogeneousLocalization.Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f) ≃ₐ[S]
      S ⊗[R] HomogeneousLocalization.Away 𝒜 f := by
  let f₁ : HomogeneousLocalization.Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f) →ₐ[S]
      Localization.Away (1 ⊗ₜ f : S ⊗[R] A) := Algebra.algHom _ _ _
  let f₂ : Localization.Away (1 ⊗ₜ f : S ⊗[R] A) ≃ₐ[S]
      S ⊗[R] Localization.Away (f : A) := Localization.Away.tensorEquiv _ _ _
  let f₃ : S ⊗[R] Localization.Away (f : A) →ₗ[S] S ⊗[R] HomogeneousLocalization.Away 𝒜 f :=
    ((HomogeneousLocalization.Away.proj₀ 𝒜 hf).restrictScalars R).baseChange S
  let forwards : HomogeneousLocalization.Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f) →ₗ[S]
      S ⊗[R] HomogeneousLocalization.Away 𝒜 f :=
    f₃ ∘ₗ f₂.toLinearMap ∘ₗ f₁.toLinearMap
  let backwards : S ⊗[R] HomogeneousLocalization.Away 𝒜 f →ₐ[S]
      HomogeneousLocalization.Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f) :=
    AlgHom.liftBaseChange <| HomogeneousLocalization.Away.mapₐ
      (Algebra.TensorProduct.includeRight (R := R) (A := S))
      (fun _ _ ↦ Submodule.tmul_mem_baseChange_of_mem _) rfl
  refine
    have left : backwards.toLinearMap ∘ₗ forwards = 1 := ?_
    have right : forwards ∘ₗ backwards.toLinearMap = 1 := ?_
    .symm { __ := backwards, invFun := forwards, left_inv := ?_, right_inv := ?_ }
  · ext x
    obtain ⟨n, a, rfl⟩ := x.lof_surjective _ (Submodule.tmul_mem_baseChange_of_mem _ hf)
    obtain ⟨a, rfl⟩ := Submodule.toBaseChange_surjective _ _ a
    simp only [smul_eq_mul, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      Module.End.one_apply]
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add a₁ a₂ ha₁ ha₂ => simp [ha₁, ha₂]
    | tmul s a =>
      simp only [forwards, f₁, f₂, f₃, backwards, Algebra.algHom]
      simp only [smul_eq_mul, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        AlgHom.coe_mk, HomogeneousLocalization.algebraMap_apply, AlgEquiv.toLinearMap_apply]
      erw [HomogeneousLocalization.Away.val_lof]
      simp only [smul_eq_mul, Submodule.toBaseChange_tmul_coe, Algebra.TensorProduct.tmul_pow,
        one_pow, Localization.Away.tensorEquiv_mk, LinearMap.baseChange_tmul,
        LinearMap.coe_restrictScalars, HomogeneousLocalization.Away.proj₀_mk',
        AlgHom.liftBaseChange_tmul, HomogeneousLocalization.val_smul]
      erw [HomogeneousLocalization.Away.mapₐ_lof]
      rw [HomogeneousLocalization.Away.val_lof]
      simp only [smul_eq_mul, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_pow, one_pow, Localization.smul_mk]
      congr 1
      rw [← tmul_eq_smul_one_tmul]
  · ext x
    obtain ⟨n, a, rfl⟩ := x.lof_surjective _ hf
    simp only [forwards, f₁, f₂, f₃, backwards, Algebra.algHom]
    simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp, smul_eq_mul,
      curry_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      AlgHom.toLinearMap_apply, AlgHom.liftBaseChange_tmul, one_smul, AlgHom.coe_mk,
      HomogeneousLocalization.algebraMap_apply, AlgEquiv.toLinearMap_apply, Module.End.one_apply]
    erw [HomogeneousLocalization.Away.mapₐ_lof]
    rw [HomogeneousLocalization.Away.val_lof]
    simp [HomogeneousLocalization.Away.proj₀_mk']
  · exact fun x ↦ congr($right x)
  · exact fun x ↦ congr($left x)

@[simps!] def _root_.GradedAlgebra.toTensor : 𝒜 →ᵍᵃ fun n ↦ (𝒜 n).baseChange S where
  __ := Algebra.TensorProduct.includeRight
  map_mem' _ _ := Submodule.tmul_mem_baseChange_of_mem _

lemma _root_.GradedAlgebra.toTensor_admissible :
    (HomogeneousIdeal.irrelevant fun n ↦ (𝒜 n).baseChange S) ≤
    (HomogeneousIdeal.irrelevant 𝒜).map (GradedAlgebra.toTensor 𝒜 S) := by
  refine (HomogeneousIdeal.irrelevant_le _).mpr fun i hi x hx ↦ ?_
  obtain ⟨a, ha⟩ := Submodule.toBaseChange_surjective _ _ ⟨x, hx⟩
  replace ha := congr(($ha).val); subst ha
  induction a with
  | zero => simp
  | add => simp [*, add_mem]
  | tmul s a =>
    simp only [Submodule.toBaseChange_tmul_coe]
    rw [tmul_eq_smul_one_tmul, ← algebraMap_smul (S ⊗[R] A), smul_eq_mul]
    exact Ideal.mul_mem_left _ _ <| Ideal.mem_map_of_mem _ <|
      HomogeneousIdeal.mem_irrelevant_of_mem _ hi a.2

@[simp] lemma awayBaseChange_symm_tmul
    {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) {s : S} {x : HomogeneousLocalization.Away 𝒜 f} :
    (awayBaseChange 𝒜 S hf).symm (s ⊗ₜ x) =
    s • .map (GradedAlgebra.toTensor 𝒜 S) rfl x := by
  obtain ⟨n, a, rfl⟩ := x.lof_surjective _ hf
  rw [AlgEquiv.symm_apply_eq, HomogeneousLocalization.Away.map_lof, map_smul]
  simp only [smul_eq_mul, awayBaseChange, AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe,
    AlgHom.toRingHom_toMonoidHom, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
    Algebra.algHom, LinearMap.coe_comp, AlgEquiv.symm_mk, GradedAlgebra.toTensor_toFun,
    AlgEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, AlgHom.toLinearMap_apply, AlgHom.coe_mk,
    HomogeneousLocalization.algebraMap_apply, AlgEquiv.toLinearMap_apply]
  conv => enter [2,2,2,2]; exact HomogeneousLocalization.Away.val_lof _ _ _ _
  simp [HomogeneousLocalization.Away.lof, HomogeneousLocalization.lof,
    HomogeneousLocalization.Away.proj₀_mk, HomogeneousLocalization.Away.mk,
    ← tmul_eq_smul_one_tmul]

@[simp] lemma awayBaseChange_lof {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) {s : S} {n : ℕ} {a : 𝒜 (n • i)} :
    awayBaseChange 𝒜 S hf (.lof (fun n ↦ (𝒜 n).baseChange S)
      (Submodule.tmul_mem_baseChange_of_mem _ hf) n (Submodule.toBaseChange _ _ (s ⊗ₜ a))) =
    s ⊗ₜ .lof _ hf n a := by
  rw [← AlgEquiv.eq_symm_apply, awayBaseChange_symm_tmul,
    HomogeneousLocalization.Away.map_lof, tmul_eq_smul_one_tmul s, map_smul, map_smul]
  rfl

noncomputable def Proj.baseChangeIsoComponent {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) :
    Spec(HomogeneousLocalization.Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f)) ≅
    pullback (Spec.map (ofHom (algebraMap R S)))
      (Spec.map (ofHom (algebraMap R (HomogeneousLocalization.Away 𝒜 f)))) :=
  Scheme.Spec.mapIso (awayBaseChange 𝒜 S hf).toCommRingCatIso.op.symm ≪≫
  (pullbackSpecIso _ _ _).symm

@[reassoc (attr := simp)] lemma Proj.baseChangeIsoComponent_hom_comp_pullback_fst
    {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) :
    (Proj.baseChangeIsoComponent 𝒜 S hf).hom ≫ pullback.fst _ _ =
    Spec.map (ofHom (algebraMap S _)) := by
  simp only [HomogeneousLocalization.algebraMap_eq', ofHom_comp, baseChangeIsoComponent,
    Scheme.Spec_obj, AlgEquiv.toRingEquiv_eq_coe, Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.op_inv, RingEquiv.toCommRingCatIso_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, Category.assoc]
  conv => enter [1,2]; exact pullbackSpecIso_inv_fst ..
  simp only [← Spec.map_comp, ← ofHom_comp]
  congr 2; ext s
  simp [← AlgEquiv.symm_toRingEquiv, IsScalarTower.algebraMap_apply S (S ⊗[R] A) (Localization _),
    ← Localization.mk_one_eq_algebraMap, tmul_eq_smul_one_tmul s, ← Localization.smul_mk,
    ← Algebra.TensorProduct.one_def, Localization.mk_one]

@[reassoc (attr := simp)] lemma Proj.baseChangeIsoComponent_hom_comp_pullback_snd
    {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) :
    (Proj.baseChangeIsoComponent 𝒜 S hf).hom ≫ pullback.snd _ _ =
    Spec.map (ofHom (HomogeneousLocalization.Away.map (GradedAlgebra.toTensor ..) rfl)) := by
  simp only [HomogeneousLocalization.algebraMap_eq', ofHom_comp, baseChangeIsoComponent,
    Scheme.Spec_obj, AlgEquiv.toRingEquiv_eq_coe, Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.op_inv, RingEquiv.toCommRingCatIso_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, Category.assoc, GradedAlgebra.toTensor_toFun]
  conv => enter [1,2]; exact pullbackSpecIso_inv_snd ..
  rw [← Spec.map_comp, ← ofHom_comp]
  congr 2; ext x
  simp [← AlgEquiv.symm_toRingEquiv]

@[reassoc] lemma Proj.map_toSpec {R R₁ R₂ A B : Type u}
    [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A] [CommRing B]
    [Algebra R R₁] [Algebra R R₂] [Algebra R A] [Algebra R B]
    [Algebra R₁ A] [IsScalarTower R R₁ A] [Algebra R₂ B] [IsScalarTower R R₂ B]
    (𝒜 : ℕ → Submodule R₁ A) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule R₂ B) [GradedAlgebra ℬ]
    (f : 𝒜 →ᵍᵃ ℬ) (hf) (hfr : ∀ r, f (algebraMap R A r) = algebraMap R B r) :
    Proj.map f hf ≫ Proj.toSpec 𝒜 ≫ Spec.map (ofHom (algebraMap R R₁)) =
    Proj.toSpec ℬ ≫ Spec.map (ofHom (algebraMap R R₂)) := by
  simp only [toSpec, Category.assoc, ← Spec.map_comp, ← ofHom_comp, map_comp_toSpecZero_assoc]
  congr 3; ext; simp [← IsScalarTower.algebraMap_apply, hfr]

@[reassoc (attr := simp)] lemma Proj.map_toTensor_toSpec :
    Proj.map _ (GradedAlgebra.toTensor_admissible 𝒜 S) ≫ Proj.toSpec 𝒜 =
    Proj.toSpec _ ≫ Spec.map (ofHom (algebraMap R S)) := by
  simpa using Proj.map_toSpec (R := R) _ _ _ (GradedAlgebra.toTensor_admissible 𝒜 S) fun r ↦ by
    simp [Algebra.TensorProduct.one_def, Algebra.algebraMap_eq_smul_one r, smul_tmul']

noncomputable def ofProjTensor :
    Proj (fun n ↦ (𝒜 n).baseChange S) ⟶
    pullback (Spec.map (ofHom (algebraMap R S))) (Proj.toSpec 𝒜) :=
  pullback.lift (Proj.toSpec _) (Proj.map _ <| GradedAlgebra.toTensor_admissible _ _) <| by simp

@[reassoc (attr := simp)] lemma Proj.awayι_comp_toSpec
    {i : ℕ} (hi : 0 < i) {s : A} (hs : s ∈ 𝒜 i) :
    Proj.awayι 𝒜 s hs hi ≫ Proj.toSpec 𝒜 = Spec.map (ofHom (algebraMap _ _)) := by
  simp [toSpec, awayι_toSpecZero_assoc]

/--
The following square commutes:
```
Proj(S ⊗[R] 𝒜) ---------⟶ Spec(S) ×[Spec(R)] Proj(𝒜)
    ^           ofProjTensor             ^
    |                                    |
    | awayι                              | 𝟙 × awayι
    |                                    |
    |           baseChangeIsoComponent   |
Spec((S⊗[R]A)[(1⊗s)⁻¹]) ⟶ Spec(S) ×[Spec(R)] Spec(A[s⁻¹])
```
-/
@[simp] lemma awayι_comp_ofProjTensor {i : ℕ} (hi : 0 < i) {s : A} (hs : s ∈ 𝒜 i) :
    Proj.awayι (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ s) (Submodule.tmul_mem_baseChange_of_mem _ hs)
      hi ≫ ofProjTensor 𝒜 S =
    (Proj.baseChangeIsoComponent 𝒜 S hs).hom ≫
      pullback.map _ _ _ _ (𝟙 _) (Proj.awayι _ s hs hi) (𝟙 _) (by simp) (by simp) :=
  pullback.hom_ext (by simp [- HomogeneousLocalization.algebraMap_eq', ofProjTensor]) <| by
  simpa [- HomogeneousLocalization.algebraMap_eq', ofProjTensor] using
    Proj.awayι_comp_map _ (GradedAlgebra.toTensor_admissible 𝒜 S) hi s hs

namespace Scheme

@[simp] lemma image_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsOpenImmersion f] [IsOpenImmersion g] (U : X.Opens) :
    (f ≫ g) ''ᵁ U = g ''ᵁ f ''ᵁ U :=
  TopologicalSpace.Opens.ext <| Set.image_comp g.base f.base (U : Set X)

lemma image_id' {X : Scheme.{u}} {f : X ⟶ X} [IsOpenImmersion f] (hf : f = 𝟙 X) {U : X.Opens} :
    f ''ᵁ U = U := by
  subst hf; exact TopologicalSpace.Opens.ext <| Set.image_id _

@[simp] lemma image_inv {X Y : Scheme.{u}} {f : X ≅ Y} (V : Y.Opens) :
    f.inv ''ᵁ V = f.hom ⁻¹ᵁ V := by
  rw [← f.hom.preimage_image_eq (f.inv ''ᵁ V), ← image_comp, image_id' (by simp)]

@[simp] lemma image_inv' {X Y : Scheme.{u}} {f : X ⟶ Y} [IsIso f] (V : Y.Opens) :
    (inv f) ''ᵁ V = f ⁻¹ᵁ V :=
  image_inv (f := asIso f) V

@[simp] lemma image_preimage {X Y : Scheme.{u}} {f : X ⟶ Y} [IsIso f] {V : Y.Opens} :
    f ''ᵁ (f ⁻¹ᵁ V) = V :=
  TopologicalSpace.Opens.ext <| Set.image_preimage_eq _
    (ConcreteCategory.bijective_of_isIso f.base).surjective

lemma image_eq_iff_eq_preimage {X Y : Scheme.{u}} {f : X ⟶ Y} [IsIso f]
    {U : X.Opens} {V : Y.Opens} :
    f ''ᵁ U = V ↔ U = f ⁻¹ᵁ V :=
  ⟨(· ▸ by simp), (· ▸ by simp)⟩

end Scheme

/-- To check if `f : X ⟶ Y` is an isomorphism, one can supply an open cover of `X` and an open
cover of `Y` (indexed by the same set `S`), and then maps `f_i : U_i ⟶ V_i` for `i : S` that are
iso such that the squares commute. -/
theorem isIso_of_cover {X Y : Scheme.{v}} (f : X ⟶ Y)
    (U : X.OpenCover) (V : Y.OpenCover)
    {ι : Type*} (iU : ι → U.I₀) (hu : iU.Surjective) (iV : ι → V.I₀) (hv : iV.Surjective)
    (φ : ∀ i : ι, U.X (iU i) ⟶ V.X (iV i)) [∀ i, IsIso (φ i)]
    (hfφ : ∀ i : ι, U.f (iU i) ≫ f = φ i ≫ V.f (iV i))
    (preimage : ∀ i : ι, f ⁻¹ᵁ (V.f (iV i)).opensRange = (U.f (iU i)).opensRange) :
    IsIso f :=
  let U' : X.OpenCover :=
  { I₀ := ι
    X i := U.X (iU i)
    f i := U.f (iU i)
    idx x := (hu (U.idx x)).choose
    covers x := by rw [(hu (U.idx x)).choose_spec]; exact U.covers x }
  let V' : Y.OpenCover :=
  { I₀ := ι
    X i := V.X (iV i)
    f i := V.f (iV i)
    idx y := (hv (V.idx y)).choose
    covers y := by rw [(hv (V.idx y)).choose_spec]; exact V.covers y }
  let inv : Y ⟶ X := V'.glueMorphisms (fun i : ι ↦ inv (φ i) ≫ U'.f i) fun i₁ i₂ : ι ↦ by
    let p : pullback (V'.f i₁) (V'.f i₂) ⟶ pullback (U'.f i₁) (U'.f i₂) :=
      IsOpenImmersion.lift (pullback.fst _ _) (pullback.fst _ _ ≫ inv (φ i₁)) <| by
        rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, SetLike.coe_subset_coe,
          IsOpenImmersion.opensRange_pullback_fst_of_right, Scheme.Hom.opensRange_comp,
          IsOpenImmersion.opensRange_pullback_fst_of_right, Scheme.image_inv',
          ← Scheme.preimage_comp, ← hfφ, Scheme.preimage_comp, preimage]
    have hp₁ : p ≫ pullback.fst _ _ = pullback.fst _ _ ≫ inv (φ i₁) :=
      IsOpenImmersion.lift_fac _ _ _
    have hp₂ : p ≫ pullback.snd _ _ = pullback.snd _ _ ≫ inv (φ i₂) := by
      rw [IsIso.eq_comp_inv]
      refine (cancel_mono (V'.f i₂)).mp ?_
      simp_rw [Category.assoc]
      rw [← hfφ, ← pullback.condition_assoc, reassoc_of% hp₁, hfφ, IsIso.inv_hom_id_assoc,
        pullback.condition]
    dsimp only
    rw [← reassoc_of% hp₁, pullback.condition, reassoc_of% hp₂]
  have comp_inv : f ≫ inv = 𝟙 X := U'.hom_ext _ _ fun i ↦ by
    unfold inv
    rw [reassoc_of% hfφ, V'.ι_glueMorphisms, IsIso.hom_inv_id_assoc, Category.comp_id]
  have inv_comp : inv ≫ f = 𝟙 Y := V'.hom_ext _ _ fun i ↦ by
    unfold inv
    rw [V'.ι_glueMorphisms_assoc, Category.assoc, hfφ, IsIso.inv_hom_id_assoc, Category.comp_id]
  ⟨inv, comp_inv, inv_comp⟩

noncomputable def Proj.openCoverBaseChange :
    (Proj fun n ↦ (𝒜 n).baseChange S).AffineOpenCover :=
  Proj.mapAffineOpenCover _ <| GradedAlgebra.toTensor_admissible 𝒜 S

noncomputable def Proj.openCoverPullback :
    (pullback (Spec.map (ofHom (algebraMap R S))) (Proj.toSpec 𝒜)).OpenCover :=
  (Scheme.Pullback.openCoverOfRight (Proj.affineOpenCover 𝒜).openCover
      (Spec.map <| ofHom <| algebraMap R S) (Proj.toSpec 𝒜)).copy
    (Proj.affineOpenCover 𝒜).I₀
    (fun f ↦ pullback (Spec.map (ofHom (algebraMap R S)))
      (Spec.map (ofHom (algebraMap R (HomogeneousLocalization.Away 𝒜 f.2)))))
    (fun f ↦ pullback.map _ _ _ _ (𝟙 _) (Proj.awayι 𝒜 f.2 f.2.2 f.1.2) (𝟙 _) (by simp) (by simp))
    (Equiv.refl _) (fun _ ↦ pullback.congrHom rfl (by simp [affineOpenCover, openCoverOfISupEqTop]))
    fun f ↦ pullback.hom_ext (by simp) (by simp [Proj.affineOpenCover, Proj.openCoverOfISupEqTop])

@[simp] lemma Proj.opensRange_openCoverPullback {f} :
    ((Proj.openCoverPullback 𝒜 S).f f).opensRange =
    pullback.snd (Spec.map (ofHom (algebraMap R S))) (toSpec 𝒜) ⁻¹ᵁ basicOpen _ f.2 :=
  TopologicalSpace.Opens.ext <| by
    simp [openCoverPullback, Scheme.Pullback.range_map, ← Proj.opensRange_awayι _ _ f.2.2]

instance : IsIso (ofProjTensor 𝒜 S) :=
  isIso_of_cover _ (Proj.openCoverBaseChange 𝒜 S).openCover
    (Proj.openCoverPullback 𝒜 S)
    id Function.surjective_id id Function.surjective_id
    (fun f ↦ (Proj.baseChangeIsoComponent 𝒜 S f.2.2).hom)
    (fun f ↦ by simp [Proj.openCoverBaseChange, Proj.openCoverPullback])
    fun f ↦ by simp [← Scheme.preimage_comp, - TopologicalSpace.Opens.map_comp_obj, ofProjTensor,
      Proj.openCoverBaseChange, Proj.opensRange_awayι]

-- https://math.arizona.edu/~cais/CourseNotes/AlgGeom04/notes216.pdf
noncomputable def projTensorProduct : Proj (fun n ↦ (𝒜 n).baseChange S) ≅
    pullback (Spec.map (ofHom (algebraMap R S))) (Proj.toSpec 𝒜) :=
  asIso <| ofProjTensor 𝒜 S

@[simp] lemma projTensorProduct_hom_comp_pullback_fst :
    (projTensorProduct 𝒜 S).hom ≫ pullback.fst _ _ = Proj.toSpec _ := by
  simp [projTensorProduct, ofProjTensor]

@[simp] lemma projTensorProduct_hom_comp_pullback_snd :
    (projTensorProduct 𝒜 S).hom ≫ pullback.snd _ _ =
    Proj.map _ (GradedAlgebra.toTensor_admissible 𝒜 S) := by
  simp [projTensorProduct, ofProjTensor]

@[simp] lemma awayι_comp_projTensorProduct {i : ℕ} (hi : 0 < i) {s : A} (hs : s ∈ 𝒜 i) :
    Proj.awayι (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ s) (Submodule.tmul_mem_baseChange_of_mem _ hs)
      hi ≫ (projTensorProduct 𝒜 S).hom =
    (Proj.baseChangeIsoComponent 𝒜 S hs).hom ≫
      pullback.map _ _ _ _ (𝟙 _) (Proj.awayι _ s hs hi) (𝟙 _) (by simp) (by simp) :=
  awayι_comp_ofProjTensor _ _ _ _

@[simp] lemma projTensorProduct_image_basicOpen {s : A} :
    (projTensorProduct 𝒜 S).hom ''ᵁ (Proj.basicOpen (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ s)) =
    pullback.snd (Spec.map (ofHom (algebraMap R S))) (Proj.toSpec 𝒜) ⁻¹ᵁ Proj.basicOpen 𝒜 s := by
  rw [Scheme.image_eq_iff_eq_preimage, ← Scheme.preimage_comp,
    projTensorProduct_hom_comp_pullback_snd, Proj.map_preimage_basicOpen,
    GradedAlgebra.toTensor_toFun]

end AlgebraicGeometry
