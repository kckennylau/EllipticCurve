/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import EllipticCurve.ProjectiveSpace.Graded.HomogeneousLocalization
import EllipticCurve.ProjectiveSpace.TensorProduct.GradedAlgebra
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Homogeneous localization of tensor product of graded algebra

Let `𝒜` be a graded `R`-algebra, and `S` be an `R`-algebra. Then `S ⊗[R] 𝒜` is a graded
`S`-algebra with the same grading.

Let `W` be a homogeneous submonoid of `𝒜`. Then `(S⊗[R]𝒜)[(1⊗W)⁻¹]₀ ≅ S ⊗[R] (𝒜[W⁻¹]₀)`.
-/

local notation:max "at " W => Localization W
local notation:max 𝒜"["W"⁻¹]₀" => HomogeneousLocalization 𝒜 W

open DirectSum SetLike

theorem coe_apply_congr {M σ ι : Type*} [AddCommMonoid M] [SetLike σ M] [AddSubmonoidClass σ M]
    {ℳ : ι → σ} {x : ⨁ i, ℳ i} {i j : ι} (h : i = j) : (x i : M) = x j := by
  subst h; rfl

namespace HomogeneousLocalization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]

noncomputable def proj₀ (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (S : Submonoid A) (homog : S ≤ SetLike.homogeneousSubmonoid 𝒜) :
    (at S) →ₗ[𝒜[S⁻¹]₀] 𝒜[S⁻¹]₀ := by
  refine
  { toFun x := x.liftOn (fun a s ↦ .mk ⟨(homog s.2).choose, decompose 𝒜 a _,
      ⟨s, (homog s.2).choose_spec⟩, s.2⟩) fun {a₁ a₂} {s₁ s₂} h ↦ ?_,
    map_add' x y := ?_,
    map_smul' c x := ?_ }
  · ext
    simp_rw [val_mk, Subtype.coe_eta, Localization.mk_eq_mk_iff]
    rw [Localization.r_iff_exists] at h ⊢
    obtain ⟨s, hs⟩ := h
    refine ⟨s, ?_⟩
    replace hs := congr((decompose 𝒜 $hs ((homog s.2).choose +
      ((homog s₁.2).choose + (homog s₂.2).choose)) : A))
    simp_rw [decompose_mul, decompose_of_mem _ (homog (Subtype.prop _)).choose_spec,
      coe_of_mul_apply_add] at hs
    rwa [add_comm (homog s₁.2).choose, coe_of_mul_apply_add] at hs
  · refine Localization.induction_on₂ x y fun c d ↦ val_injective _ ?_
    by_cases hs₀ : 0 ∈ S
    · subsingleton [IsLocalization.uniqueOfZeroMem hs₀]
    have ne_zero {x} (hx : x ∈ S) : (x : A) ≠ 0 := fun hx₀ ↦ hs₀ <| hx₀ ▸ hx
    simp_rw [val_add, Localization.add_mk, Localization.liftOn_mk, val_mk,
      Localization.add_mk, decompose_add, add_apply, Submonoid.coe_mul, decompose_mul,
      Submodule.coe_add, Subtype.coe_eta]
    have : (homog (c.2 * d.2).2).choose = (homog c.2.2).choose + (homog d.2.2).choose :=
      degree_eq_of_mem_mem _ (homog (c.2 * d.2).2).choose_spec
        (mul_mem_graded (homog c.2.2).choose_spec (homog d.2.2).choose_spec) (ne_zero (c.2 * d.2).2)
    simp_rw [coe_apply_congr this, decompose_of_mem _ (homog (Subtype.prop _)).choose_spec,
      coe_of_mul_apply_add, coe_apply_congr (add_comm (homog c.2.2).choose _),
      coe_of_mul_apply_add]
    rfl
  · refine Localization.induction_on x fun d ↦ val_injective _ ?_
    obtain ⟨c, rfl⟩ := mk_surjective c
    by_cases hs₀ : 0 ∈ S
    · subsingleton [IsLocalization.uniqueOfZeroMem hs₀]
    have ne_zero {x} (hx : x ∈ S) : (x : A) ≠ 0 := fun hx₀ ↦ hs₀ <| hx₀ ▸ hx
    have : (homog (mul_mem c.den_mem d.2.2)).choose = c.deg + (homog d.2.2).choose :=
      degree_eq_of_mem_mem _ (homog (mul_mem c.den_mem d.2.2)).choose_spec
        (mul_mem_graded c.den.2 (homog d.2.2).choose_spec) (ne_zero <| mul_mem c.den_mem d.2.2)
    rw [RingHom.id_apply, Algebra.smul_def, smul_eq_mul, val_mul, algebraMap_apply, val_mk]
    simp_rw [Localization.mk_mul, Localization.liftOn_mk, val_mk, Localization.mk_mul,
      decompose_mul, decompose_of_mem _ c.num.2, coe_apply_congr this, coe_of_mul_apply_add]

variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
  (S : Submonoid A) (homog : S ≤ SetLike.homogeneousSubmonoid 𝒜)

theorem proj₀_mk (a : A) (s : S) : proj₀ 𝒜 S homog (.mk a s) =
    .mk ⟨(homog s.2).choose, DirectSum.decompose 𝒜 a _, ⟨s, (homog s.2).choose_spec⟩, s.2⟩ := rfl

@[simp] lemma proj₀_val (x : 𝒜[S⁻¹]₀) : proj₀ 𝒜 S homog x.val = x := by
  ext
  by_cases hs₀ : 0 ∈ S
  · subsingleton [IsLocalization.uniqueOfZeroMem hs₀]
  obtain ⟨x, rfl⟩ := mk_surjective x
  simp_rw [val_mk, proj₀_mk, val_mk, decompose_of_mem _ x.num.2,
    coe_apply_congr (degree_eq_of_mem_mem _ (homog x.den_mem).choose_spec x.den.2
      (mt (· ▸ x.den_mem) hs₀)), of_eq_same]

noncomputable nonrec def Away.proj₀ {i : ι} {f : A} (hf : f ∈ 𝒜 i) :
    Localization.Away (f : A) →ₗ[Away 𝒜 f] Away 𝒜 f :=
  proj₀ _ _ <| Submonoid.powers_le.mpr ⟨_, hf⟩

theorem Away.proj₀_mk {i : ι} {f : A} (hf : f ∈ 𝒜 i) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • i)) :
    proj₀ 𝒜 hf (.mk a ⟨f ^ n, n, rfl⟩) = .of _ hf n ⟨a, ha⟩ :=
  proj₀_val _ _ _ (Away.mk _ hf _ _ _)

end HomogeneousLocalization


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

/-! # localization of tensor, to be moved -/

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


-- # Algebra result

namespace HomogeneousLocalization

variable (R ι A : Type*) [CommRing R] [CommRing A] [Algebra R A] (W : Submonoid A)
  [DecidableEq ι] [AddCancelCommMonoid ι]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

instance : Algebra R 𝒜[W⁻¹]₀ where
  algebraMap := (algebraMap _ _).comp <| algebraMap R (𝒜 0)
  commutes' r x := mul_comm _ _
  smul_def' r x := HomogeneousLocalization.val_injective _ <| by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    simpa [Algebra.smul_def] using by rfl

instance : IsScalarTower R 𝒜[W⁻¹]₀ (at W) :=
  .of_algebraMap_eq' rfl

end HomogeneousLocalization

open TensorProduct

-- # Main result

namespace HomogeneousLocalization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
  (S : Type*) [CommRing S] [Algebra R S]

variable {i : ι} {f : A} (hf : f ∈ 𝒜 i)

private noncomputable def ofAwayBaseChange :
    Away (𝒜.baseChange S) (1 ⊗ₜ[R] f) →ₗ[S] S ⊗[R] Away 𝒜 f :=
  have f₁ : Away (𝒜.baseChange S) (1 ⊗ₜ[R] f) →ₐ[S]
      Localization.Away (1 ⊗ₜ f : S ⊗[R] A) := Algebra.algHom _ _ _
  have f₂ : Localization.Away (1 ⊗ₜ f : S ⊗[R] A) ≃ₐ[S]
      S ⊗[R] Localization.Away (f : A) := Localization.Away.tensorEquiv _ _ _
  have f₃ : S ⊗[R] Localization.Away (f : A) →ₗ[S] S ⊗[R] Away 𝒜 f :=
    ((Away.proj₀ 𝒜 hf).restrictScalars R).baseChange S
  f₃ ∘ₗ f₂.toLinearMap ∘ₗ f₁.toLinearMap

variable (f) in
private noncomputable def toAwayBaseChange :
    S ⊗[R] Away 𝒜 f →ₐ[S] Away (𝒜.baseChange S) (1 ⊗ₜ[R] f) :=
  AlgHom.liftBaseChange <| Away.mapₐ (GradedAlgebra.includeRight 𝒜 S) rfl

private lemma ofAwayBaseChange_apply {n : ℕ} (x : 𝒜 (n • i)) :
    ofAwayBaseChange 𝒜 S hf
      (Away.of (𝒜.baseChange S) (Submodule.tmul_mem_baseChange_of_mem _ hf) n
        (Submodule.toBaseChange S (𝒜 (n • i))
          (1 ⊗ₜ[R] x))) =
    1 ⊗ₜ[R] Away.of 𝒜 hf n x := by
  simp [ofAwayBaseChange, Algebra.algHom, Away.proj₀_mk]

private lemma toAwayBaseChange_apply {n : ℕ} (x : 𝒜 (n • i)) :
    toAwayBaseChange 𝒜 S f (1 ⊗ₜ[R] (Away.of 𝒜 hf n) x) =
    Away.of (𝒜.baseChange S) (Submodule.tmul_mem_baseChange_of_mem _ hf) n
      ((Submodule.toBaseChange S (𝒜 (n • i))) (1 ⊗ₜ[R] x)) := by
  simp [toAwayBaseChange]; rfl

private theorem toAwayBaseChange_ofAwayBaseChange :
    toAwayBaseChange 𝒜 S f ∘ₗ ofAwayBaseChange 𝒜 S hf = .id := by
  refine Away.hom_ext (𝒜.baseChange S) (Submodule.tmul_mem_baseChange_of_mem _ hf) fun n ↦ ?_
  refine (LinearMap.cancel_right (Submodule.toBaseChange_surjective _ _)).mp ?_
  ext x : 3
  simp_rw [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp, curry_apply,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.coe_coe, LinearMap.id_apply]
  conv => enter [1,2]; exact ofAwayBaseChange_apply ..
  exact toAwayBaseChange_apply ..

private theorem ofAwayBaseChange_toAwayBaseChange :
    ofAwayBaseChange 𝒜 S hf ∘ₗ toAwayBaseChange 𝒜 S f = .id := by
  ext : 2
  refine Away.hom_ext 𝒜 hf fun n ↦ ?_
  ext x
  simp_rw [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp, LinearMap.comp_apply,
    curry_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.coe_coe,
    LinearMap.id_apply, Away.mkₗ_apply]
  rw [toAwayBaseChange_apply, ofAwayBaseChange_apply]

noncomputable def awayBaseChange :
    Away (𝒜.baseChange S) ((1 : S) ⊗ₜ[R] f) ≃ₐ[S] S ⊗[R] Away 𝒜 f := .symm
  { __ := toAwayBaseChange 𝒜 S f,
    invFun := ofAwayBaseChange 𝒜 S hf,
    left_inv x := congr($(ofAwayBaseChange_toAwayBaseChange 𝒜 S hf) x),
    right_inv x := congr($(toAwayBaseChange_ofAwayBaseChange 𝒜 S hf) x) }

@[simp] lemma awayBaseChange_apply {n : ℕ} (x : 𝒜 (n • i)) :
    awayBaseChange 𝒜 S hf
      (Away.of (𝒜.baseChange S) (Submodule.tmul_mem_baseChange_of_mem _ hf) n
        (Submodule.toBaseChange S (𝒜 (n • i)) (1 ⊗ₜ[R] x))) =
    1 ⊗ₜ[R] Away.of 𝒜 hf n x :=
  ofAwayBaseChange_apply ..

@[simp] lemma awayBaseChange_symm_apply (x : Away 𝒜 f) :
    (awayBaseChange 𝒜 S hf).symm (1 ⊗ₜ[R] x) =
    Away.mapₐ (GradedAlgebra.includeRight 𝒜 S) (by rfl) x := by
  simp [awayBaseChange, toAwayBaseChange]

end HomogeneousLocalization
