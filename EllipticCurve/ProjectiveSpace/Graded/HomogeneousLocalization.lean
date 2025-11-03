/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.ProjectiveSpace.Graded.AlgHom
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

namespace SetLike.GradeZero

instance instAlgebra' {ι R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [DecidableEq ι] [AddMonoid ι] (𝒜 : ι → Submodule R A) [GradedMonoid 𝒜]
    (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R] [Algebra R₀ A] [IsScalarTower R₀ R A] :
    Algebra R₀ (𝒜 0) where
  algebraMap := (algebraMap R (𝒜 0)).comp (algebraMap R₀ R)
  commutes' _ _ := Algebra.commutes (algebraMap R₀ R _) _
  smul_def' r x := Subtype.ext <| by
    rw [SetLike.val_smul_of_tower, ← algebraMap_smul R, Algebra.smul_def]; rfl

variable {ι R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [DecidableEq ι] [AddMonoid ι] (𝒜 : ι → Submodule R A) [GradedMonoid 𝒜]
  (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R] [Algebra R₀ A] [IsScalarTower R₀ R A]

instance instIsScalarTower₁ : IsScalarTower R₀ R (𝒜 0) where
  smul_assoc x y z := by simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_assoc]

instance instIsScalarTower₂ : IsScalarTower R₀ (𝒜 0) A where
  smul_assoc _ _ _ := Algebra.smul_mul_assoc ..

@[simp] theorem algebraMap_coe
    (x : R₀) : algebraMap R₀ (𝒜 0) x = algebraMap R₀ A x :=
  (IsScalarTower.algebraMap_apply ..).symm

end SetLike.GradeZero

@[simp] theorem Localization.localRingHom_mk {R : Type*} [CommSemiring R]
    {P : Type*} [CommSemiring P]
    (I : Ideal R) [hI : I.IsPrime] (J : Ideal P) [J.IsPrime]
    (f : R →+* P) (hIJ : I = Ideal.comap f J) (x : R) (y : ↥I.primeCompl) :
    (localRingHom I J f hIJ) (mk x y) =
      mk (f x) ⟨f y, le_comap_primeCompl_iff.mpr (ge_of_eq hIJ) y.2⟩ := by
  simp [mk_eq_mk', localRingHom_mk']

namespace HomogeneousLocalization

open SetLike

section Algebra

@[simp] lemma val_fromZeroRingHom {ι A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A]
    [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜] (x : Submonoid A) (f : 𝒜 0) :
    (fromZeroRingHom 𝒜 x f).val = .mk f 1 :=
  rfl

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [DecidableEq ι] [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedRing 𝒜] (x : Submonoid A)
  (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R] [Algebra R₀ A] [IsScalarTower R₀ R A]

instance : SMul R₀ (HomogeneousLocalization 𝒜 x) :=
  have : SMulMemClass (Submodule R A) R₀ A := SMulMemClass.ofIsScalarTower ..
  inferInstance

instance : Algebra R₀ (HomogeneousLocalization 𝒜 x) where
  algebraMap := (fromZeroRingHom 𝒜 x).comp <| algebraMap R₀ (𝒜 0)
  commutes' _ _ := mul_comm _ _
  smul_def' r z := by
    obtain ⟨z, rfl⟩ := z.mk_surjective
    ext
    simp [Localization.smul_mk, Localization.mk_mul, ← Algebra.smul_def]

instance : Module R₀ (HomogeneousLocalization 𝒜 x) :=
  inferInstance

lemma algebraMap_apply' {r : R₀} : algebraMap R₀ (HomogeneousLocalization 𝒜 x) r =
    fromZeroRingHom 𝒜 x (algebraMap R₀ (𝒜 0) r) := rfl

instance : IsScalarTower R₀ R (HomogeneousLocalization 𝒜 x) :=
  .of_algebraMap_eq' rfl

end Algebra

section GradedRing
variable {ι A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [DecidableEq ι] [AddCommMonoid ι]
  (𝒜 : ι → σ) [GradedRing 𝒜] {s : Submonoid A} {f : A}

-- bundled AddHom
def of {i : ι} {d : 𝒜 i} (hd : ↑d ∈ s) : 𝒜 i →+ HomogeneousLocalization 𝒜 s where
  toFun x := mk ⟨i, x, d, hd⟩
  map_add' x y := by ext; simp [Localization.add_mk_self]
  map_zero' := by ext; simp [Localization.mk_zero]

namespace Away
variable {i : ι} (hf : f ∈ 𝒜 i) (n : ℕ)

-- bundled AddHom, default constructor
nonrec def of : 𝒜 (n • i) →+ Away 𝒜 f :=
  of 𝒜 (d := ⟨f ^ n, SetLike.pow_mem_graded _ hf⟩) ⟨n, rfl⟩

@[simp] theorem val_of (a : 𝒜 (n • i)) : (of 𝒜 hf n a).val = .mk a ⟨f ^ n, n, rfl⟩ := rfl

theorem of_surjective {i : ι} (hf : f ∈ 𝒜 i) (x : Away 𝒜 f) :
    ∃ n num, of 𝒜 hf n num = x :=
  let ⟨n, num, num_mem, hx⟩ := x.mk_surjective 𝒜 hf; ⟨n, ⟨num, num_mem⟩, hx⟩

end Away

end GradedRing

section GradedAlgebra
variable {ι R A : Type*}
variable [DecidableEq ι] [AddCommMonoid ι]
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
variable {x : Submonoid A}

/-- Given a denominator `den : 𝒜 i`, we have a linear map `𝒜 i → HomogeneousLocalization 𝒜 x` that
sends `n` to `n/den`. -/
def mkₗ {i : ι} {den : 𝒜 i} (den_mem : (den : A) ∈ x) :
    𝒜 i →ₗ[R] HomogeneousLocalization 𝒜 x where
  toFun num := mk ⟨_, num, den, den_mem⟩
  map_add' _ _ := by ext; simp [Localization.add_mk_self]
  map_smul' _ _ := by ext; simp [Localization.smul_mk]

@[simp] lemma mkₗ_apply {i : ι} {den : 𝒜 i} (den_mem : (den : A) ∈ x) (n : 𝒜 i) :
    mkₗ 𝒜 den_mem n = of 𝒜 den_mem n := rfl

/-- Given `n : ℕ`, we have a linear map `𝒜 (n • d) → HomogeneousLocalization 𝒜 x` that sends `x`
to `x / f ^ n`. -/
nonrec def Away.mkₗ {f : A} {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ) :
    𝒜 (n • d) →ₗ[R] HomogeneousLocalization.Away 𝒜 f :=
  mkₗ 𝒜 (den := ⟨f ^ n, pow_mem_graded _ hf⟩) ⟨n, rfl⟩

@[simp] lemma Away.mkₗ_apply {f : A} {d : ι} (hf : f ∈ 𝒜 d) {n : ℕ} (x : 𝒜 (n • d)) :
    Away.mkₗ 𝒜 hf n x = .of 𝒜 hf n x := rfl

theorem Away.hom_ext {f : A} {d : ι} (hf : f ∈ 𝒜 d)
    {M : Type*} [AddCommGroup M] [Module R M] {g₁ g₂ : Away 𝒜 f →ₗ[R] M}
    (h : ∀ n, g₁ ∘ₗ Away.mkₗ 𝒜 hf n = g₂ ∘ₗ Away.mkₗ 𝒜 hf n) : g₁ = g₂ :=
  LinearMap.ext fun x ↦ let ⟨n, num, hx⟩ := x.of_surjective 𝒜 hf; hx ▸ congr($(h n) num)

end GradedAlgebra

section GradedRingHom
variable {ι A₁ A₂ σ₁ σ₂ : Type*} [CommRing A₁] [CommRing A₂]
  [SetLike σ₁ A₁] [AddSubgroupClass σ₁ A₁] [SetLike σ₂ A₂] [AddSubgroupClass σ₂ A₂]
  [DecidableEq ι] [AddCommMonoid ι]
  {𝒜₁ : ι → σ₁} [GradedRing 𝒜₁] {𝒜₂ : ι → σ₂} [GradedRing 𝒜₂]
  {F : Type*} [GradedFunLike F 𝒜₁ 𝒜₂] [RingHomClass F A₁ A₂] (f : F)

section
variable {P : Submonoid A₁} {Q : Submonoid A₂} (comap_le : P ≤ Q.comap f)

def map' : HomogeneousLocalization 𝒜₁ P →+* HomogeneousLocalization 𝒜₂ Q :=
  map _ _ f comap_le fun _ _ ↦ map_mem f

lemma map'_mk (c : NumDenSameDeg 𝒜₁ P) :
    map' f comap_le (mk c) =
    mk ⟨c.deg, ⟨_, map_mem f c.num.2⟩, ⟨_, map_mem f c.den.2⟩, comap_le c.den_mem⟩ := rfl

end

namespace Away
variable {x₁ : A₁} {x₂ : A₂} (hfx : f x₁ = x₂)

def map : Away 𝒜₁ x₁ →+* Away 𝒜₂ x₂ :=
  map' f <| Submonoid.powers_le.mpr ⟨1, by simp [hfx]⟩

@[simp] lemma map_of {d : ι} (hx : x₁ ∈ 𝒜₁ d) (n : ℕ) (a : 𝒜₁ (n • d)) :
    map f hfx (.of 𝒜₁ hx n a) = .of 𝒜₂ (hfx ▸ map_mem f hx) n (gradedAddHom f (n • d) a) := by
  simp [map, of, HomogeneousLocalization.of, map'_mk, gradedAddHom, hfx]

-- lemma val_map {d : ι} (hx : x₁ ∈ 𝒜₁ d) (a : Away 𝒜₁ x₁) :
--     (map f hfx a).val = Localization.awayLift ((algebraMap _ _).comp f.toRingHom) _
--       (IsLocalization.map_units (M := .powers x₂) _ ⟨f x₁, 1, hfx ▸ pow_one _⟩) a.val := by
--   obtain ⟨n, a, ha, rfl⟩ := a.of_surjective _ hx
--   simp [Localization.awayLift_mk]

end Away

noncomputable def localRingHom (I : Ideal A₁) [I.IsPrime] (J : Ideal A₂) [J.IsPrime]
    (hIJ : I = J.comap f) :
    AtPrime 𝒜₁ I →+* AtPrime 𝒜₂ J :=
  map' f <| (Localization.le_comap_primeCompl_iff (f := RingHomClass.toRingHom f)).mpr <|
    hIJ ▸ le_rfl

variable (I : Ideal A₁) [I.IsPrime] (J : Ideal A₂) [J.IsPrime] (hIJ : I = J.comap f)

@[simp] lemma val_localRingHom (x : AtPrime 𝒜₁ I) :
    (localRingHom f I J hIJ x).val = Localization.localRingHom _ _ f hIJ x.val := by
  obtain ⟨⟨i, x, s, hs⟩, rfl⟩ := x.mk_surjective
  simp [localRingHom, map'_mk]

instance isLocalHom_localRingHom : IsLocalHom (localRingHom f I J hIJ) where
  map_nonunit x hx := by
    rw [← isUnit_iff_isUnit_val] at hx ⊢
    rw [val_localRingHom] at hx
    exact IsLocalHom.map_nonunit _ hx

@[simps] def NumDenSameDeg.map {W₁ : Submonoid A₁} {W₂ : Submonoid A₂}
    (hw : W₁ ≤ W₂.comap f) (c : NumDenSameDeg 𝒜₁ W₁) : NumDenSameDeg 𝒜₂ W₂ where
  deg := c.deg
  den := gradedAddHom f _ c.den
  num := gradedAddHom f _ c.num
  den_mem := hw c.den_mem

lemma localRingHom_mk (c : NumDenSameDeg 𝒜₁ I.primeCompl) :
    localRingHom f I J hIJ (.mk c) =
      .mk (c.map f <| hIJ ▸ by rfl) := by
  rfl

end GradedRingHom

section GradedAlgHom

variable {R R₁ R₂ A₁ A₂ : Type*}
  [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
  [Algebra R R₁] [Algebra R₁ A₁] [Algebra R A₁] [IsScalarTower R R₁ A₁]
  [Algebra R R₂] [Algebra R₂ A₂] [Algebra R A₂] [IsScalarTower R R₂ A₂]
  {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
  {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
  {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
  (g : 𝒜₁ →ₐᵍ[R] 𝒜₂) {𝒮₁ : Submonoid A₁} {𝒮₂ : Submonoid A₂}
  (comap_le : 𝒮₁ ≤ Submonoid.comap g 𝒮₂)

open NumDenSameDeg in
def mapₐ : HomogeneousLocalization 𝒜₁ 𝒮₁ →ₐ[R] HomogeneousLocalization 𝒜₂ 𝒮₂ where
  __ := map' g comap_le
  commutes' r := by ext; simp [map'_mk, algebraMap_apply', fromZeroRingHom]

@[simp] lemma mapₐ_mk (c : NumDenSameDeg 𝒜₁ 𝒮₁) :
    HomogeneousLocalization.mapₐ g comap_le (mk c) =
    mk ⟨c.deg, ⟨_, g.2 c.num.2⟩, ⟨_, g.2 c.den.2⟩, comap_le c.den_mem⟩ := rfl

variable {f₁ : A₁} {f₂ : A₂} (hgf : g f₁ = f₂)

def Away.mapₐ : HomogeneousLocalization.Away 𝒜₁ f₁ →ₐ[R] HomogeneousLocalization.Away 𝒜₂ f₂ :=
  HomogeneousLocalization.mapₐ g (Submonoid.powers_le.mpr ⟨1, by simp [hgf]⟩)

@[simp] lemma Away.mapₐ_mk {d : ι} (hf : f₁ ∈ 𝒜₁ d) (n : ℕ) (a : A₁) (ha : a ∈ 𝒜₁ (n • d)) :
    mapₐ g hgf (.mk _ hf n a ha) = .mk _ (hgf ▸ g.2 hf) n (g a) (g.2 ha) := by
  simp [mapₐ, Away.mk, hgf]

@[simp] lemma Away.mapₐ_of {d : ι} (hf : f₁ ∈ 𝒜₁ d) (n : ℕ) (a : 𝒜₁ (n • d)) :
    mapₐ g hgf (of _ hf n a) = of _ (hgf ▸ g.2 hf) n ⟨g a, g.2 a.2⟩ :=
  mapₐ_mk _ _ hf _ _ _

end GradedAlgHom

end HomogeneousLocalization
