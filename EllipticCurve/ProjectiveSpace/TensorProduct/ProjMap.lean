/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.ProjectiveSpace.AlgebraHomogeneousLocalization
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Functoriality of Proj
-/

-- not `@[ext]` because `A` cannot be inferred.
theorem IsLocalization.algHom_ext {R A L B : Type*}
    [CommSemiring R] [CommSemiring A] [CommSemiring L] [CommSemiring B]
    (W : Submonoid A) [Algebra A L] [IsLocalization W L]
    [Algebra R A] [Algebra R L] [IsScalarTower R A L] [Algebra R B]
    {f g : L →ₐ[R] B} (h : f.comp (Algebra.algHom R A L) = g.comp (Algebra.algHom R A L)) :
    f = g :=
  AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext W <| RingHom.ext <| AlgHom.ext_iff.mp h

@[ext high] theorem Localization.algHom_ext {R A B : Type*}
    [CommSemiring R] [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B] (W : Submonoid A)
    {f g : Localization W →ₐ[R] B}
    (h : f.comp (Algebra.algHom R A _) = g.comp (Algebra.algHom R A _)) :
    f = g :=
  IsLocalization.algHom_ext W h

universe u v

@[simp] lemma Localization.localRingHom_mk {R P : Type*} [CommSemiring R] [CommSemiring P]
    (I : Ideal R) [I.IsPrime] (J : Ideal P) [J.IsPrime] (f : R →+* P) (hIJ : I = Ideal.comap f J)
    (x : R) (y : I.primeCompl) :
    Localization.localRingHom I J f hIJ (Localization.mk x y) =
      Localization.mk (f x) ⟨f y, by aesop⟩ := by
  simp [mk_eq_mk', localRingHom_mk']

lemma HomogeneousIdeal.toIdeal_le_toIdeal_iff {ι σ A : Type*} [Semiring A] [SetLike σ A]
    [AddSubmonoidClass σ A] (𝒜 : ι → σ) [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]
    {I J : HomogeneousIdeal 𝒜} : I.toIdeal ≤ J.toIdeal ↔ I ≤ J := Iff.rfl

variable {R : Type u} {A₁ A₂ : Type v} [CommRing R] [CommRing A₁] [CommRing A₂]
  [Algebra R A₁] [Algebra R A₂]
  (𝒜₁ : ℕ → Submodule R A₁) (𝒜₂ : ℕ → Submodule R A₂)

structure GradedAlgHom extends A₁ →ₐ[R] A₂ where
  map_mem' : ∀ ⦃n a⦄, a ∈ 𝒜₁ n → toAlgHom a ∈ 𝒜₂ n

@[inherit_doc]
notation:25 𝒜₁ " →ᵍᵃ " 𝒜₂ => GradedAlgHom 𝒜₁ 𝒜₂

namespace GradedAlgHom

variable {𝒜₁ 𝒜₂}

theorem toAlgHom_injective : Function.Injective (toAlgHom : (𝒜₁ →ᵍᵃ 𝒜₂) → (A₁ →ₐ[R] A₂)) := by
  rintro ⟨_⟩ _ h
  congr

instance funLike : FunLike (𝒜₁ →ᵍᵃ 𝒜₂) A₁ A₂ where
  coe f := f.toFun
  coe_injective' _ _ h := toAlgHom_injective <| AlgHom.coe_fn_injective h

instance algHomClass : AlgHomClass (𝒜₁ →ᵍᵃ 𝒜₂) R A₁ A₂ where
  map_mul f := f.map_mul
  map_add f := f.map_add
  map_one f := f.map_one
  map_zero f := f.map_zero
  commutes f := f.commutes

variable (f : 𝒜₁ →ᵍᵃ 𝒜₂)

@[simp] lemma coe_toAlgHom : (f.toAlgHom : A₁ → A₂) = f := rfl

lemma map_mem {n : ℕ} {a : A₁} (ha : a ∈ 𝒜₁ n) : f a ∈ 𝒜₂ n :=
  f.map_mem' ha

@[simps] def linearMap (n : ℕ) : 𝒜₁ n →ₗ[R] 𝒜₂ n where
  toFun a := ⟨f a, f.map_mem a.2⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

@[simp] lemma decompose_map [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂] {x : A₁} :
    DirectSum.decompose 𝒜₂ (f x) = .map (fun n ↦ f.linearMap n) (.decompose 𝒜₁ x) := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜₁ x, map_sum, DirectSum.decompose_sum,
    DirectSum.decompose_sum, map_sum]
  congr 1
  ext n : 1
  rw [DirectSum.decompose_of_mem _ (f.map_mem (Subtype.prop _)),
    DirectSum.decompose_of_mem _ (Subtype.prop _), DirectSum.map_of]
  rfl

lemma map_coe_decompose [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂] {x : A₁} {n : ℕ} :
    f (DirectSum.decompose 𝒜₁ x n) = DirectSum.decompose 𝒜₂ (f x) n := by
  simp

end GradedAlgHom

namespace HomogeneousIdeal

variable {𝒜₁ 𝒜₂} [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂] (f : 𝒜₁ →ᵍᵃ 𝒜₂)

@[simp] lemma coe_toIdeal (I : HomogeneousIdeal 𝒜₁) : (I.toIdeal : Set A₁) = I := rfl

def map (I : HomogeneousIdeal 𝒜₁) : HomogeneousIdeal 𝒜₂ where
  __ := I.toIdeal.map f
  is_homogeneous' n a ha := by
    rw [Ideal.map] at ha
    induction ha using Submodule.span_induction generalizing n with
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      rw [← f.map_coe_decompose]
      exact Ideal.mem_map_of_mem _ (I.2 _ ha)
    | zero => simp
    | add => simp [*, Ideal.add_mem]
    | smul a₁ a₂ ha₂ ih =>
      classical rw [smul_eq_mul, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
      exact sum_mem fun ij hij ↦ Ideal.mul_mem_left _ _ <| ih _

def comap (I : HomogeneousIdeal 𝒜₂) : HomogeneousIdeal 𝒜₁ where
  __ := I.toIdeal.comap f
  is_homogeneous' n a ha := by
    rw [Ideal.mem_comap, HomogeneousIdeal.mem_iff, f.map_coe_decompose]
    exact I.2 _ ha

variable {f}

lemma coe_comap (I : HomogeneousIdeal 𝒜₂) : (I.comap f : Set A₁) = f ⁻¹' I := rfl

lemma map_le_iff_le_comap {I : HomogeneousIdeal 𝒜₁} {J : HomogeneousIdeal 𝒜₂} :
    I.map f ≤ J ↔ I ≤ J.comap f :=
  Ideal.map_le_iff_le_comap
alias ⟨le_comap_of_map_le, map_le_of_le_comap⟩ := map_le_iff_le_comap

theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦
  map_le_iff_le_comap

end HomogeneousIdeal

namespace HomogeneousLocalization

variable {𝒜₁ 𝒜₂} [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂] (f : 𝒜₁ →ᵍᵃ 𝒜₂)

noncomputable def localRingHom (I : Ideal A₁) [I.IsPrime] (J : Ideal A₂) [J.IsPrime]
    (hIJ : I = J.comap f) :
    AtPrime 𝒜₁ I →+* AtPrime 𝒜₂ J :=
  map _ _ f (Localization.le_comap_primeCompl_iff.mpr <| hIJ ▸ le_rfl) f.2

variable (I : Ideal A₁) [I.IsPrime] (J : Ideal A₂) [J.IsPrime] (hIJ : I = J.comap f)

@[simp] lemma val_localRingHom (x : AtPrime 𝒜₁ I) :
    (localRingHom f I J hIJ x).val = Localization.localRingHom _ _ f hIJ x.val := by
  obtain ⟨⟨i, x, s, hs⟩, rfl⟩ := x.mk_surjective
  simp [localRingHom, map_mk]

instance isLocalHom_localRingHom : IsLocalHom (localRingHom f I J hIJ) where
  map_nonunit x hx := by
    rw [← isUnit_iff_isUnit_val] at hx ⊢
    rw [val_localRingHom] at hx
    exact IsLocalHom.map_nonunit _ hx

@[simps] def NumDenSameDeg.map {W₁ : Submonoid A₁} {W₂ : Submonoid A₂}
    (hw : W₁ ≤ W₂.comap f) (c : NumDenSameDeg 𝒜₁ W₁) : NumDenSameDeg 𝒜₂ W₂ where
  deg := c.deg
  den := f.linearMap _ c.den
  num := f.linearMap _ c.num
  den_mem := hw c.den_mem

lemma localRingHom_mk (c : NumDenSameDeg 𝒜₁ I.primeCompl) :
    localRingHom f I J hIJ (.mk c) =
      .mk (c.map f <| hIJ ▸ by rfl) := by
  rfl

def lof {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (S : Submonoid A) {i : ι} (d : 𝒜 i) (hd : ↑d ∈ S) :
    𝒜 i →ₗ[R] HomogeneousLocalization 𝒜 S where
  toFun x := mk ⟨i, x, d, hd⟩
  map_add' x y := by ext; simp [Localization.add_mk_self]
  map_smul' c x := by ext; simp [Localization.smul_mk]

nonrec def Away.lof {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i : ι} {f : A} (hf : f ∈ 𝒜 i) (n : ℕ) :
    𝒜 (n • i) →ₗ[R] HomogeneousLocalization.Away 𝒜 f :=
  lof _ _ ⟨f ^ n, SetLike.pow_mem_graded _ hf⟩ ⟨n, rfl⟩

@[simp] lemma Away.val_lof
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i : ι} {f : A} (hf : f ∈ 𝒜 i) (n : ℕ) (a : 𝒜 (n • i)) :
    (lof _ hf n a).val = .mk a ⟨f ^ n, n, rfl⟩ := rfl

lemma Away.lof_surjective
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i : ι} {f : A} (hf : f ∈ 𝒜 i) (x : Away 𝒜 f) :
    ∃ (n : ℕ) (a : 𝒜 (n • i)), lof _ hf n a = x := by
  obtain ⟨n, a, ha, rfl⟩ := x.mk_surjective _ hf
  exact ⟨n, ⟨a, ha⟩, rfl⟩

open NumDenSameDeg in
def mapₐ {R R₁ R₂ A₁ A₂ : Type*}
    [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [Algebra R R₁] [Algebra R₁ A₁] [Algebra R A₁] [IsScalarTower R R₁ A₁]
    [Algebra R R₂] [Algebra R₂ A₂] [Algebra R A₂] [IsScalarTower R R₂ A₂]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
    {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
    {𝒮₁ : Submonoid A₁} {𝒮₂ : Submonoid A₂}
    (g : A₁ →ₐ[R] A₂) (comap_le : 𝒮₁ ≤ Submonoid.comap g 𝒮₂)
    (hg : ∀ ⦃i⦄, ∀ a ∈ 𝒜₁ i, g a ∈ 𝒜₂ i) :
    HomogeneousLocalization 𝒜₁ 𝒮₁ →ₐ[R] HomogeneousLocalization 𝒜₂ 𝒮₂ where
  toFun := Quotient.map'
    (fun x ↦ ⟨x.deg, ⟨_, hg _ x.num.2⟩, ⟨_, hg _ x.den.2⟩, comap_le x.den_mem⟩)
    fun x y (e : x.embedding = y.embedding) ↦ by
      apply_fun IsLocalization.map (Localization 𝒮₂) (g : A₁ →+* A₂) comap_le at e
      simp_rw [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
        IsLocalization.map_mk', ← Localization.mk_eq_mk'] at e
      exact e
  map_add' := Quotient.ind₂' fun x y ↦ by
    simp only [← mk_add, Quotient.map'_mk'', num_add, map_add, map_mul, den_add]; rfl
  map_mul' := Quotient.ind₂' fun x y ↦ by
    simp only [← mk_mul, Quotient.map'_mk'', num_mul, map_mul, den_mul]; rfl
  map_zero' := by simp only [← mk_zero (𝒜 := 𝒜₁), Quotient.map'_mk'', deg_zero,
    num_zero, ZeroMemClass.coe_zero, map_zero, den_zero, map_one]; rfl
  map_one' := by simp only [← mk_one (𝒜 := 𝒜₁), Quotient.map'_mk'',
    num_one, den_one, map_one]; rfl
  commutes' r := by ext; simp [fromZeroRingHom]

@[simp] lemma mapₐ_mk {R R₁ R₂ A₁ A₂ : Type*}
    [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [Algebra R R₁] [Algebra R₁ A₁] [Algebra R A₁] [IsScalarTower R R₁ A₁]
    [Algebra R R₂] [Algebra R₂ A₂] [Algebra R A₂] [IsScalarTower R R₂ A₂]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
    {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
    {𝒮₁ : Submonoid A₁} {𝒮₂ : Submonoid A₂}
    (g : A₁ →ₐ[R] A₂) (comap_le : 𝒮₁ ≤ Submonoid.comap g 𝒮₂)
    (hg : ∀ ⦃i⦄, ∀ a ∈ 𝒜₁ i, g a ∈ 𝒜₂ i)
    (c : NumDenSameDeg 𝒜₁ 𝒮₁) :
    HomogeneousLocalization.mapₐ g comap_le hg (mk c) =
    mk ⟨c.deg, ⟨_, hg _ c.num.2⟩, ⟨_, hg _ c.den.2⟩, comap_le c.den_mem⟩ := rfl

def Away.mapₐ {R R₁ R₂ A₁ A₂ : Type*}
    [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [Algebra R R₁] [Algebra R₁ A₁] [Algebra R A₁] [IsScalarTower R R₁ A₁]
    [Algebra R R₂] [Algebra R₂ A₂] [Algebra R A₂] [IsScalarTower R R₂ A₂]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
    {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
    {f₁ : A₁} {f₂ : A₂} (g : A₁ →ₐ[R] A₂) (hg : ∀ ⦃i⦄, ∀ a ∈ 𝒜₁ i, g a ∈ 𝒜₂ i)
    (hgf : g f₁ = f₂) :
    HomogeneousLocalization.Away 𝒜₁ f₁ →ₐ[R] HomogeneousLocalization.Away 𝒜₂ f₂ :=
  HomogeneousLocalization.mapₐ g (Submonoid.powers_le.mpr ⟨1, by simp [hgf]⟩) hg

@[simp] lemma Away.mapₐ_mk {R R₁ R₂ A₁ A₂ : Type*}
    [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [Algebra R R₁] [Algebra R₁ A₁] [Algebra R A₁] [IsScalarTower R R₁ A₁]
    [Algebra R R₂] [Algebra R₂ A₂] [Algebra R A₂] [IsScalarTower R R₂ A₂]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
    {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
    {f₁ : A₁} {f₂ : A₂} (g : A₁ →ₐ[R] A₂) (hg : ∀ ⦃i⦄, ∀ a ∈ 𝒜₁ i, g a ∈ 𝒜₂ i)
    (hgf : g f₁ = f₂) {d : ι} (hf : f₁ ∈ 𝒜₁ d) (n : ℕ) (a : A₁) (ha : a ∈ 𝒜₁ (n • d)) :
    mapₐ g hg hgf (.mk _ hf n a ha) = .mk _ (hgf ▸ hg _ hf) n (g a) (hg _ ha) := by
  simp [mapₐ, Away.mk, hgf]

@[simp] lemma Away.mapₐ_lof {R R₁ R₂ A₁ A₂ : Type*}
    [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [Algebra R R₁] [Algebra R₁ A₁] [Algebra R A₁] [IsScalarTower R R₁ A₁]
    [Algebra R R₂] [Algebra R₂ A₂] [Algebra R A₂] [IsScalarTower R R₂ A₂]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
    {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
    {d : ι} {f₁ : A₁} (hf : f₁ ∈ 𝒜₁ d) {f₂ : A₂}
    (g : A₁ →ₐ[R] A₂) (hg : ∀ ⦃i⦄, ∀ a ∈ 𝒜₁ i, g a ∈ 𝒜₂ i)
    (hgf : g f₁ = f₂) (n : ℕ) (a : 𝒜₁ (n • d)) :
    mapₐ g hg hgf (lof _ hf n a) = lof _ (hgf ▸ hg _ hf) n ⟨g a, hg _ a.2⟩ :=
  mapₐ_mk _ _ _ hf _ _ _

end HomogeneousLocalization


variable {𝒜₁ 𝒜₂} [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂] (f : 𝒜₁ →ᵍᵃ 𝒜₂)
  (hf : HomogeneousIdeal.irrelevant 𝒜₂ ≤ (HomogeneousIdeal.irrelevant 𝒜₁).map f)

namespace ProjectiveSpectrum

@[simps] def comap.toFun (p : ProjectiveSpectrum 𝒜₂) : ProjectiveSpectrum 𝒜₁ where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
  not_irrelevant_le le := p.3 <| hf.trans <| HomogeneousIdeal.map_le_of_le_comap le

def comap : C(ProjectiveSpectrum 𝒜₂, ProjectiveSpectrum 𝒜₁) where
  toFun := comap.toFun f hf
  continuous_toFun := by
    simp only [continuous_iff_isClosed, isClosed_iff_zeroLocus]
    rintro _ ⟨s, rfl⟩
    refine ⟨f '' s, ?_⟩
    ext x
    simp only [mem_zeroLocus, Set.image_subset_iff, Set.mem_preimage, mem_zeroLocus,
      comap.toFun_asHomogeneousIdeal, HomogeneousIdeal.coe_comap]

end ProjectiveSpectrum

namespace AlgebraicGeometry.Proj

open TopologicalSpace ProjectiveSpectrum Opposite HomogeneousLocalization

namespace StructureSheaf

variable (U : Opens (ProjectiveSpectrum 𝒜₁)) (V : Opens (ProjectiveSpectrum 𝒜₂))
  (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)

noncomputable def comapFun (s : ∀ x : U, AtPrime 𝒜₁ x.1.1.1) (y : V) :
    AtPrime 𝒜₂ y.1.1.1 :=
  localRingHom f _ y.1.1.1 rfl <| s ⟨.comap f hf y.1, hUV y.2⟩

lemma isLocallyFraction_comapFun
    (s : ∀ x : U, AtPrime 𝒜₁ x.1.1.1)
    (hs : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜₁).pred s) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜₂).pred
      (comapFun f hf U (unop (op V)) hUV ↑s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨.comap f hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (ProjectiveSpectrum.comap f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
    f.linearMap i a, f.linearMap i b, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩, ?_⟩
  rintro ⟨q, ⟨hqW, hqV⟩⟩
  ext
  specialize h_frac ⟨_, hqW⟩
  simp_all [comapFun]

noncomputable def comap :
    (Proj.structureSheaf 𝒜₁).1.obj (op U) →+* (Proj.structureSheaf 𝒜₂).1.obj (op V) where
  toFun s := ⟨comapFun _ _ _ _ hUV s.1, isLocallyFraction_comapFun _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [comapFun]
  map_zero' := by ext; simp [comapFun]
  map_add' x y := by ext; simp [comapFun]
  map_mul' x y := by ext; simp [comapFun]

end StructureSheaf

open CategoryTheory

@[simps (isSimp := false)] noncomputable def sheafedSpaceMap :
    Proj.toSheafedSpace 𝒜₂ ⟶ Proj.toSheafedSpace 𝒜₁ where
  base := TopCat.ofHom <| ProjectiveSpectrum.comap f hf
  c := { app U := CommRingCat.ofHom <| StructureSheaf.comap f hf _ _ Set.Subset.rfl }

@[simp] lemma germ_map_sectionInBasicOpen {p : ProjectiveSpectrum 𝒜₂}
    (c : NumDenSameDeg 𝒜₁ (p.comap f hf).1.toIdeal.primeCompl) :
    (toSheafedSpace 𝒜₂).presheaf.germ
      ((Opens.map (sheafedSpaceMap f hf).base).obj _) p (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMap f hf).c.app _ (sectionInBasicOpen 𝒜₁ _ c)) =
    (toSheafedSpace 𝒜₂).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4
      (sectionInBasicOpen 𝒜₂ p (c.map _ le_rfl)) :=
  rfl

@[simp] lemma val_sectionInBasicOpen_apply (p : ProjectiveSpectrum.top 𝒜₁)
    (c : NumDenSameDeg 𝒜₁ p.1.toIdeal.primeCompl)
    (q : ProjectiveSpectrum.basicOpen 𝒜₁ c.den) :
    ((sectionInBasicOpen 𝒜₁ p c).val q).val = .mk c.num ⟨c.den, q.2⟩ :=
  rfl

@[elementwise] theorem localRingHom_comp_stalkIso (p : ProjectiveSpectrum 𝒜₂) :
    (stalkIso 𝒜₁ (ProjectiveSpectrum.comap f hf p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫
        (stalkIso 𝒜₂ p).inv =
      (sheafedSpaceMap f hf).stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_apply, RingHom.coe_coe]
  -- I sincerely apologise for your eyes.
  erw [stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germ_map_sectionInBasicOpen]
  erw [stalkIso'_germ]
  simp

noncomputable def map : Proj 𝒜₂ ⟶ Proj 𝒜₁ where
  __ := sheafedSpaceMap f hf
  prop p := .mk fun x hx ↦ by
    rw [← localRingHom_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (stalkIso 𝒜₂ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (stalkIso 𝒜₁ (p.comap f hf)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

@[simp] theorem map_preimage_basicOpen (s : A₁) :
    map f hf ⁻¹ᵁ basicOpen 𝒜₁ s = basicOpen 𝒜₂ (f s) :=
  rfl

theorem ι_comp_map (s : A₁) :
    (basicOpen 𝒜₂ (f s)).ι ≫ map f hf =
    (map f hf).resLE _ _ le_rfl ≫ (basicOpen 𝒜₁ s).ι := by
  simp

/-- Given `f, g : X ⟶ Spec(R)`, if the two induced maps `R ⟶ Γ(X)` are equal, then `f = g`. -/
lemma _root_.AlgebraicGeometry.ext_to_Spec {X : Scheme} {R : Type*} [CommRing R]
    {f g : X ⟶ Spec(R)}
    (h : (Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map f.op =
      (Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map g.op) :
    f = g :=
  (ΓSpec.adjunction.homEquiv X (op <| .of R)).symm.injective <| unop_injective h

lemma _root_.AlgebraicGeometry.Γ_map_Spec_map_ΓSpecIso_inv
    {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    Scheme.Γ.map (Spec.map f).op ((Scheme.ΓSpecIso R).inv x) = (Scheme.ΓSpecIso S).inv (f x) :=
  congr($((Scheme.ΓSpecIso_inv_naturality f).symm) x)

@[simp] lemma _root_.AlgebraicGeometry.Scheme.resLE_app_top
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) {h} :
    (f.resLE V U h).app ⊤ =
    V.topIso.hom ≫ f.appLE V U h ≫ U.topIso.inv := by
  simp [Scheme.Hom.resLE]

@[simp] lemma awayToSection_comp_appLE {i : ℕ} {s : A₁} (hs : s ∈ 𝒜₁ i) :
    awayToSection 𝒜₁ s ≫
      Scheme.Hom.appLE (map f hf) (basicOpen 𝒜₁ s) (basicOpen 𝒜₂ (f s)) (by rfl) =
    CommRingCat.ofHom (Away.mapₐ f f.2 rfl : Away 𝒜₁ s →ₐ[R] Away 𝒜₂ (f s)) ≫
      awayToSection 𝒜₂ (f s) := by
  ext x
  obtain ⟨n, x, rfl⟩ := x.lof_surjective _ hs
  simp only [CommRingCat.hom_comp, smul_eq_mul, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, RingHom.coe_coe]
  conv => enter[2,2]; exact Away.mapₐ_lof _ _ _ _ _ _
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

/--
The following square commutes:
```
Proj 𝒜₂         ⟶ Proj 𝒜₁
    ^                   ^
    |                   |
Spec A₂[f(s)⁻¹]₀ ⟶ Spec A₁[s⁻¹]₀
```
-/
theorem awayι_comp_map {i : ℕ} (hi : 0 < i) (s : A₁) (hs : s ∈ 𝒜₁ i) :
    awayι 𝒜₂ (f s) (f.2 hs) hi ≫ map f hf =
    Spec.map (CommRingCat.ofHom (Away.mapₐ f f.2 (by rfl)).toRingHom) ≫ awayι 𝒜₁ s hs hi := by
  rw [awayι, awayι, Category.assoc, ι_comp_map, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (basicOpen 𝒜₂ (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top, awayToSection_comp_appLE _ _ hs]

end AlgebraicGeometry.Proj
