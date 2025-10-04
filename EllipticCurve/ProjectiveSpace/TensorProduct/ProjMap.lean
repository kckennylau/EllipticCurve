/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Functoriality of Proj
-/

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

end AlgebraicGeometry.Proj
