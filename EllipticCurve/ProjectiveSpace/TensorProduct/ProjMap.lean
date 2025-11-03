/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import EllipticCurve.ProjectiveSpace.Graded.Admissible
import EllipticCurve.ProjectiveSpace.Graded.AlgHom
import EllipticCurve.ProjectiveSpace.Graded.HomogeneousLocalization
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Functoriality of Proj
-/

universe u₁ u₂ u v

open GradedRingHom HomogeneousIdeal

section GradedRingHom
variable {A₁ A₂ A₃ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]
  {σ₁ σ₂ σ₃ : Type*} [SetLike σ₁ A₁] [AddSubgroupClass σ₁ A₁]
  [SetLike σ₂ A₂] [AddSubgroupClass σ₂ A₂] [SetLike σ₃ A₃] [AddSubgroupClass σ₃ A₃]
  {𝒜₁ : ℕ → σ₁} {𝒜₂ : ℕ → σ₂} {𝒜₃ : ℕ → σ₃} [GradedRing 𝒜₁] [GradedRing 𝒜₂] [GradedRing 𝒜₃]
  {F : Type*} [GradedFunLike F 𝒜₁ 𝒜₂] [RingHomClass F A₁ A₂]
  (f : F) (hf : Admissible f)

namespace ProjectiveSpectrum

@[simps] def comap.toFun (p : ProjectiveSpectrum 𝒜₂) : ProjectiveSpectrum 𝒜₁ where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
  not_irrelevant_le le := p.3 <| hf.1.trans <| HomogeneousIdeal.map_le_of_le_comap le

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

open SpecOfNotation TopologicalSpace ProjectiveSpectrum Opposite HomogeneousLocalization

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
    gradedAddHom f i a, gradedAddHom f i b, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩, ?_⟩
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
    CommRingCat.ofHom (Away.map f rfl : Away 𝒜₁ s →+* Away 𝒜₂ (f s)) ≫
      awayToSection 𝒜₂ (f s) := by
  ext x
  obtain ⟨n, x, rfl⟩ := x.of_surjective _ hs
  simp only [CommRingCat.hom_comp, smul_eq_mul, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom]
  conv => enter[2,2]; exact Away.map_of ..
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
@[reassoc] theorem awayι_comp_map {i : ℕ} (hi : 0 < i) (s : A₁) (hs : s ∈ 𝒜₁ i) :
    awayι 𝒜₂ (f s) (map_mem f hs) hi ≫ map f hf =
    Spec.map (CommRingCat.ofHom (Away.map f (by rfl))) ≫ awayι 𝒜₁ s hs hi := by
  rw [awayι, awayι, Category.assoc, ι_comp_map, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (basicOpen 𝒜₂ (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top, awayToSection_comp_appLE _ _ hs]

@[simps! I₀ f] noncomputable def mapAffineOpenCover : (Proj 𝒜₂).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan _ (fun s : (affineOpenCover 𝒜₁).I₀ ↦ f s.2)
    (fun s ↦ map_mem f s.2.2) (fun s ↦ s.1.2) <|
    (HomogeneousIdeal.toIdeal_le_toIdeal_iff.mpr hf.1).trans <|
    Ideal.map_le_of_le_comap <| (HomogeneousIdeal.irrelevant_toIdeal_le _).mpr fun i hi x hx ↦
    Ideal.subset_span ⟨⟨⟨i, hi⟩, ⟨x, hx⟩⟩, rfl⟩

@[simp] lemma away_map_comp_fromZeroRingHom (s : A₁) :
    (Away.map f rfl).comp (fromZeroRingHom 𝒜₁ (Submonoid.powers s)) =
    (fromZeroRingHom 𝒜₂ (Submonoid.powers (f s))).comp (gradedZeroRingHom f) :=
  RingHom.ext fun x ↦ by ext; simp [fromZeroRingHom, Away.map, map'_mk]

@[reassoc (attr := simp)] lemma map_comp_toSpecZero :
    map f hf ≫ toSpecZero 𝒜₁ =
    toSpecZero 𝒜₂ ≫ Spec.map (CommRingCat.ofHom (gradedZeroRingHom f)) := by
  refine (mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s ↦ ?_
  simp [awayι_comp_map_assoc _ _ s.1.2 (s.2 : A₁) s.2.2, awayι_toSpecZero, awayι_toSpecZero_assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]

@[simp] theorem map_coe' (hf : Admissible (f : 𝒜₁ →+*ᵍ 𝒜₂)) :
    map (f : 𝒜₁ →+*ᵍ 𝒜₂) hf = map f hf.of_coe := rfl

theorem map_coe : map (f : 𝒜₁ →+*ᵍ 𝒜₂) hf.coe = map f hf := rfl

theorem map_comp {g : 𝒜₂ →+*ᵍ 𝒜₃} {f : 𝒜₁ →+*ᵍ 𝒜₂} (hg : Admissible g) (hf : Admissible f) :
    map (g.comp f) (hg.comp hf) = map g hg ≫ map f hf := by
  refine (mapAffineOpenCover _ <| hg.comp hf).openCover.hom_ext _ _
    fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_X, Scheme.AffineOpenCover.openCover_f,
    mapAffineOpenCover_f]
  rw [awayι_comp_map _ _ _ _ s.2.2]
  simp only [GradedRingHom.comp_apply]
  rw [awayι_comp_map_assoc _ _ _ _ (map_mem f s.2.2), awayι_comp_map _ _ _ _ s.2.2,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  ext x : 1
  obtain ⟨n, a, ha, rfl⟩ := x.of_surjective _ s.2.2
  simp only [smul_eq_mul, RingHom.coe_comp, Function.comp_apply]
  conv => enter [2,2]; exact Away.map_of ..
  conv => enter [2]; exact Away.map_of ..
  exact Away.map_of ..

theorem map_id : map (GradedRingHom.id 𝒜₁) .id = 𝟙 (Proj 𝒜₁) := by
  refine (affineOpenCover _).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [affineOpenCover, Proj.affineOpenCoverOfIrrelevantLESpan,
    Scheme.AffineOpenCover.openCover_X, Scheme.AffineOpenCover.openCover_f, Category.comp_id]
  conv_lhs => exact awayι_comp_map (GradedRingHom.id 𝒜₁) _ _ _ s.2.2
  conv_rhs => exact (Category.id_comp _).symm
  congr 1
  rw [Spec.map_eq_id]
  ext x : 2
  obtain ⟨n, a, ha, rfl⟩ := x.of_surjective _ s.2.2
  simp only [GradedRingHom.id_apply, CommRingCat.hom_ofHom, smul_eq_mul, CommRingCat.hom_id,
    RingHom.id_apply]
  exact Away.map_of ..

@[simps] protected noncomputable def congr (e : 𝒜₁ ≃+*ᵍ 𝒜₂) : Proj 𝒜₁ ≅ Proj 𝒜₂ where
  hom := Proj.map _ e.symm.admissible
  inv := Proj.map _ e.admissible
  hom_inv_id := by
    rw [← map_coe, ← map_coe e, ← map_comp, ← map_id]
    congr 1
    simp
  inv_hom_id := by
    rw [← map_coe, ← map_coe e.symm, ← map_comp, ← map_id]
    congr 1
    simp

end AlgebraicGeometry.Proj

end GradedRingHom

section GradedAlgHom
variable {R R₁ R₂ A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
  [CommRing R₁] [CommRing R₂] [Algebra R₁ A₁] [Algebra R₂ A₂]
  [CommRing R] [Algebra R R₁] [Algebra R R₂]
  [Algebra R A₁] [Algebra R A₂] [IsScalarTower R R₁ A₁] [IsScalarTower R R₂ A₂]
  {𝒜₁ : ℕ → Submodule R₁ A₁} {𝒜₂ : ℕ → Submodule R₂ A₂} [GradedRing 𝒜₁] [GradedRing 𝒜₂]
  (f : 𝒜₁ →ₐᵍ[R] 𝒜₂) (hf : Admissible f)

namespace AlgebraicGeometry.Proj

open SpecOfNotation CategoryTheory CommRingCat

variable (𝒜₁) in
noncomputable def toSpec : Proj 𝒜₁ ⟶ Spec(R₁) :=
  toSpecZero 𝒜₁ ≫ Spec.map (ofHom <| algebraMap R₁ (𝒜₁ 0))

@[reassoc] theorem map_toSpec :
    Proj.map f hf ≫ toSpec 𝒜₁ ≫ Spec.map (ofHom <| algebraMap R R₁) =
    toSpec 𝒜₂ ≫ Spec.map (ofHom <| algebraMap R R₂) := by
  simp only [toSpec, Category.assoc, ← Spec.map_comp, ← ofHom_comp, map_comp_toSpecZero_assoc]
  congr 3; ext; simp [← IsScalarTower.algebraMap_apply]

@[reassoc (attr := simp)] theorem map_toSpec'
    [Algebra R₁ R₂] [Algebra R₁ A₂] [IsScalarTower R₁ R₂ A₂]
    (f : 𝒜₁ →ₐᵍ[R₁] 𝒜₂) (hf : Admissible f) :
    Proj.map f hf ≫ toSpec 𝒜₁ = toSpec 𝒜₂ ≫ Spec.map (ofHom <| algebraMap R₁ R₂) := by
  simp [← map_toSpec f hf]

end AlgebraicGeometry.Proj

end GradedAlgHom
