/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import EllipticCurve.ProjectiveSpace.TensorProduct.Admissible
import EllipticCurve.ProjectiveSpace.TensorProduct.HomogeneousLocalization
import EllipticCurve.ProjectiveSpace.TensorProduct.ProjMap
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Proj of tensor product

In this file we show `Proj (S ⊗[R] 𝒜) ≅ Spec S ×_R Proj 𝒜` where `𝒜` is a graded `R`-algebra.
-/

universe u

namespace AlgebraicGeometry
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
  (S : Type u) [CommRing S] [Algebra R S]

open SpecOfNotation CategoryTheory Limits CommRingCat HomogeneousLocalization TensorProduct

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

namespace Proj

noncomputable def baseChangeIsoComponent {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) :
    Spec(HomogeneousLocalization.Away (𝒜.baseChange S) (1 ⊗ₜ[R] f)) ≅
    pullback (Spec.map (ofHom (algebraMap R S)))
      (Spec.map (ofHom (algebraMap R (HomogeneousLocalization.Away 𝒜 f)))) :=
  Scheme.Spec.mapIso (awayBaseChange 𝒜 S hf).toCommRingCatIso.op.symm ≪≫
  (pullbackSpecIso _ _ _).symm

@[reassoc (attr := simp)] lemma baseChangeIsoComponent_hom_comp_pullback_fst
    {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) :
    (baseChangeIsoComponent 𝒜 S hf).hom ≫ pullback.fst _ _ =
    Spec.map (ofHom (algebraMap S _)) := by
  simp only [baseChangeIsoComponent, Scheme.Spec_obj, AlgEquiv.toRingEquiv_eq_coe,
    Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv,
    RingEquiv.toCommRingCatIso_inv, Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc]
  conv => enter [1,2]; exact pullbackSpecIso_inv_fst ..
  simp only [← Spec.map_comp, ← ofHom_comp]
  congr 2; ext s
  simp [← AlgEquiv.symm_toRingEquiv, tmul_eq_smul_one_tmul s, ← Localization.smul_mk,
    ← Algebra.TensorProduct.one_def, Localization.mk_one, algebraMap_apply']

@[reassoc (attr := simp)] lemma baseChangeIsoComponent_hom_comp_pullback_snd
    {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) :
    (baseChangeIsoComponent 𝒜 S hf).hom ≫ pullback.snd _ _ =
    Spec.map (ofHom (Away.mapₐ (GradedAlgebra.includeRight 𝒜 S) (f₂ := 1 ⊗ₜ[R] f) rfl)) := by
  simp only [baseChangeIsoComponent,
    Scheme.Spec_obj, AlgEquiv.toRingEquiv_eq_coe, Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.op_inv, RingEquiv.toCommRingCatIso_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, Category.assoc]
  conv => enter [1,2]; exact pullbackSpecIso_inv_snd ..
  rw [← Spec.map_comp, ← ofHom_comp]
  congr 2; ext x : 1
  simp [← AlgEquiv.symm_toRingEquiv]

@[reassoc (attr := simp)] lemma awayι_comp_toSpec
    {i : ℕ} (hi : 0 < i) {s : A} (hs : s ∈ 𝒜 i) :
    awayι 𝒜 s hs hi ≫ toSpec 𝒜 = Spec.map (ofHom (algebraMap _ _)) := by
  simp only [toSpec, awayι_toSpecZero_assoc, ← Spec.map_comp]; rfl

end Proj

noncomputable def ofProjTensor :
    Proj (𝒜.baseChange S) ⟶
    pullback (Spec.map (ofHom (algebraMap R S))) (Proj.toSpec 𝒜) :=
  pullback.lift (Proj.toSpec _) (Proj.map _ <| .includeRight 𝒜 S) <| by simp

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
    Proj.awayι (𝒜.baseChange S) (1 ⊗ₜ s) (Submodule.tmul_mem_baseChange_of_mem _ hs) hi ≫
      ofProjTensor 𝒜 S =
    (Proj.baseChangeIsoComponent 𝒜 S hs).hom ≫
      pullback.map _ _ _ _ (𝟙 _) (Proj.awayι _ s hs hi) (𝟙 _) (by simp) (by simp) :=
  pullback.hom_ext (by simp [ofProjTensor]) <| by
    simpa [ofProjTensor] using Proj.awayι_comp_map _ (.includeRight 𝒜 S) hi s hs


/-- To check if `f : X ⟶ Y` is an isomorphism, one can supply an open cover of `X` and an open
cover of `Y` (indexed by the same set `S`), and then maps `f_i : U_i ⟶ V_i` for `i : S` that are
iso such that the squares commute. -/
theorem isIso_of_cover {X Y : Scheme.{u}} (f : X ⟶ Y)
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
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ?_, inferInstance⟩
      obtain ⟨i, x, rfl⟩ := U.exists_eq x
      obtain ⟨i, rfl⟩ := hu i
      exact ⟨i, x, rfl⟩ }
  let V' : Y.OpenCover :=
  { I₀ := ι
    X i := V.X (iV i)
    f i := V.f (iV i)
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ?_, inferInstance⟩
      obtain ⟨i, x, rfl⟩ := V.exists_eq x
      obtain ⟨i, rfl⟩ := hv i
      exact ⟨i, x, rfl⟩ }
  let inv : Y ⟶ X := V'.glueMorphisms (fun i : ι ↦ inv (φ i) ≫ U'.f i) fun i₁ i₂ : ι ↦ by
    let p : pullback (V'.f i₁) (V'.f i₂) ⟶ pullback (U'.f i₁) (U'.f i₂) :=
      IsOpenImmersion.lift (pullback.fst _ _) (pullback.fst _ _ ≫ inv (φ i₁)) <| by
        rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, SetLike.coe_subset_coe,
          Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_comp,
          Scheme.Hom.opensRange_pullbackFst, Scheme.image_inv',
          ← Scheme.Hom.comp_preimage, ← hfφ, Scheme.Hom.comp_preimage, preimage]
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

namespace Proj

noncomputable def openCoverBaseChange :
    (Proj (𝒜.baseChange S)).AffineOpenCover :=
  Proj.mapAffineOpenCover _ <| .includeRight 𝒜 S

noncomputable def openCoverPullback :
    (pullback (Spec.map (ofHom (algebraMap R S))) (Proj.toSpec 𝒜)).OpenCover :=
  (Scheme.Pullback.openCoverOfRight (Proj.affineOpenCover 𝒜).openCover
      (Spec.map <| ofHom <| algebraMap R S) (Proj.toSpec 𝒜)).copy
    (Proj.affineOpenCover 𝒜).I₀
    (fun f ↦ pullback (Spec.map (ofHom (algebraMap R S)))
      (Spec.map (ofHom (algebraMap R (HomogeneousLocalization.Away 𝒜 (f.2 : A))))))
    (fun f ↦ pullback.map _ _ _ _ (𝟙 _) (Proj.awayι 𝒜 (f.2 : A) f.2.2 f.1.2) (𝟙 _) (by simp)
      (by simp))
    (Equiv.refl _) (fun _ ↦ pullback.congrHom rfl
      (by simp [affineOpenCover, affineOpenCoverOfIrrelevantLESpan]))
    fun f ↦ pullback.hom_ext (by simp)
      (by simp [Proj.affineOpenCover, Proj.affineOpenCoverOfIrrelevantLESpan])

@[simp] lemma opensRange_openCoverPullback {f} :
    ((Proj.openCoverPullback 𝒜 S).f f).opensRange =
    pullback.snd (Spec.map (ofHom (algebraMap R S))) (toSpec 𝒜) ⁻¹ᵁ basicOpen _ f.2 :=
  TopologicalSpace.Opens.ext <| by
    simp [openCoverPullback, Scheme.Pullback.range_map, ← Proj.opensRange_awayι _ _ f.2.2]

instance : IsIso (ofProjTensor 𝒜 S) :=
  isIso_of_cover _ (openCoverBaseChange 𝒜 S).openCover
    (openCoverPullback 𝒜 S)
    id Function.surjective_id id Function.surjective_id
    (fun f ↦ (Proj.baseChangeIsoComponent 𝒜 S f.2.2).hom)
    (fun f ↦ by simp [openCoverBaseChange, openCoverPullback, GradedAlgebra.includeRight])
    fun f ↦ by simp [← Scheme.Hom.comp_preimage, - TopologicalSpace.Opens.map_comp_obj,
      ofProjTensor, Proj.openCoverBaseChange, Proj.opensRange_awayι]
-- TODO: GradedAlgebra.includeRight simps

end Proj

-- https://math.arizona.edu/~cais/CourseNotes/AlgGeom04/notes216.pdf
noncomputable def projTensorProduct : Proj (𝒜.baseChange S) ≅
    pullback (Spec.map (ofHom (algebraMap R S))) (Proj.toSpec 𝒜) :=
  asIso <| ofProjTensor 𝒜 S

@[simp] lemma projTensorProduct_hom_comp_pullback_fst :
    (projTensorProduct 𝒜 S).hom ≫ pullback.fst _ _ = Proj.toSpec _ := by
  simp [projTensorProduct, ofProjTensor]

@[simp] lemma projTensorProduct_hom_comp_pullback_snd :
    (projTensorProduct 𝒜 S).hom ≫ pullback.snd _ _ =
    Proj.map _ (.includeRight 𝒜 S) := by
  simp [projTensorProduct, ofProjTensor]

@[simp] lemma awayι_comp_projTensorProduct {i : ℕ} (hi : 0 < i) {s : A} (hs : s ∈ 𝒜 i) :
    Proj.awayι (𝒜.baseChange S) (1 ⊗ₜ s) (Submodule.tmul_mem_baseChange_of_mem _ hs)
      hi ≫ (projTensorProduct 𝒜 S).hom =
    (Proj.baseChangeIsoComponent 𝒜 S hs).hom ≫
      pullback.map _ _ _ _ (𝟙 _) (Proj.awayι _ s hs hi) (𝟙 _) (by simp) (by simp) :=
  awayι_comp_ofProjTensor _ _ _ _

@[simp] lemma projTensorProduct_image_basicOpen {s : A} :
    (projTensorProduct 𝒜 S).hom ''ᵁ (Proj.basicOpen (𝒜.baseChange S) (1 ⊗ₜ s)) =
    pullback.snd (Spec.map (ofHom (algebraMap R S))) (Proj.toSpec 𝒜) ⁻¹ᵁ Proj.basicOpen 𝒜 s := by
  rw [Scheme.image_eq_iff_eq_preimage, ← Scheme.Hom.comp_preimage,
    projTensorProduct_hom_comp_pullback_snd, Proj.map_preimage_basicOpen,
    GradedAlgebra.includeRight]; rfl

end AlgebraicGeometry
