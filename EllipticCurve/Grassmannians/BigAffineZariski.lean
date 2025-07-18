/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

-- import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# The Big Zariski Site on Affine Schemes

In this file we define the Zariski topology on the category of affine schemes.
-/

universe u v

open CategoryTheory Functor Opposite Category Limits

set_option linter.unusedVariables false in
def Canon (R : Type u) (S : Type v) : Type v := S

namespace Canon

variable (R : Type u) (S : Type v)

def of (x : S) : Canon R S := x
def down (x : Canon R S) : S := x

instance [Semiring S] : Semiring (Canon R S) :=
  inferInstanceAs (Semiring S)

@[simps] def ringEquiv [Semiring S] : Canon R S ≃+* S where
  toFun := down R S
  invFun := of R S
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

instance [CommSemiring S] : CommSemiring (Canon R S) :=
  inferInstanceAs (CommSemiring S)

instance [Ring S] : Ring (Canon R S) :=
  inferInstanceAs (Ring S)

instance [CommRing S] : CommRing (Canon R S) :=
  inferInstanceAs (CommRing S)

instance [Field S] : Field (Canon R S) :=
  inferInstanceAs (Field S)

def toCanon [CommSemiring R] [Semiring S] [Algebra R S] : R →+* Canon R S :=
  _root_.algebraMap R S

instance [CommSemiring R] [Semiring S] [Algebra R S] :
    Algebra R (Canon R S) where
  algebraMap := toCanon R S
  smul r x := toCanon R S r * x
  commutes' r x := Algebra.commutes r (show S from x)
  smul_def' _ _ := rfl

example [CommSemiring R] [CommSemiring S] [Algebra R S] :
    (algebraMap R (Canon R S)).toAlgebra = inferInstanceAs (Algebra R (Canon R S)) :=
  rfl

def algEquiv [CommSemiring R] [CommSemiring S] [Algebra R S] :
    Canon R S ≃ₐ[R] S :=
  AlgEquiv.ofRingEquiv (f := ringEquiv R S) fun _ ↦ rfl

instance [CommSemiring R] [CommSemiring S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    IsLocalization M (Canon R S) :=
  IsLocalization.isLocalization_of_algEquiv M (algEquiv R S).symm

end Canon


open AlgebraicGeometry AffineScheme Scheme TensorProduct

namespace CommRingCat

/-- A scheme is covered by affines. -/
instance : IsCoverDense (equivCommRingCat.inverse ⋙ forgetToScheme) Scheme.zariskiTopology.{u} where
  is_cover X := ⟨.ofArrows (Spec ∘ X.affineOpenCover.obj) X.affineOpenCover.map,
    ⟨X.affineOpenCover.openCover, rfl⟩,
    fun _ u ⟨j⟩ ↦ ⟨⟨op (X.affineOpenCover.obj j), 𝟙 _, X.affineOpenCover.map j, by rw [id_comp]⟩⟩⟩

/-- The Zariski topology on the opposite category of commutative rings, constructed using the
induced topology from the Zariski topology on the category of schemes. -/
def zariskiTopology : GrothendieckTopology CommRingCat.{u}ᵒᵖ :=
  inducedTopology (equivCommRingCat.inverse ⋙ forgetToScheme) Scheme.zariskiTopology

structure StandardSystem (R : Type u) [CommRing R] : Type (u+1) where
  J : Type
  fintype : Fintype J := by infer_instance
  elem : J → R
  span_eq_top : Ideal.span (Set.range elem) = ⊤
  loc : J → Type u
  commRing : ∀ j, CommRing (loc j) := by infer_instance
  algebra : ∀ j, Algebra R (loc j) := by infer_instance
  away : ∀ j, IsLocalization.Away (elem j) (loc j) := by infer_instance

namespace StandardSystem

attribute [simp] fintype span_eq_top
attribute [instance] fintype commRing algebra away

@[simp] abbrev obj {R : Type u} [CommRing R] (s : StandardSystem R) (j : s.J) : CommRingCatᵒᵖ :=
  op (of (s.loc j))

@[simp]
abbrev hom {R : Type u} [CommRing R] (s : StandardSystem R) (j : s.J) : s.obj j ⟶ op (of R) :=
  op (ofHom (algebraMap R (s.loc j)))

/-- A standard cover of Spec R by Spec R_{fᵢ} where {fᵢ}ᵢ is a finite set that generates the unit
ideal of R. -/
inductive cover {R : Type u} [CommRing R] (s : StandardSystem R) : Presieve (op (of R)) where
  | mk (j : s.J) : cover s (s.hom j)

abbrev ofIsIso {R S : CommRingCat.{u}ᵒᵖ} (f : S ⟶ R) [IsIso f] : StandardSystem ↑(unop R) where
  J := Unit
  elem j := 1
  span_eq_top := by rw [Set.range_const, Ideal.span_singleton_one]
  loc j := ↑(unop S)
  algebra j := f.unop.hom.toAlgebra
  away j := letI := f.unop.hom.toAlgebra; haveI := isIso_unop f;
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      (by convert (CategoryTheory.isIso_iff_bijective ((forget CommRingCat).map f.unop)).1 <|
        inferInstance)

-- MOVE
@[ext] lemma _root_.Presieve.ext {C : Type u} [Category C] {X : C} {p q : Presieve X}
    (h : ∀ (Y : C) (u : Y ⟶ X), p u ↔ q u) : p = q :=
  funext fun Y ↦ funext fun f ↦ propext <| h Y f

@[simp] lemma ofIsIso_cover {R S : CommRingCat.{u}ᵒᵖ} (f : S ⟶ R) [IsIso f] :
    (ofIsIso f).cover = Presieve.singleton f := by
  ext Y u; constructor
  · rintro ⟨j⟩; exact ⟨⟩
  · rintro ⟨⟩; exact ⟨()⟩

noncomputable abbrev baseChange {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (s : StandardSystem R)
    (loc' : s.J → Type u) [∀ j, CommRing (loc' j)] [∀ j, Algebra S (loc' j)]
    [∀ j : s.J, IsLocalization.Away (f (s.elem j)) (loc' j)] :
    StandardSystem S where
  J := s.J
  elem j := f (s.elem j)
  span_eq_top := by rw [Set.range_comp', ← Ideal.map_span, s.span_eq_top, Ideal.map_top]
  loc := loc'

inductive _root_.Presieve.pullbackArrows' {C : Type u} [Category C] {X Y : C} (f : Y ⟶ X)
    (R : Presieve X) (cone : ∀ Z, ∀ (u : Z ⟶ X), R u → PullbackCone u f) : Presieve Y where
  | mk (Z : C) (u : Z ⟶ X) (h : R u) : pullbackArrows' f R cone (cone Z u h).snd

noncomputable def _root_.CommRingCat.pullbackConeOp {X Y Z : CommRingCat.{u}ᵒᵖ}
    (f : X ⟶ Z) (g : Y ⟶ Z) : PullbackCone f g :=
  letI := f.unop.hom.toAlgebra
  letI := g.unop.hom.toAlgebra
  PullbackCone.mk (W := op (of (Canon X.unop (X.unop ⊗[Z.unop] Y.unop))))
    (op (ofHom (algebraMap _ _)))
    (op (ofHom Algebra.TensorProduct.includeRight.toRingHom))
    congr(op (ofHom $Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap))

instance (C : Type u) [Category.{v} C] : Trans (Iso (C := C)) Iso Iso where
  trans := Iso.trans

noncomputable def _root_.CommRingCat.pullbackConeOpIsoPullback {X Y Z : CommRingCat.{u}ᵒᵖ}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    letI := f.unop.hom.toAlgebra
    letI := g.unop.hom.toAlgebra
    pullbackConeOp f g ≅ (pushoutCocone Z.unop X.unop Y.unop).op :=
  PullbackCone.ext (Iso.op (RingEquiv.toCommRingCatIso (Canon.ringEquiv _ _).symm))

noncomputable def _root_.CommRingCat.pullbackConeOpIsLimit {X Y Z : CommRingCat.{u}ᵒᵖ}
    (f : X ⟶ Z) (g : Y ⟶ Z) : IsLimit (pullbackConeOp f g) :=
  letI := f.unop.hom.toAlgebra
  letI := g.unop.hom.toAlgebra
  have := IsColimit.coconePointUniqueUpToIso (pushout.isColimit _ _)
      (pushoutCoconeIsColimit Z.unop X.unop Y.unop)
  .ofIsoLimit (PushoutCocone.isColimitEquivIsLimitOp _ <| pushoutCoconeIsColimit _ _ _)
    (pullbackConeOpIsoPullback f g).symm

noncomputable def _root_.CommRingCat.pullbackConeOpIso {X Y Z : CommRingCat.{u}ᵒᵖ}
    (f : X ⟶ Z) (g : Y ⟶ Z) : (pullbackConeOp f g).pt ≅ pullback f g :=
  (pullbackConeOpIsLimit f g).conePointUniqueUpToIso (limit.isLimit _)

@[simp] lemma baseChange_cover {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (s : StandardSystem R) :
    letI := f.toAlgebra;
    (s.baseChange (algebraMap R S) fun j ↦ Canon S (S ⊗[R] Canon R (s.loc j))).cover =
      Presieve.pullbackArrows' (op (ofHom f)) s.cover fun _ u _ ↦
        (pullbackConeOp (op (ofHom f)) u).flip := by
  letI := f.toAlgebra
  have : f = algebraMap R S := rfl; rw [this]
  ext Y u; constructor
  · rintro ⟨j⟩; exact ⟨s.obj j, s.hom j, ⟨_⟩⟩
  · rintro ⟨_, _, ⟨j⟩⟩; exact ⟨_⟩


section Bind

variable {R : Type u} [CommRing R] (s : StandardSystem R)
  (t : (j : s.J) → StandardSystem (s.loc j))
  (j : s.J) (tj : StandardSystem (s.loc j)) (k : tj.J)

noncomputable def bindElem : R :=
  (IsLocalization.Away.sec (s.elem j) (tj.elem k)).1

lemma associated_bindElem :
    Associated (algebraMap R (s.loc j) (bindElem s j tj k)) (tj.elem k) := by
  unfold bindElem
  rw [← IsLocalization.Away.sec_spec, map_pow]
  exact associated_mul_unit_left _ _ (.pow _ <| IsLocalization.Away.algebraMap_isUnit _)

instance : IsLocalization.Away (algebraMap R (s.loc j) (bindElem s j tj k)) (tj.loc k) :=
  IsLocalization.Away.of_associated (associated_bindElem s j tj k).symm

theorem span_map_bindElem_eq_top :
    Ideal.span (Set.range (algebraMap R (s.loc j) ∘ bindElem s j tj)) = ⊤ := by
  rw [eq_top_iff, ← tj.span_eq_top, Ideal.span_le, Set.range_subset_iff]
  exact fun k ↦ let ⟨u, hu⟩ := associated_bindElem s j tj k
    hu ▸ Ideal.mul_mem_right _ _ (Ideal.subset_span <| Set.mem_range_self _)

theorem exists_pow_mem_span_bindElem :
    ∃ n : ℕ, s.elem j ^ n ∈ Ideal.span (Set.range (bindElem s j tj)) := by
  have := span_map_bindElem_eq_top s j tj
  rw [Ideal.eq_top_iff_one, Set.range_comp, ← Ideal.map_span, ← map_one (algebraMap R (s.loc j)),
    IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (s.elem j))] at this
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := this
  exact ⟨n, by simpa using hn⟩

theorem exists_pow_mem_span_mul_bindElem :
    ∃ n : ℕ, s.elem j ^ n ∈ Ideal.span (Set.range fun k : tj.J ↦ s.elem j * bindElem s j tj k) := by
  obtain ⟨n, hn⟩ := exists_pow_mem_span_bindElem s j tj
  refine ⟨n + 1, ?_⟩
  rw [pow_succ']
  convert Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hn
  rw [Ideal.span_mul_span', Set.singleton_mul, ← Set.range_comp]
  rfl

theorem span_bindElem_eq_top :
    Ideal.span (Set.range fun jk : (j : s.J) × (t j).J ↦
      s.elem jk.fst * s.bindElem jk.fst (t jk.fst) jk.snd) = ⊤ := by
  have (j : s.J) := exists_pow_mem_span_mul_bindElem s j (t j)
  choose n hn using this
  rw [eq_top_iff, ← Ideal.span_pow_eq_top _ s.span_eq_top (∑ j : s.J, n j), Ideal.span_le,
    ← Set.range_comp, Set.range_subset_iff]
  refine fun j ↦ Ideal.mem_of_dvd _ ?_ (Ideal.span_mono ?_ (hn j))
  · exact pow_dvd_pow _ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _))
  · exact Set.range_subset_iff.2 fun k ↦ ⟨⟨j, k⟩, rfl⟩

noncomputable abbrev bind [∀ j k, Algebra R ((t j).loc k)]
    [∀ j k, IsScalarTower R (s.loc j) ((t j).loc k)] :
    StandardSystem R where
  J := (j : s.J) × (t j).J
  elem j := s.elem j.fst * s.bindElem j.fst (t j.fst) j.snd
  span_eq_top := span_bindElem_eq_top s t
  loc j := ((t j.fst).loc j.snd)
  away j := IsLocalization.Away.mul' (s.loc j.fst) _ _ _

theorem bind_cover (t'' : ∀ (Y : CommRingCatᵒᵖ) (u : Y ⟶ op (of R)), s.cover u →
      StandardSystem (Y.unop))
    (ht : ∀ j, t'' (s.obj j) (s.hom j) (cover.mk j) = t j)
    [∀ j k, Algebra R ((t j).loc k)]
    [∀ j k, IsScalarTower R (s.loc j) ((t j).loc k)] :
    (s.bind t).cover = s.cover.bind fun Y u hu ↦ (t'' Y u hu).cover := by
  ext Y u; constructor
  · rintro ⟨⟨j, k⟩⟩
    refine ⟨_, (t j).hom k, s.hom j, cover.mk j, ?_, ?_⟩
    · simp only [ht]; exact ⟨k⟩
    · have := IsScalarTower.algebraMap_eq R (s.loc j) ((t j).loc k)
      exact congr(op (ofHom $this.symm))
  · rintro ⟨Z, v, _, ⟨j⟩, ⟨k⟩, rfl⟩
    revert k
    rw [ht]
    intro k
    convert cover.mk (s := s.bind t) ⟨j, k⟩
    have := IsScalarTower.algebraMap_eq R (s.loc j) ((t j).loc k)
    exact congr(op (ofHom $this.symm))

end Bind

end StandardSystem

open StandardSystem

def standardPretopology : Pretopology CommRingCat.{u}ᵒᵖ where
  coverings R := { u : Presieve R | ∃ (s : StandardSystem ↑(unop R)), s.cover = u }
  has_isos R S f _ := ⟨ofIsIso f, ofIsIso_cover f⟩
  pullbacks R S u := by
    rintro _ ⟨s, rfl⟩
    letI := u.unop.hom.toAlgebra
    let e (j : s.J) : pullback (s.hom j) u ≅
        op (of (Canon S.unop (S.unop ⊗[R.unop] Canon R.unop (s.loc j)))) :=
      (pullbackSymmetry _ _).trans (pullbackConeOpIso u (s.hom j)).symm
    letI (j : s.J) := (pullback.snd (s.hom j) u).unop.hom.toAlgebra
    letI (j : s.J) := (e j).hom.unop.hom.toAlgebra
    have h (j : s.J) : (e j).hom ≫ (pullbackConeOp u (s.hom j)).fst = pullback.snd (s.hom j) u := by
      unfold e pullbackConeOpIso
      rw [Iso.trans_hom, assoc, Iso.symm_hom, IsLimit.conePointUniqueUpToIso_inv_comp,
        pullbackSymmetry, IsLimit.conePointUniqueUpToIso_hom_comp]
      rfl
    haveI (j : s.J) : IsScalarTower (S.unop)
        (Canon S.unop (S.unop ⊗[R.unop] Canon R.unop (s.loc j)))
        (pullback (s.hom j) u).unop :=
      .of_algebraMap_eq' congr((unop $((h j).symm)).hom)
    let t := (s.baseChange (algebraMap R.unop S.unop) fun j : s.J ↦
      Canon S.unop (S.unop ⊗[R.unop] Canon R.unop (s.loc j))).bind fun j : s.J ↦
        ofIsIso (e j).hom
    use t; ext Y v; constructor
    · rintro ⟨j, ⟨⟩⟩
      exact ⟨s.obj j, s.hom j, ⟨_⟩⟩
    · rintro ⟨_, _, ⟨j⟩⟩
      exact cover.mk (s := t) ⟨j, Unit.unit⟩
  transitive := by
    rintro R _ t'' ⟨s, rfl⟩ ht'
    choose t' ht using ht'
    let t (j : s.J) : StandardSystem (s.loc j) := t' (s.hom j) (cover.mk j)
    letI (j : s.J) (k : (t j).J) : Algebra (unop R).1 ((t j).loc k) :=
      Algebra.compHom _ (algebraMap (unop R).1 (s.loc j))
    have (j : s.J) (k : (t j).J) : IsScalarTower (↑(unop R)) (s.loc j) ((t j).loc k) :=
      .of_algebraMap_eq fun r ↦ rfl
    use s.bind t
    convert s.bind_cover t t' (fun j ↦ rfl); exact (ht _ _).symm

end CommRingCat
