/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.Lemmas
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Grassmannian

/-!
# Grassmannians

## Main definitions

- `Module.Grassmannian`: `G(k, M; R)` is the `k`ᵗʰ Grassmannian of the `R`-module
  `M`. It is defined to be the set of submodules of `M` whose quotient is locally free of rank `k`.
  Note that this indexing is the opposite of some indexing in literature, where this rank would be
  `n-k` instead, where `M=R^n`.

## TODO
- Grassmannians for schemes and quasi-coherent sheaf of modules.
- Representability.

-/

universe u v w

open CategoryTheory Limits TensorProduct Submodule

namespace Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (k : ℕ)

attribute [simp] Grassmannian.rankAtStalk_eq

namespace Grassmannian

variable {R M k}

@[simp] lemma coe_mk (N : Submodule R M) {h₁ h₂ h₃} :
    (⟨N, h₁, h₂, h₃⟩ : G(k, M; R)).toSubmodule = N := rfl

/-- An easier constructor that uses a linear equiv and instances. -/
def mk' (N : Submodule R M) (P : Type*) [AddCommGroup P] [Module R P]
    (e : (M ⧸ N) ≃ₗ[R] P) [Module.Finite R P] [Projective R P]
    (h : ∀ p, rankAtStalk (R := R) P p = k :=
      by intro p; haveI := PrimeSpectrum.nontrivial p; simp) :
    G(k, M; R) where
  toSubmodule := N
  finite_quotient := Module.Finite.equiv e.symm
  projective_quotient := Projective.of_equiv e.symm
  rankAtStalk_eq := fun p ↦ by rw [rankAtStalk_eq_of_equiv e, h]

@[simp] lemma coe_mk' (N : Submodule R M) (P : Type*) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Projective R P] (e : (M ⧸ N) ≃ₗ[R] P)
    (h : ∀ p, rankAtStalk (R := R) P p = k) :
    (mk' N P e h).toSubmodule = N :=
  rfl

variable (N : G(k, M; R))

/-- Copy of an element of the Grassmannian, with a new carrier equal to the old one. Useful to fix
definitional equalities. -/
def copy (N : G(k, M; R)) (N' : Set M) (h : N' = N) : G(k, M; R) :=
  mk' (N.toSubmodule.copy N' h) _ (quotEquivOfEq _ N (N.copy_eq _ _))

/-- Given an isomorphism `M⧸N ↠ R^k`, return an element of `G(k, M; R)`. -/
def ofEquiv (N : Submodule R M) (e : (M ⧸ N) ≃ₗ[R] (Fin k → R)) : G(k, M; R) :=
  mk' N _ e

@[simp] lemma coe_ofEquiv (N : Submodule R M) (e : (M ⧸ N) ≃ₗ[R] (Fin k → R)) :
    ofEquiv N e = N :=
  rfl

/-- Given a surjection `M ↠ R^k`, return an element of `G(k, M; R)`. -/
def ofSurjective (f : M →ₗ[R] (Fin k → R)) (hf : Function.Surjective f) : G(k, M; R) :=
  ofEquiv _ (f.quotKerEquivOfSurjective hf)

@[simp] lemma coe_ofSurjective (f : M →ₗ[R] (Fin k → R)) (hf : Function.Surjective f) :
    ofSurjective f hf = LinearMap.ker f :=
  rfl

variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]

/-- If `M₁` surjects to `M₂`, then there is an induced map `G(k, M₂; R) → G(k, M₁; R)` by
"pulling back" a submodule. -/
def ofLinearMap (f : M₁ →ₗ[R] M₂) (hf : Function.Surjective f) (N : G(k, M₂; R)) : G(k, M₁; R) :=
  mk' (N.comap f) _ (N.quotientComapLinearEquiv f hf)

@[simp] lemma coe_ofLinearMap (f : M₁ →ₗ[R] M₂) (hf : Function.Surjective f) (N : G(k, M₂; R)) :
    ofLinearMap f hf N = N.comap f :=
  rfl

/-- If `M₁` and `M₂` are isomorphic, then `G(k, M₁; R) ≃ G(k, M₂; R)`. -/
def ofLinearEquiv (e : M₁ ≃ₗ[R] M₂) : G(k, M₁; R) ≃ G(k, M₂; R) where
  toFun N := ofLinearMap e.symm e.symm.surjective N
  invFun N := ofLinearMap e e.surjective N
  left_inv N := ext <| by simp [← map_equiv_eq_comap_symm, comap_map_eq]
  right_inv N := ext <| by simp [← map_equiv_eq_comap_symm, map_comap_eq]

@[simp] lemma coe_ofLinearEquiv (e : M₁ ≃ₗ[R] M₂) (N : G(k, M₁; R)) :
    ofLinearEquiv e N = N.map e :=
  (map_equiv_eq_comap_symm e N).symm

/-- The quotients of `ofLinearEquiv` are isomorphic. -/
def ofLinearEquivEquiv (e : M₁ ≃ₗ[R] M₂) (N : G(k, M₁; R)) :
    (M₂ ⧸ (N.ofLinearEquiv e : Submodule R M₂)) ≃ₗ[R] M₁ ⧸ (N : Submodule R M₁) :=
  Quotient.equiv _ _ e.symm <| (map_comap_eq _ _).trans <| by simp

variable (R) in
/-- The affine chart corresponding to a chosen `x : R^k → M`, represented by `k` elements in `M`.
It is the quotients `q : M ↠ V` such that the composition `x ∘ q : R^k → V` is an isomorphism. -/
def chart (x : Fin k → M) : Set G(k, M; R) :=
  { N | Function.Bijective (N.mkQ ∘ Fintype.linearCombination R x) }
-- TODO: `chart f` is affine
-- Proof sketch: we have equalizer diagram `chart f → Hom[R-Mod](M,R^k) ⇒ Hom[R-Mod](R^k,R^k)`

/-- An element `N ∈ chart R f` produces an isomorphism `M ⧸ N ≃ₗ[R] R^k`. -/
noncomputable def equivOfChart {x : Fin k → M} {N : G(k, M; R)} (hn : N ∈ chart R x) :
    (M ⧸ (N : Submodule R M)) ≃ₗ[R] (Fin k → R) :=
  (LinearEquiv.ofBijective (N.mkQ ∘ₗ Fintype.linearCombination R x) hn).symm

@[simp] lemma equivOfChart_apply {x : Fin k → M} {N : G(k, M; R)} (hn : N ∈ chart R x) (i : Fin k) :
    equivOfChart hn (Submodule.Quotient.mk (x i)) = Pi.single i 1 := by
  rw [equivOfChart, LinearEquiv.symm_apply_eq]
  simp

@[simp] lemma equivOfChart_apply_apply {x : Fin k → M} {N : G(k, M; R)} (hn : N ∈ chart R x)
    (i j : Fin k) :
    equivOfChart hn (Submodule.Quotient.mk (x i)) j = if j = i then 1 else 0 := by
  rw [equivOfChart_apply, Pi.single_apply]

lemma ofEquiv_mem_chart {N : Submodule R M} (e : (M ⧸ N) ≃ₗ[R] (Fin k → R))
    (x : Fin k → M) (hx : ∀ i, e (Submodule.Quotient.mk (x i)) = Pi.single i 1) :
    ofEquiv N e ∈ chart R x := by
  rw [chart, Set.mem_setOf, ← LinearMap.coe_comp]
  convert e.symm.bijective using 1
  refine DFunLike.coe_fn_eq.2 (LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring <| Eq.symm <|
    e.symm_apply_eq.2 ?_)
  simp [hx]

lemma ofSurjective_mem_chart {q : M →ₗ[R] Fin k → R} (hq : Function.Surjective q)
    (f : Fin k → M) (hf : ∀ i, q (f i) = Pi.single i 1) :
    ofSurjective q hq ∈ chart R f :=
  ofEquiv_mem_chart _ _ hf

lemma exists_ofEquiv_mem_chart {N : Submodule R M} (e : (M ⧸ N) ≃ₗ[R] (Fin k → R)) :
    ∃ f, ofEquiv N e ∈ chart R f :=
  ⟨_, ofEquiv_mem_chart _ (fun i ↦ (e.symm (Pi.single i 1)).out) fun i ↦ by simp⟩

lemma exists_ofSurjective_mem_chart {q : M →ₗ[R] Fin k → R} (hq : Function.Surjective q) :
    ∃ f, ofSurjective q hq ∈ chart R f :=
  exists_ofEquiv_mem_chart _

variable (A : Type*) [CommRing A] [Algebra R A]

/-- Base change to an `R`-algebra `A`, where `M` is replaced with `A ⊗[R] M`. -/
noncomputable def baseChange (N : G(k, M; R)) : G(k, A ⊗[R] M; A) :=
  mk' (N.toSubmodule.baseChange A) _ (N.quotientBaseChange A) fun p ↦ by
    rw [rankAtStalk_baseChange, rankAtStalk_eq]

@[simp] lemma coe_baseChange (N : G(k, M; R)) : baseChange A N = N.toSubmodule.baseChange A := rfl

/-- The quotient of `baseChange` is isomorphic to the base change of the quotient. -/
@[simp] noncomputable def quotientBaseChangeEquiv (N : G(k, M; R)) :
    (A ⊗[R] M ⧸ (baseChange A N).toSubmodule) ≃ₗ[A] A ⊗[R] (M ⧸ N.toSubmodule) :=
  N.quotientBaseChange A

variable {A} {B : Type*} [CommRing B] [Algebra R B]

/-- Functoriality of Grassmannian in the category of `R`-algebras. Note that given an `R`-algebra
`A`, we replace `M` with `A ⊗[R] M`. The map `f : A →ₐ[R] B` should technically provide an instance
`[Algebra A B]`, but this might cause problems later down the line, so we do not require this
instance in the type signature of the function. Instead, given any instance `[Algebra A B]`, we
later prove that the map is equal to the one induced by `IsScalarTower.toAlgHom R A B : A →ₐ[R] B`.
See `map_val` and `map_eq`.
-/
noncomputable def map (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) : G(k, B ⊗[R] M; B) :=
  letI := f.toAlgebra;
  ofLinearEquiv (AlgebraTensorModule.cancelBaseChange R A B B M) (baseChange B N)

lemma coe_map (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) :
    N.map f = span B (f.toLinearMap.rTensor M '' N) := by
  letI := f.toAlgebra;
  rw [map, coe_ofLinearEquiv, coe_baseChange, baseChange_eq_span, map_span,
    map_coe, ← Set.image_comp, AlgebraTensorModule.coe_cancelBaseChange_comp_mk_one]
  rfl

lemma coe_map' (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) :
    (N.map f).toSubmodule = .span B ((N.restrictScalars R).map (f.toLinearMap.rTensor M)) :=
  coe_map f N

lemma map_eq [Algebra A B] [IsScalarTower R A B] (N : G(k, A ⊗[R] M; A)) :
    N.map (IsScalarTower.toAlgHom R A B) = ofLinearEquiv
      (AlgebraTensorModule.cancelBaseChange R A B B M) (baseChange B N) := by
  ext; rw [coe_map, coe_ofLinearEquiv, coe_baseChange, baseChange_eq_span,
    map_span, map_coe, ← Set.image_comp,
    AlgebraTensorModule.coe_cancelBaseChange_comp_mk_one]

lemma map_id (N : G(k, A ⊗[R] M; A)) : N.map (AlgHom.id R A) = N :=
  ext (by rw [coe_map, AlgHom.toLinearMap_id, LinearMap.rTensor_id, LinearMap.id_coe, Set.image_id,
    span_coe_eq_restrictScalars, restrictScalars_self])

variable {C : Type*} [CommRing C] [Algebra R C]

lemma map_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) (N : G(k, A ⊗[R] M; A)) :
    N.map (g.comp f) = (N.map f).map g := by
  refine letI := f.toAlgebra; letI := g.toAlgebra; ext ?_
  have hg : g = IsScalarTower.toAlgHom R B C := rfl
  rw [coe_map, coe_map', coe_map, hg, ← AlgebraTensorModule.cancelBaseChange_comp_mk_one',
    ← restrictScalars_map, map_span, coe_restrictScalars,
    span_span_of_tower, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_toLinearMap, AlgebraTensorModule.coe_cancelBaseChange_comp_mk_one,
    AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.coe_comp, Set.image_comp]

/-- The Grassmannian functor given a ring `R`, an `R`-module `M`, and a natural number `k`.
Given an `R`-algebra `A`, we return the set `G(k, A ⊗[R] M; A)`. -/
@[simps!] noncomputable def functor (R : CommRingCat.{u}) (M : ModuleCat.{v} R) (k : ℕ) :
    Under R ⥤ Type (max u v) where
  obj A := G(k, A ⊗[R] M; A)
  map f := map (CommRingCat.toAlgHom f)
  map_id _ := funext map_id
  map_comp f g := funext (map_comp (CommRingCat.toAlgHom f) (CommRingCat.toAlgHom g))

/-- Functoriality of `chart`. -/
lemma baseChange_mem_chart (f : Fin k → M) {N : G(k, M; R)} (hn : N ∈ chart R f) :
    N.baseChange A ∈ chart A (TensorProduct.mk R A M 1 ∘ f) := by
  convert ofEquiv_mem_chart (N.quotientBaseChange A ≪≫ₗ (equivOfChart hn).baseChange R A _ _
    ≪≫ₗ TensorProduct.piScalarRight R A A (Fin k)) ?_ (fun i ↦ ?_) using 1
  simp [Pi.single_apply_smul]

/-- Functoriality of `chart`. -/
lemma baseChange_chart_subset (f : Fin k → M) :
    baseChange A '' (chart R f) ⊆ chart A (TensorProduct.mk R A M 1 ∘ f) :=
  Set.image_subset_iff.2 fun _ ↦ baseChange_mem_chart f

/-- Functoriality of `chart`. -/
lemma map_mem_chart (f : A →ₐ[R] B) (x : Fin k → M) {N : G(k, A ⊗[R] M; A)}
    (hn : N ∈ chart A (TensorProduct.mk R A M 1 ∘ x)) :
    N.map f ∈ chart B (TensorProduct.mk R B M 1 ∘ x) := by
  letI := f.toAlgebra
  have hf : IsScalarTower.toAlgHom R A B = f := rfl
  convert ofEquiv_mem_chart ((Quotient.equiv _ _ (AlgebraTensorModule.cancelBaseChange
    R A B B M) rfl).symm ≪≫ₗ N.quotientBaseChangeEquiv B ≪≫ₗ (equivOfChart hn).baseChange
    A B _ _ ≪≫ₗ TensorProduct.piScalarRight A B B (Fin k)) _ (fun i ↦ ?_) using 1
  · rw [map]; simp [Grassmannian.ext_iff]
  simp only [Quotient.equiv_symm, quotientBaseChangeEquiv, Function.comp_apply,
    mk_apply, LinearEquiv.trans_apply, Quotient.equiv_apply, mapQ_apply,
    LinearEquiv.coe_coe, AlgebraTensorModule.cancelBaseChange_symm_tmul, piScalarRight_apply]
  conv => enter [1,2,2]; exact quotientBaseChange_apply ..
  simp only [LinearEquiv.baseChange_apply, piScalarRightHom_tmul]
  refine funext fun j ↦ ?_
  conv => enter [1,1]; exact equivOfChart_apply_apply hn i j
  rw [ite_smul, one_smul, zero_smul, Pi.single_apply]

/-- Functoriality of `chart`. -/
lemma map_chart_subset (f : A →ₐ[R] B) (x : Fin k → M) :
    map f '' (chart A (TensorProduct.mk R A M 1 ∘ x)) ⊆ chart B (TensorProduct.mk R B M 1 ∘ x) :=
  Set.image_subset_iff.2 fun _ ↦ map_mem_chart f _

/-- A subfunctor of the Grassmannian, given an indexing `x : Fin k → M`, `chart x` selects the
elements `N ∈ G(k, A ⊗[R] M; A)` such that the composition `A^k → A ⊗[R] M → (A ⊗[R] M)/N.val` is
an isomorphism. This is called `chart` because it corresponds to an affine open chart in the
Grassmannian. -/
@[simps!] noncomputable def chartFunctor (R : CommRingCat.{u}) (M : ModuleCat.{v} R) (k : ℕ)
    (x : Fin k → M) :
    Under R ⥤ Type (max u v) where
  obj A := chart A (TensorProduct.mk R A M 1 ∘ x)
  map f N := ⟨N.1.map (CommRingCat.toAlgHom f), map_mem_chart _ x N.2⟩
  map_id _ := funext fun _ ↦ Subtype.ext <| map_id ..
  map_comp _ _ := funext fun _ ↦ Subtype.ext <|
    map_comp (CommRingCat.toAlgHom _) (CommRingCat.toAlgHom _) _

/-- `chartFunctor R M k x` is a subfunctor of `Grassmannian.functor R M k`. -/
noncomputable def chartToFunctor (R : CommRingCat.{u}) (M : ModuleCat.{v} R) (k : ℕ)
    (x : Fin k → M) :
    chartFunctor R M k x ⟶ functor R M k where
  app A := Subtype.val


namespace Corepresentable

/-!
# Corepresentability of chart

We show that `chart x` is the equalizer of `Hom[R](M, R^k) ⥤ Hom[R](R^k, R^k)`.

We call `Hom[R](M, R^k)` "left" and `Hom[R](R^k, R^k)` "right".
-/

variable (R M k) (x : Fin k → M)

/-- The first module in the equaliser diagram. -/
abbrev left : Type (max u v) :=
  M →ₗ[R] (Fin k → R)

/-- The second module in the equaliser diagram. -/
abbrev right : Type u :=
  (Fin k → R) →ₗ[R] (Fin k → R)

variable {M k} in
/-- The first map `left ⟶ right`. -/
@[simp] def compose : left R M k → right R k :=
  fun f ↦ f ∘ₗ Fintype.linearCombination R x

variable {M k} in
/-- The second map `left ⟶ right`. -/
@[simp] def const1 : left R M k → right R k :=
  fun _ ↦ LinearMap.id

variable {R M k x} in
lemma surjective_of_compose_eq_const1 {f : left R M k} (h : compose R x f = const1 R f) :
    Function.Surjective f :=
  fun p ↦ ⟨Fintype.linearCombination R x p, congr($h p)⟩

/-- The isomorphism between `chart x` and the equaliser of `compose, const1 : left ⟶ right`. -/
noncomputable def chartEquivEq : chart R x ≃ {f : left R M k // compose R x f = const1 R f} where
  toFun N := ⟨equivOfChart N.2 ∘ₗ N.1.mkQ, LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring <| by simp⟩
  invFun f := ⟨ofSurjective f.1 <| surjective_of_compose_eq_const1 f.2,
    ofSurjective_mem_chart _ _ fun i ↦ by simpa using congr($(f.2) (Pi.single i 1))⟩
  left_inv N := by ext; simp
  right_inv f := Subtype.ext <| LinearMap.ext fun p ↦ (LinearEquiv.symm_apply_eq _).2 <|
    (LinearMap.quotKerEquivOfSurjective _ (surjective_of_compose_eq_const1 f.2)).injective <| by
      simpa using congr($(f.2.symm) (f.1 p))

variable {R M k} (A) in
/-- Base change of `left` from `R` to `A`. -/
def leftBaseChange (f : left R M k) : left A (A ⊗[R] M) k :=
  TensorProduct.piScalarRightHom R A A (Fin k) ∘ₗ f.baseChange A

/-- Base change of `left` from `A` to `B`. -/
def leftMap (φ : A →ₐ[R] B) (f : left A (A ⊗[R] M) k) : left B (B ⊗[R] M) k :=
  letI := φ.toAlgebra
  leftBaseChange B f ∘ₗ (AlgebraTensorModule.cancelBaseChange R A B B M).symm

variable {R M k} in
@[simp] lemma leftMap_tmul (φ : A →ₐ[R] B) (f : left A (A ⊗[R] M) k) (a : A) (m : M) (i : Fin k) :
    leftMap R M k φ f (φ a ⊗ₜ m) i = φ (f (a ⊗ₜ m) i) := by
  letI := φ.toAlgebra
  simp [leftMap, leftBaseChange, tmul_eq_smul_one_tmul a m, ← algebraMap_smul B, mul_comm,
    show algebraMap A B = φ from rfl]

@[simp] lemma leftMap_one_tmul {φ : A →ₐ[R] B} {f : left A (A ⊗[R] M) k} (m : M) (i : Fin k) :
    leftMap R M k φ f (1 ⊗ₜ m) i = φ (f (1 ⊗ₜ m) i) := by
  simpa only [map_one] using leftMap_tmul φ f 1 m i

@[simp] lemma leftMap_id : leftMap R M k (AlgHom.id R A) = id := by
  ext; simp

@[simp] lemma leftMap_comp (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) :
    leftMap R M k (ψ.comp φ) = leftMap R M k ψ ∘ leftMap R M k φ := by
  ext; simp

variable (R : CommRingCat.{u}) (M : ModuleCat.{v} R) (k : ℕ) (x : Fin k → M)

/-- `left` as a functor. -/
def leftFunctor : Under R ⥤ Type (max u v) where
  obj A := left A (A ⊗[R] M) k
  map f := leftMap R M k (CommRingCat.toAlgHom f)

end Corepresentable


end Grassmannian

end Module
