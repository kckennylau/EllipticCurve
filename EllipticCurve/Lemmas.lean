/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.GroupTheory.Congruence.Hom
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Fin.Basic

/-!
# Lemmas for Mathlib

These are small lemmas that can be immediatly PR'ed to Mathlib.
-/

universe u v w

namespace Con

variable (M : Type*) {N : Type*} {P : Type*}
variable {M}
variable [MulOneClass M] [MulOneClass N] [MulOneClass P] {c : Con M}

/-- Extensionality for maps `f, g : M⧸~ →* N`: they are equal if their composition with
`mk' : M → M⧸~` are equal. -/
@[to_additive (attr := ext) "Extensionality for maps `f, g : M⧸~ →+ N`: they are equal if their
composition with `mk' : M → M⧸~` are equal."]
lemma hom_ext {f g : c.Quotient →* P} (h : f.comp (mk' c) = g.comp (mk' c)) : f = g :=
  lift_funext _ _ fun x ↦ DFunLike.congr_fun h x

end Con


namespace Fin

open Equiv Function

variable {M : Type*} {i j : ℕ} (f : Fin i → M) (g : Fin j → M)

@[simp] lemma append_update_left (c : Fin i) (x : M)
    [DecidableEq (Fin i)] [DecidableEq (Fin (i + j))] :
    (append (update f c x) g : _ → M) = update (append f g) (c.castAdd j) x := by
  refine funext fun p ↦ p.addCases (fun p ↦ ?_) fun p ↦ ?_
  · rw [append_left, update_apply, update_apply, append_left]
    exact ite_congr (by rw [castAdd_inj]) (fun _ ↦ rfl) fun _ ↦ rfl
  · rw [append_right, update_apply,
      if_neg (by rw [Fin.ext_iff]; simpa using by omega), append_right]

@[simp] lemma append_update_right (c : Fin j) (x : M)
    [DecidableEq (Fin j)] [DecidableEq (Fin (i + j))] :
    (append f (update g c x) : _ → M) = update (append f g) (c.natAdd i) x := by
  refine funext fun p ↦ p.addCases (fun p ↦ ?_) fun p ↦ ?_
  · rw [append_left, update_apply,
      if_neg (by rw [Fin.ext_iff]; simpa using by omega), append_left]
  · rw [append_right, update_apply, update_apply, append_right]
    exact ite_congr (by rw [natAdd_inj]) (fun _ ↦ rfl) fun _ ↦ rfl

lemma lastCases_update_left {n : ℕ} {M : Fin (n + 1) → Type*}
    (p q : M (Fin.last n)) (v : (i : Fin n) → M i.castSucc) (j : Fin (n + 1)) :
    lastCases p v j = update (lastCases q v) (Fin.last n) p j :=
  j.lastCases (by simp) fun j ↦ by simp

@[simp] lemma update_last {n : ℕ} [DecidableEq (Fin (n + 1))]
    {M : Fin (n + 1) → Type*} (v : (i : _) → M i) (i : Fin n) (x : M i.castSucc) :
    update v i.castSucc x (last n) = v (last n) := by
  simp [update, Fin.ext_iff, show n ≠ ↑i from ne_of_gt i.2]

@[simp] lemma update_castSucc {n : ℕ} [DecidableEq (Fin (n + 1))]
    {M : Fin (n + 1) → Type*} (v : (i : _) → M i) (i : Fin n) (x : M i.castSucc) (j : Fin n) :
    update v i.castSucc x j.castSucc = update (fun c : Fin n ↦ v c.castSucc) i x j := by
  simp only [update, castSucc_inj]
  split_ifs with h
  · subst h; rfl
  · rfl

@[simp] lemma lastCases_update_right {n : ℕ} [DecidableEq (Fin n)] {M : Fin (n + 1) → Type*}
    (p : M (Fin.last n)) (v : (i : Fin n) → M i.castSucc) (i : Fin n) (x : M i.castSucc)
    (j : Fin (n + 1)) :
    lastCases p (update v i x) j = update (lastCases p v) i.castSucc x j := by
  refine j.lastCases ?_ fun j ↦ ?_
  · simp
  · simpa using by congr

@[simp] lemma lastCases_last_castSucc {n : ℕ} {M : Fin (n + 1) → Type*} (v : (i : _) → M i) :
    lastCases (v (Fin.last n)) (fun i ↦ v i.castSucc) = v :=
  funext <| lastCases (by simp) (by simp)

variable (e₁ : Perm (Fin i)) (e₂ : Perm (Fin j))

def permAdd : Perm (Fin (i + j)) :=
  finSumFinEquiv.permCongr (e₁.sumCongr e₂)

@[simp] lemma permAdd_left (x : Fin i) : permAdd e₁ e₂ (x.castAdd j) = (e₁ x).castAdd j := by
  simp [permAdd]

@[simp] lemma permAdd_right (x : Fin j) : permAdd e₁ e₂ (x.natAdd i) = (e₂ x).natAdd i := by
  simp [permAdd]

end Fin

open Submodule

lemma Finsupp.image_lift (R : Type*) [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {X : Type*} (f : X → M) : LinearMap.range (lift M R X f) = .span R (Set.range f) := by
  refine le_antisymm (LinearMap.range_le_iff_comap.2 <| eq_top_iff'.2 fun c ↦ ?_)
    (span_le.2 <| Set.range_subset_iff.2 fun x ↦ ⟨single x 1, by simp⟩)
  simpa using sum_mem fun c hc ↦ smul_mem _ _ (subset_span <| Set.mem_range_self c)

lemma Finsupp.lift_surjective_iff (R : Type*) [Semiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] {X : Type*} (f : X → M) :
    Function.Surjective (lift M R X f) ↔ span R (Set.range f) = ⊤ := by
  rw [← LinearMap.range_eq_top, image_lift]

/-- `s` spans a module `M` iff the corresponding map from `s →₀ R` is surjective. -/
lemma Finsupp.lift_surjective_iff' (R : Type*) [Semiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] (s : Set M) :
    Function.Surjective (lift M R s Subtype.val) ↔ span R s = ⊤ := by
  rw [lift_surjective_iff, Subtype.range_coe_subtype, Set.setOf_mem_eq]

-- Generalises `Basis.ext_multilinear`.
lemma MultilinearMap.hom_ext {R ι N : Type*} [CommSemiring R] [Finite ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]
    {f g : MultilinearMap R M N} (s : ∀ i, Set (M i))
    (span : ∀ i, span R (s i) = ⊤)
    (h : ∀ v : (i : ι) → s i, (f fun i ↦ v i) = g fun i ↦ v i) : f = g := by
  cases nonempty_fintype ι
  ext v
  obtain ⟨a, rfl⟩ := Function.Surjective.piMap
    (fun i ↦ (Finsupp.lift_surjective_iff' R _).2 (span i)) v
  unfold Pi.map
  classical simp [Finsupp.sum, map_sum_finset, map_smul_univ, h]

lemma MultilinearMap.hom_ext' {R ι N : Type*} [CommSemiring R] [Finite ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]
    {f g : MultilinearMap R M N} (X : ι → Type*) (s : (i : ι) → X i → M i)
    (span : ∀ i, span R (Set.range (s i)) = ⊤)
    (h : ∀ v : (i : ι) → X i, (f fun i ↦ s i (v i)) = g fun i ↦ s i (v i)) : f = g :=
  hom_ext _ span fun v ↦ by
    convert h fun i ↦ (v i).2.choose using 2 <;>
    exact funext fun i ↦ (v i).2.choose_spec.symm

lemma MultilinearMap.hom_ext₂ {R ι N : Type*} [CommSemiring R] [Finite ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]
    {f g : MultilinearMap R M N} (X : ι → Type*) (Y : ι → Type*) (s : (i : ι) → X i → Y i → M i)
    (span : ∀ i, span R ({ t | ∃ m n, s i m n = t }) = ⊤)
    (h : ∀ (v : (i : ι) → X i) (w : (i : ι) → Y i),
      (f fun i ↦ s i (v i) (w i)) = g fun i ↦ s i (v i) (w i)) : f = g :=
  hom_ext' (fun i ↦ X i × Y i) (fun i ↦ Function.uncurry (s i))
    (fun i ↦ by convert span i; simp [Function.uncurry, Set.range]) fun v ↦ h _ _

@[simp]
lemma TensorProduct.span_mk_one_eq_top {R A M : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [AddCommMonoid M] [Module R M] :
    span A (Set.range (mk R A M 1)) = ⊤ := by
  rw [← Set.image_univ, ← baseChange_span, span_univ, baseChange_top]


@[simps!] noncomputable
def Submodule.quotientComapLinearEquiv {R : Type*} [Ring R] {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (f : M₁ →ₗ[R] M₂) (hf : Function.Surjective f) (N : Submodule R M₂) :
    (M₁ ⧸ N.comap f) ≃ₗ[R] (M₂ ⧸ N) := by
  refine .ofBijective (mapQ _ _ f le_rfl) ⟨fun x y h ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := mkQ_surjective _ x
    obtain ⟨y, rfl⟩ := mkQ_surjective _ y
    simp_all [Submodule.Quotient.eq]
  · obtain ⟨x, rfl⟩ := mkQ_surjective _ x
    obtain ⟨x, rfl⟩ := hf x
    exact ⟨mkQ _ x, by simp⟩

open TensorProduct

@[simp] lemma LinearEquiv.baseChange_apply {R A M N : Type*} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (a : A) (m : M) :
    e.baseChange R A M N (a ⊗ₜ m) = a ⊗ₜ (e m) :=
  rfl

noncomputable def Submodule.quotientBaseChange {R : Type u} {M : Type v} (A : Type w) [CommRing R]
    [Ring A] [Algebra R A] [AddCommGroup M] [Module R M] (S : Submodule R M) :
    (A ⊗[R] M ⧸ S.baseChange A) ≃ₗ[A] A ⊗[R] (M ⧸ S) :=
  Function.Exact.linearEquivOfSurjective
    (g := S.mkQ.baseChange A)
    (by convert lTensor_exact A (LinearMap.exact_subtype_mkQ S) S.mkQ_surjective)
    (S.mkQ.lTensor_surjective A S.mkQ_surjective)

@[simp]
lemma Submodule.quotientBaseChange_apply {R : Type u} {M : Type v} (A : Type w) [CommRing R]
    [Ring A] [Algebra R A] [AddCommGroup M] [Module R M] (S : Submodule R M) (a : A) (m : M) :
    S.quotientBaseChange A (Quotient.mk (a ⊗ₜ m)) = a ⊗ₜ (Quotient.mk m) :=
  rfl

@[simp]
lemma Submodule.quotientBaseChange_symm_apply {R : Type u} {M : Type v} (A : Type w) [CommRing R]
    [Ring A] [Algebra R A] [AddCommGroup M] [Module R M] (S : Submodule R M) (a : A) (m : M) :
    (S.quotientBaseChange A).symm (a ⊗ₜ (Quotient.mk m)) = Quotient.mk (a ⊗ₜ m) :=
  (LinearEquiv.symm_apply_eq _).2 <| Submodule.quotientBaseChange_apply ..

/-- The triangle of `R`-modules `A ⊗[R] M ⟶ B ⊗[A] (A ⊗[R] M) ⟶ B ⊗[R] M` commutes. -/
lemma AlgebraTensorModule.cancelBaseChange_comp_mk_one {R A B M : Type*}
    [CommSemiring R] [CommSemiring A] [Semiring B] [AddCommMonoid M] [Module R M]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] :
    (AlgebraTensorModule.cancelBaseChange R A B B M).toLinearMap.restrictScalars R ∘ₗ
        (TensorProduct.mk A B (A ⊗[R] M) 1).restrictScalars R =
      LinearMap.rTensor M (IsScalarTower.toAlgHom R A B).toLinearMap :=
  ext <| LinearMap.ext₂ fun a m ↦ by simp [Algebra.algebraMap_eq_smul_one]

/-- The triangle of `R`-modules `A ⊗[R] M ⟶ B ⊗[A] (A ⊗[R] M) ⟶ B ⊗[R] M` commutes. -/
lemma AlgebraTensorModule.cancelBaseChange_comp_mk_one' {R A B M : Type*}
    [CommSemiring R] [CommSemiring A] [Semiring B] [AddCommMonoid M] [Module R M]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] :
    ((AlgebraTensorModule.cancelBaseChange R A B B M).toLinearMap.restrictScalars A ∘ₗ
        TensorProduct.mk A B (A ⊗[R] M) 1).restrictScalars R =
      LinearMap.rTensor M (IsScalarTower.toAlgHom R A B).toLinearMap :=
  cancelBaseChange_comp_mk_one

/-- The triangle of `R`-modules `A ⊗[R] M ⟶ B ⊗[A] (A ⊗[R] M) ⟶ B ⊗[R] M` commutes. -/
lemma AlgebraTensorModule.coe_cancelBaseChange_comp_mk_one {R A B M : Type*}
    [CommSemiring R] [CommSemiring A] [Semiring B] [AddCommMonoid M] [Module R M]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] :
    (AlgebraTensorModule.cancelBaseChange R A B B M) ∘ (TensorProduct.mk A B (A ⊗[R] M) 1) =
      LinearMap.rTensor M (IsScalarTower.toAlgHom R A B).toLinearMap :=
  funext <| LinearMap.congr_fun cancelBaseChange_comp_mk_one

lemma LinearMap.restrictScalars_baseChange {R A M N : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (f.baseChange A).restrictScalars R = f.lTensor A :=
  rfl

@[simp] lemma LinearMap.quotKerEquivOfSurjective_apply {R M M₂ : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R M₂]
    (f : M →ₗ[R] M₂) (hf : Function.Surjective f) (x : M) :
    f.quotKerEquivOfSurjective hf (Submodule.Quotient.mk x) = f x :=
  rfl

lemma LinearEquiv.piRing_symm_apply_single {R M ι S : Type*} [Semiring R] [Fintype ι]
    [DecidableEq ι] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M] [SMulCommClass R S M]
    (f : ι → M) (i : ι) (r : R) :
    (LinearEquiv.piRing R M ι S).symm f (Pi.single i r) = r • f i := by
  rw [piRing_symm_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (by intros; simp [*]),
    Pi.single_apply, if_pos rfl]

lemma LinearEquiv.piRing_symm_apply_single_one {R M ι S : Type*} [Semiring R] [Fintype ι]
    [DecidableEq ι] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M] [SMulCommClass R S M]
    (f : ι → M) (i : ι) :
    (LinearEquiv.piRing R M ι S).symm f (Pi.single i 1) = f i := by
  rw [piRing_symm_apply_single, one_smul]
