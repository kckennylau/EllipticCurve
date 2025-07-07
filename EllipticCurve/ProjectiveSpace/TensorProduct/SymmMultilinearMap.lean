/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Symmetric Multilinear Maps

In this file we define symmetric multilinear maps bewteen modules as a module itself.

## Main definitions

* `SymmMultilinearMap R M N ι`: the symmetric `R`-multilinear maps from `ι → M` to `N`.

-/

universe u u' u₁ u₂ u₃ v w w'

open Equiv MultilinearMap

variable (R : Type u) [Semiring R] (M : Type v) [AddCommMonoid M] [Module R M]
  (N : Type w) [AddCommMonoid N] [Module R N]
  (P : Type w') [AddCommMonoid P] [Module R P] (ι : Type u')
  (S : Type u₁) [Semiring S] [Module S M] [SMulCommClass R S M] [Module S N] [SMulCommClass R S N]

def MultilinearMap.IsSymmetric (f : MultilinearMap R (fun _ : ι ↦ M) N) : Prop :=
  ∀ e : Perm ι, f.domDomCongr e = f

abbrev SymmMultilinearMap :=
  { f : MultilinearMap R (fun _ : ι ↦ M) N // f.IsSymmetric }

namespace SymmMultilinearMap

variable {R M N P ι S} {f f₁ f₂ g g₁ g₂ : SymmMultilinearMap R M N ι}

instance : FunLike (SymmMultilinearMap R M N ι) (ι → M) N where
  coe f := f
  coe_injective' _ _ h := by ext x; exact congrFun h x

@[simp, norm_cast] lemma coe_coe : ⇑(f : MultilinearMap R (fun _ : ι ↦ M) N) = f := rfl

@[simp] lemma coe_mk (f : MultilinearMap R (fun _ : ι ↦ M) N) (h) :
  ⇑(⟨f, h⟩ : SymmMultilinearMap R M N ι) = f := rfl

@[simp] lemma apply_perm_apply (e : Perm ι) (x : ι → M) : (f fun i ↦ x (e i)) = f x :=
  DFunLike.congr_fun (f.2 e) x

variable (R M N ι) in
def addSubmonoid : AddSubmonoid (MultilinearMap R (fun _ : ι ↦ M) N) where
  carrier := IsSymmetric R M N ι
  add_mem' hf hg e := ext fun x ↦ congrArg₂ (· + ·)
    (DFunLike.congr_fun (hf e) x) (DFunLike.congr_fun (hg e) x)
  zero_mem' _ := rfl

instance : AddCommMonoid (SymmMultilinearMap R M N ι) :=
  AddSubmonoid.toAddCommMonoid (addSubmonoid R M N ι)

@[simp] lemma add_coe : ⇑(f + g) = f + g := rfl

@[simp] lemma zero_coe : ⇑(0 : SymmMultilinearMap R M N ι) = 0 := rfl

variable (R M N ι S) in
def submodule : Submodule S (MultilinearMap R (fun _ : ι ↦ M) N) where
  __ := addSubmonoid R M N ι
  smul_mem' c _ hf e := ext fun x ↦ congrArg (c • ·) (DFunLike.congr_fun (hf e) x)

instance (S : Type*) [Semiring S] [SMul S M] [Module S N] [SMulCommClass R S N] :
    SMul S (SymmMultilinearMap R M N ι) :=
  SetLike.smul (submodule R M N ι S)

@[simp] lemma smul_coe {S : Type*} [Semiring S] [SMul S M] [Module S N] [SMulCommClass R S N]
    (c : S) : ⇑(c • f) = c • ⇑f := rfl

instance [Module R S] : Module S (SymmMultilinearMap R M N ι) :=
  SMulMemClass.toModule (submodule R M N ι S)

def _root_.LinearMap.compSymmMultilinearMap
    (f : N →ₗ[R] P) (g : SymmMultilinearMap R M N ι) : SymmMultilinearMap R M P ι :=
  ⟨f.compMultilinearMap g, fun e => by simp [g.2 e]⟩

@[simp] lemma _root_.LinearMap.compSymmMultilinearMap_coe
    (f : N →ₗ[R] P) (g : SymmMultilinearMap R M N ι) :
    ⇑(f.compSymmMultilinearMap g) = ⇑f ∘ ⇑g :=
  rfl

lemma _root_.LinearMap.compSymmMultilinearMap_apply
    (f : N →ₗ[R] P) (g : SymmMultilinearMap R M N ι) (x : ι → M) :
    f.compSymmMultilinearMap g x = f (g x) :=
  rfl

def compLinearMap (f : SymmMultilinearMap R N P ι) (g : M →ₗ[R] N) :
    SymmMultilinearMap R M P ι :=
  ⟨f.1.compLinearMap fun _ ↦ g, fun e ↦ MultilinearMap.ext fun x ↦ apply_perm_apply e (g ∘ x)⟩

@[simp] lemma compLinearMap_coe (f : SymmMultilinearMap R N P ι) (g : M →ₗ[R] N) :
    ⇑(f.compLinearMap g) = ⇑f ∘ fun x i ↦ g (x i) := rfl

lemma compLinearMap_apply (f : SymmMultilinearMap R N P ι) (g : M →ₗ[R] N) (x : ι → M) :
    f.compLinearMap g x = f (g ∘ x) := rfl

end SymmMultilinearMap
