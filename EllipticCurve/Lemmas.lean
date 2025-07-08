/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.GroupTheory.Congruence.Hom
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Fin.Basic

/-!
# Lemmas for Mathlib

These are small lemmas that can be immediatly PR'ed to Mathlib.
-/

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

variable (e₁ : Perm (Fin i)) (e₂ : Perm (Fin j))

def permAdd : Perm (Fin (i + j)) :=
  finSumFinEquiv.permCongr (e₁.sumCongr e₂)

@[simp] lemma permAdd_left (x : Fin i) : permAdd e₁ e₂ (x.castAdd j) = (e₁ x).castAdd j := by
  simp [permAdd]

@[simp] lemma permAdd_right (x : Fin j) : permAdd e₁ e₂ (x.natAdd i) = (e₂ x).natAdd i := by
  simp [permAdd]

end Fin
