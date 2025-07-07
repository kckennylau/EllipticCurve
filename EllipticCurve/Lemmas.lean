/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.GroupTheory.Congruence.Hom

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
