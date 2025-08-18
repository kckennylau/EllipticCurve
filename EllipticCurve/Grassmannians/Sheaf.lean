/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.Grassmannians.Basic
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Grassmannian is Sheaf

In this file we show that the Grassmannian functor `Module.Grassmannian.functor : Under R ⥤ Type u`
is a sheaf.

-/

universe u v

open CategoryTheory

namespace Module.Grassmannian

#check functor
#check Presieve.IsSheaf

end Module.Grassmannian
