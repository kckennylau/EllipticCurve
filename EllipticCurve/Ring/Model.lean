/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Models of Elliptic Curves over a Ring

We define elliptic curves over a ring from the Weierstrass equation. Note that not all "elliptic
curves" in the literature necessarily satisfy a Weierstrass cubic globally.

## Main definitions

* `FooBar`

-/

universe u

open CategoryTheory

namespace EllipticCurve.Ring

variable {R : Type u} [CommRing R] (W : WeierstrassCurve.Affine R)

-- to be replaced
def model : CommRingCat.{u} ⥤ Type u :=
  _

end EllipticCurve.Ring
