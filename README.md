# EllipticCurve

Towards a general definition of elliptic curve over schemes.

The eventual goal is to put everything here into
[Mathlib](https://github.com/leanprover-community/mathlib4).

The biggest finished goal for now is [`EllipticCurve.Ring.model`](https://kckennylau.github.io/EllipticCurve-docs/EllipticCurve/Ring/Model.html#EllipticCurve.Ring.model), which is a functor from R-Alg to Type given commutative ring R and an R-module M.

## File Organisation

The files are organised into folders:

* `EllipticCurve.Field`: for the "classical" result of ellptic curve over fields.
* `EllipticCurve.Grassmannians`: for defining the (scheme of) Grassmannians for a module over a
  ring.
* `EllipticCurve.ProjectiveSpace`: for defining projective space over a scheme.
* `EllipticCurve.Sheaf`: for results on modules over a scheme.
* `EllipticCurve.Ring`: for defining elliptic curves over rings from the Weierstrass equation. Note
  that not all "elliptic curves" in the literature has a globally defined Weierstrass cubic. For the
  mathematically correct definition, use elliptic curves over `Spec R` as defined below.
* `EllipticCurve.Scheme`: for defining elliptic curves over schemes.
