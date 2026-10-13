/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.ExactFunctor
public import Quillen.Waldhausen.QuillenComparison.BasedNaturality

/-! # Canonical Q/S naturality with the original K-maps of any exact functor -/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Limits
universe v u

namespace Quillen.Waldhausen.QuillenComparison
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : Quillen.ExactStructure C} {ED : Quillen.ExactStructure D}
  (F : Quillen.ExactFunctor EC ED)

/-- The original based Q/S isomorphism commutes with both genuine K-map APIs,
without any extra pushout-preservation or zero-equality hypothesis. -/
theorem comparisonKEquiv_exactFunctor_naturality (n : ℕ) :
    (comparisonKEquiv ED n).toMonoidHom.comp (Waldhausen.KMap F.waldhausenExact n) =
      (F.KMap n).comp (comparisonKEquiv EC n).toMonoidHom :=
  comparisonKEquiv_naturality_KMap F F.waldhausenExact n

end Quillen.Waldhausen.QuillenComparison
