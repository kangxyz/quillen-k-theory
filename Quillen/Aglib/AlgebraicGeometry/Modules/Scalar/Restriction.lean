/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.Scalar.Pullback

/-! Original restriction maps preserve the actual global scalar action. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original open restriction takes scalar multiplication to the actual restricted scalar. -/
lemma restrict_map_globalScalar {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (r : Γ(X, ⊤)) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor j).map ((globalScalar X r).app M) =
      (globalScalar U (j.appTop r)).app ((Scheme.Modules.restrictFunctor j).obj M) := by
  apply (cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M)).mp
  have he := (Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality
    ((globalScalar X r).app M)
  refine he.trans ?_
  rw [pullback_map_globalScalar]
  exact (globalScalar U (j.appTop r)).naturality
    ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M)

end AlgebraicGeometry.Scheme.Modules
