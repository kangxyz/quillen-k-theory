/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenFunctorNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.RestrictionFunctoriality

/-! # Reindexing the open vertex of an exact restriction square

Only the open vertex is transported through an actual scheme isomorphism.
The ambient perfect functor and the original restriction composition maps
are retained.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.OpenFunctorNaturality.ExactRestrictionSquare

variable {U X V Y V' : Scheme.{u}} {j : U ⟶ X} {k : V ⟶ Y}
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- Reindex only the target open through the specified actual geometric comparison. -/
def reindexTargetOpen (D : ExactRestrictionSquare j k) (e : V' ≅ V)
    (k' : V' ⟶ Y) [IsOpenImmersion k'] (w : e.hom ≫ k = k') :
    ExactRestrictionSquare j k' where
  ambient := D.ambient
  onOpen := D.onOpen ⋙ perfectRestrict e.hom
  ambient_exact := D.ambient_exact
  onOpen_exact := D.onOpen_exact.comp (perfectRestrict_waldhausenExact e.hom)
  restrictionIso :=
    Functor.isoWhiskerLeft D.ambient
      (eqToIso (by subst k'; rfl) ≪≫ perfectRestrictCompIso e.hom k) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight D.restrictionIso (perfectRestrict e.hom) ≪≫
      Functor.associator _ _ _

end Quillen.PerfectComplexes.OpenFunctorNaturality.ExactRestrictionSquare
