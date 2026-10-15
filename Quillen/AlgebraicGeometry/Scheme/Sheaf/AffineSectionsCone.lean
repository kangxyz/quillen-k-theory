/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Algebra.Homology.SingleConeFunctor
public import Quillen.Algebra.ModuleComplex.LinearMapConeShift
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Affine sections and the original shifted single-map cone

For quasicoherent endpoints, the actual tilde counits identify the associated
module cone with the original sheaf cone. The arrow square is counit naturality.
-/

@[expose] public section
open Quillen
open Quillen.SchemeSheaf


section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u}) {M N : (Spec R).Modules}
variable [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)

/-- The original affine counits identify the associated section cone with the sheaf cone. -/
def affineSectionsCechIso :
    ((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj
        (Quillen.ModuleComplex.linearMapCechComplex (moduleSpecΓFunctor.map f).hom) ≅
      (CochainComplex.mappingCone
        ((single (Spec R).Modules (.up ℤ) 0).map f))⟦(-1 : ℤ)⟧ := by
  refine CochainComplex.mappingCone.shiftedSingleFunctorIso
    (tilde.functor R) (moduleSpecΓFunctor.map f) ≪≫
    (CategoryTheory.shiftFunctor (CochainComplex (Spec R).Modules ℤ) (-1 : ℤ)).mapIso ?_
  refine CochainComplex.mappingCone.isoOfIso _ _
    ((single (Spec R).Modules (.up ℤ) 0).mapIso (asIso M.fromTildeΓ))
    ((single (Spec R).Modules (.up ℤ) 0).mapIso (asIso N.fromTildeΓ)) ?_
  simpa only [Functor.mapIso_hom, asIso_hom, ← Functor.map_comp,
    Functor.comp_map, Functor.id_map, Scheme.Modules.fromTildeΓNatTrans] using
    congrArg (single (Spec R).Modules (.up ℤ) 0).map
      (Scheme.Modules.fromTildeΓNatTrans.naturality f)

end AlgebraicGeometry.Scheme.Modules
end

end
