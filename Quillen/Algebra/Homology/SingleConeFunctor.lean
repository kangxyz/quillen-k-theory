/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Algebra.Homology.MappingConeIso
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Additive functors on cones of single maps

The comparison uses the original single-complex natural isomorphism and cone map.
The explicit minus-one shift is retained.
-/

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v u' v'
namespace CochainComplex.mappingCone
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D]
variable (F : C ⥤ D) [F.Additive] {X Y : C} (f : X ⟶ Y)

/-- An additive functor carries the original cone of a single map to its mapped cone. -/
def singleFunctorIso :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (mappingCone ((single C (.up ℤ) 0).map f)) ≅
      mappingCone ((single D (.up ℤ) 0).map (F.map f)) :=
  mapHomologicalComplexIso ((single C (.up ℤ) 0).map f) F ≪≫
    isoOfIso _ _ ((singleMapHomologicalComplex F (.up ℤ) 0).app X)
      ((singleMapHomologicalComplex F (.up ℤ) 0).app Y)
      ((singleMapHomologicalComplex F (.up ℤ) 0).hom.naturality f)

/-- The cone comparison preserves the explicit minus-one shift. -/
def shiftedSingleFunctorIso :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((mappingCone ((single C (.up ℤ) 0).map f))⟦(-1 : ℤ)⟧) ≅
      (mappingCone ((single D (.up ℤ) 0).map (F.map f)))⟦(-1 : ℤ)⟧ :=
  ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (-1 : ℤ)).app _ ≪≫
    (CategoryTheory.shiftFunctor (CochainComplex D ℤ) (-1 : ℤ)).mapIso (singleFunctorIso F f)

end CochainComplex.mappingCone
end

end
