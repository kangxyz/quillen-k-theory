/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientFullOpenBassRestriction

/-! The actual full-open localization arrows retain identity and composition. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
namespace Quillen.PerfectComplexes
universe u
variable {R : CommRingCat.{u}} {P Q S : Over (Spec R)}

local instance fullOpenRestrictionId (P : Over (Spec R)) :
    IsOpenImmersion (Over.Hom.left (𝟙 P)) := by
  change IsOpenImmersion (𝟙 P.left)
  infer_instance

local instance fullOpenRestrictionComp (f : P ⟶ Q) (g : Q ⟶ S)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] :
    IsOpenImmersion (Over.Hom.left (f ≫ g)) := by
  change IsOpenImmersion (f.left ≫ g.left)
  infer_instance

example (P : Over (Spec R)) :
    boundedFlatCoefficientAmbientBassTelescopeFullOpen (𝟙 P) =
      𝟙 (boundedFlatCoefficientAmbientBassTelescopeFunctor P) := by
  rw [boundedFlatCoefficientAmbientBassTelescopeFullOpen_eq_schemeRestriction,
    boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction_id]

example (f : P ⟶ Q) (g : Q ⟶ S) [IsOpenImmersion f.left] [IsOpenImmersion g.left] :
    boundedFlatCoefficientAmbientBassTelescopeFullOpen (f ≫ g) =
      boundedFlatCoefficientAmbientBassTelescopeFullOpen g ≫
        boundedFlatCoefficientAmbientBassTelescopeFullOpen f := by
  rw [boundedFlatCoefficientAmbientBassTelescopeFullOpen_eq_schemeRestriction,
    boundedFlatCoefficientAmbientBassTelescopeFullOpen_eq_schemeRestriction,
    boundedFlatCoefficientAmbientBassTelescopeFullOpen_eq_schemeRestriction]
  exact boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction_comp f g

#print axioms boundedFlatCoefficientFullOpenBassTelescopeFunctor_eq_ambient
#print axioms boundedFlatCoefficientAmbientBassTelescopeFullOpen_eq_schemeRestriction
#print axioms boundedFlatCoefficientAmbientBassNegativeMap_fullOpen
end Quillen.PerfectComplexes
