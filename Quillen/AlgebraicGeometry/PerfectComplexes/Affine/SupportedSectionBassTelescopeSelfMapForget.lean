/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassTelescopeSelfMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassForgetTower
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescopeSelfMapIdentification
public import Quillen.KTheory.Bass.StrictUnderSelfMap

/-!
# The original support-forgetting telescope square

The actual supported and ambient self-maps commute with the existing original telescope
inclusion. The generic restriction square is applied to the proved original supported Laurent
seed square, retaining every finite restriction transport and the honest open endpoint.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The unchanged original telescope inclusion is the actual generic restriction arrow. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeForget_eq :
    boundedFlatAffineSupportedSectionBassTelescopeForget j =
      KTheory.Bass.strictRingDiagramRestrictionTelescopeArrow R
        (boundedFlatAffineSupportedSectionBassSeed j) boundedFlatAffineSectionBassSeed
        (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j)
        (boundedFlatAffineSupportedSectionBassSeed_forget j) := rfl

/-- The whole original supported/ambient square commutes, without any supplied compatibility. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeBassMap_forget :
    boundedFlatAffineSupportedSectionBassTelescopeBassMap j ≫
        (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineSupportedSectionBassTelescopeForget j) =
      boundedFlatAffineSupportedSectionBassTelescopeForget j ≫
        KTheory.Bass.strictRingDiagramUnderSeed R boundedFlatAffineSectionBassTelescopeBassMap := by
  rw [boundedFlatAffineSupportedSectionBassTelescopeForget_eq,
    boundedFlatAffineSectionBassTelescopeBassMap_eq]
  have h := KTheory.Bass.strictRingDiagramRestrictionTelescopeArrow_selfMap R
    (boundedFlatAffineSupportedSectionBassSeed j) boundedFlatAffineSectionBassSeed
    (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j)
    (boundedFlatAffineSupportedSectionBassSeed_forget j)
  apply NatTrans.ext
  funext a
  exact NatTrans.congr_app h a

/-- At each actual coefficient, the right edge is the unchanged ambient ring self-map. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeBassMap_forget_app (a : Under R) :
    (boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app a ≫
        ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineSupportedSectionBassTelescopeForget j)).app a =
      (boundedFlatAffineSupportedSectionBassTelescopeForget j).app a ≫
        boundedFlatAffineSectionBassTelescopeBassMap.app a.right :=
  NatTrans.congr_app (boundedFlatAffineSupportedSectionBassTelescopeBassMap_forget j) a

end Quillen.PerfectComplexes
