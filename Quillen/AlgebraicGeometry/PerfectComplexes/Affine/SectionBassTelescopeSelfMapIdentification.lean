/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.Square
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescopeSelfMap
public import Quillen.KTheory.Bass.StrictDiagramSelfMap

/-!
# The unchanged ambient telescope self-map is the generic original-seed construction

The equality is proved on the entire original cylinder, retaining the existing successor
transport and original Laurent seed. It introduces no new ambient map or stage transition.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The original ambient map is exactly the genuine generic construction on its original seed. -/
theorem boundedFlatAffineSectionBassTelescopeBassMap_eq :
    boundedFlatAffineSectionBassTelescopeBassMap.{u} =
      KTheory.Bass.strictDiagramTelescopeSelfMap laurentSquareFunctor
        boundedFlatAffineSectionBassSeed := by
  apply NatTrans.ext
  funext R
  apply Telescope.hom_ext
  intros
  rfl

end Quillen.PerfectComplexes
