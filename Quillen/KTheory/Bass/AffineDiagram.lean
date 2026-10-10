/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.KTheory.Bass.TwoChart
public import Quillen.KTheory.Bass.Contraction

/-!
Literal specialization of the generic two-chart construction to the original polynomial/Laurent ring
diagram, preserving its original cokernel objects, Laurent projection and transformation maps.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u v
namespace Quillen.Bass

/--
General two-chart contraction specializes to the already accepted literal affine construction.
-/
lemma twoChart_contraction_affine (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) :
    TwoChart.contraction plus minus F = contraction F := rfl

/-- The original Laurent representative arrow is unchanged by the generic specialization. -/
lemma twoChart_contractionπ_affine (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) :
    TwoChart.contractionπ plus minus F = contractionπ F := rfl

/-- Every transformation map also specializes literally to the old cokernel map. -/
lemma twoChart_contractionMap_affine {F G : CommRingCat.{u} ⥤ AddCommGrpCat.{v}} (α : F ⟶ G) :
    TwoChart.contractionMap plus minus α = contractionMap α := rfl

end Quillen.Bass

end
