/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FirstEndpointBeta

/-! # Actual original first coefficient and beta component maps -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
variable (R : CommRingCat.{u})

/-- The pre-total erasure isos retain the original coefficient chain map. -/
lemma coefficientActualRawMap_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (coefficientActualRawMap R).app K = coefficientChainMap R K := by
  simp only [coefficientActualRawMap, coefficientEraseIso, pulledEraseIso,
    modelToPlusEraseIso, coefficientRawMap, NatTrans.comp_app,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapCochainComplexPlusCompι_hom_app,
    Functor.mapCochainComplexPlusCompι_inv_app,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.comp_id]
  dsimp only [Functor.comp_obj, FlasqueCoefficients.toPlus, CochainComplex.Plus.ι,
    ObjectProperty.lift, Functor.mapCochainComplexPlus, ObjectProperty.ι_obj]
  rw [((FlasqueDiagonal.coefficient R .first).mapHomologicalComplex (.up ℤ)).map_id K.obj]
  rw [(pullbackComplex (relativeFirst R)).map_id ((resolved R).obj K).obj]
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- The actual natural beta retains only native endpoint erasure and associations. -/
lemma beta_actual_factor (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((beta R).app K).hom = (betaSourceIso R).hom.app K ≫
      (betaRawMap R).app K ≫ (betaTargetIso R).hom.app K := rfl

end Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
