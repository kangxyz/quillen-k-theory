/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueGammaCarrierComparisons
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PlusQuasiIso

/-! # Typed arbitrary precomposition of the actual original right contraction weak law -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints

/-- The original weak-law is typed before any chosen model-to-Plus input is specialized. -/
lemma rightContraction_precompose_weak {C : Type*} [Category C]
    (R : CommRingCat.{u}) (H : C ⥤ CochainComplex.Plus (twoChartLine R).Modules) (K : C) :
    QuasiIso ((Functor.whiskerLeft H (originalRightLineGodementContractionMap R)).app K).hom :=
  AlgebraicGeometry.Scheme.Modules.Plus.plus_nattrans_precompose_quasiIso
    (originalRightLineGodementContractionMap R) H
    (originalRightLineGodementContractionMap_quasiIso R) K

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
