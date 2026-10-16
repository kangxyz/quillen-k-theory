/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.OriginalLineGodementContractions

/-! # Original insertion and contraction map consumers -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Godement

namespace OriginalLineGodementConsumers

/-- The same original insertion is weak on every original Plus input. -/
theorem original_insertion_weak {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (E : X.Modules)
    [IsFiniteLocallyFree X E] (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementContractionInsertion X F E).app K).hom :=
  godementContractionInsertion_quasiIso F E K

/-- The actual contraction still first reverses the original iso, then inserts the unit. -/
theorem original_contraction_component {X : Scheme.{u}} (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) (e : F ⋙ moduleTensorLeftFunctor X E ≅ 𝟭 X.Modules)
    (K : CochainComplex.Plus X.Modules) :
    (godementContractionMap F E e).app K =
      (godementContractionPlainIso F E e).inv.app K ≫
        (godementContractionInsertion X F E).app K :=
  godementContractionMap_app F E e K

/-- Both original legs give the actual weak contraction without a resolution premise. -/
theorem original_contraction_weak {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (E : X.Modules)
    [IsFiniteLocallyFree X E] (e : F ⋙ moduleTensorLeftFunctor X E ≅ 𝟭 X.Modules)
    (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementContractionMap F E e).app K).hom :=
  godementContractionMap_quasiIso F E e K

open AlgebraicGeometry.Scheme.ProjectiveLine

/-- The actual original left named comparison remains weak without an extra premise. -/
theorem original_left_named_contraction_weak (R : CommRingCat.{u})
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    QuasiIso ((originalLeftLineGodementContractionMap R).app K).hom :=
  originalLeftLineGodementContractionMap_quasiIso R K

/-- The actual original right named comparison retains the original braiding and is weak. -/
theorem original_right_named_contraction_weak (R : CommRingCat.{u})
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    QuasiIso ((originalRightLineGodementContractionMap R).app K).hom :=
  originalRightLineGodementContractionMap_quasiIso R K

/-- The left named map is still definitionally the same original generic contraction. -/
theorem original_left_named_contraction_definition (R : CommRingCat.{u}) :
    originalLeftLineGodementContractionMap R =
      godementContractionMap
        (moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine R))
        (tautologicalLine R) (originalLeftLineContractionIso R) := rfl

/-- The right named map still uses the literal right tensor and original contraction iso. -/
theorem original_right_named_contraction_definition (R : CommRingCat.{u}) :
    originalRightLineGodementContractionMap R =
      godementContractionMap
        (moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R))
        (tautologicalLine R) (originalRightLineContractionIso R) := rfl

end OriginalLineGodementConsumers
