/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Godement.Contraction
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.OriginalLineContractionComplexes
public import Aglib.AlgebraicGeometry.Cohomology.Godement.Tensor
public import Aglib.CategoryTheory.NatTrans.Unit
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PlusQuasiIso

/-! # Natural weak original line contractions after Godement totalization

The literal maps insert the original Godement augmentation inside the left line
tensor. The determinant pairing and the original right-tensor braiding contract
the unresolved pair before the original outer total is applied.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open Quillen




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u})

/-- The literal total T(L tensor T(Q tensor K)). -/
def originalLeftLineGodementResolved :=
  godementContractionResolved (twoChartLine R)
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine R))
    (tautologicalLine R)

/-- The literal total T(L tensor T(K tensor Q)). -/
def originalRightLineGodementResolved :=
  godementContractionResolved (twoChartLine R)
    (moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R))
    (tautologicalLine R)

/-- The actual original left-pair contraction followed by the original outer total. -/
def originalLeftLineGodementPlainIso :=
  godementContractionPlainIso _ _ (originalLeftLineContractionIso R)

/-- The actual original right-pair contraction followed by the original outer total. -/
def originalRightLineGodementPlainIso :=
  godementContractionPlainIso _ _ (originalRightLineContractionIso R)

/-- The natural comparison T(K) to the actual left resolved pair. -/
def originalLeftLineGodementContractionMap :=
  godementContractionMap _ _ (originalLeftLineContractionIso R)

/-- The natural comparison T(K) to the actual right resolved pair. -/
def originalRightLineGodementContractionMap :=
  godementContractionMap _ _ (originalRightLineContractionIso R)

/-- The actual original left comparison is weak on every Plus input, including zero-ring inputs.
-/
theorem originalLeftLineGodementContractionMap_quasiIso
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    QuasiIso ((originalLeftLineGodementContractionMap R).app K).hom :=
  godementContractionMap_quasiIso _ _ (originalLeftLineContractionIso R) K

/-- The actual original right comparison is weak on every Plus input. -/
theorem originalRightLineGodementContractionMap_quasiIso
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    QuasiIso ((originalRightLineGodementContractionMap R).app K).hom :=
  godementContractionMap_quasiIso _ _ (originalRightLineContractionIso R) K

end AlgebraicGeometry.Scheme.ProjectiveLine
