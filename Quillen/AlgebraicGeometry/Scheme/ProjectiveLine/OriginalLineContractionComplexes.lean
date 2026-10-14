/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.OriginalLineContraction

/-! # The original line contractions on actual cochain complexes

The termwise lifts retain the original determinant contraction and braiding.
The bounded-below lifts retain the original composition and identity comparisons.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.SchemeSheaf

/-- The termwise lift of an actual module-functor contraction. -/
def cochainContractionIso {X : Scheme.{u}} (F G : X.Modules ⥤ X.Modules)
    [F.Additive] [G.Additive] (e : F ⋙ G ≅ 𝟭 X.Modules) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex X.Modules ℤ) :=
  Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso X.Modules (.up ℤ)

/-- Each degree is the same original contraction component. -/
lemma cochainContractionIso_hom_f {X : Scheme.{u}} (F G : X.Modules ⥤ X.Modules)
    [F.Additive] [G.Additive] (e : F ⋙ G ≅ 𝟭 X.Modules)
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    ((cochainContractionIso F G e).hom.app K).f n = e.hom.app (K.X n) := by
  simp [cochainContractionIso]

/-- The bounded-below lift retains the original composition and identity units. -/
def plusContractionIso {X : Scheme.{u}} (F G : X.Modules ⥤ X.Modules)
    [F.Additive] [G.Additive] (e : F ⋙ G ≅ 𝟭 X.Modules) :
    F.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus ≅
      𝟭 (CochainComplex.Plus X.Modules) :=
  (Functor.mapCochainComplexPlusCompIso F G).symm ≪≫
    NatIso.mapCochainComplexPlus e ≪≫ Functor.mapCochainComplexPlusIdIso X.Modules

/-- The actual comparison maps appear in their original order. -/
lemma plusContractionIso_hom_app {X : Scheme.{u}} (F G : X.Modules ⥤ X.Modules)
    [F.Additive] [G.Additive] (e : F ⋙ G ≅ 𝟭 X.Modules)
    (K : CochainComplex.Plus X.Modules) :
    (plusContractionIso F G e).hom.app K =
      (Functor.mapCochainComplexPlusCompIso F G).inv.app K ≫
        (NatIso.mapCochainComplexPlus e).hom.app K ≫
        (Functor.mapCochainComplexPlusIdIso X.Modules).hom.app K := rfl

/-- Its complex map is the termwise original contraction. -/
lemma plusContractionIso_hom_f {X : Scheme.{u}} (F G : X.Modules ⥤ X.Modules)
    [F.Additive] [G.Additive] (e : F ⋙ G ≅ 𝟭 X.Modules)
    (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    ((plusContractionIso F G e).hom.app K).hom.f n = e.hom.app (K.obj.X n) := by
  simp [plusContractionIso, Functor.mapCochainComplexPlusCompIso,
    NatIso.mapCochainComplexPlus, Functor.mapCochainComplexPlusIdIso]

end Quillen.SchemeSheaf

namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf
variable (R : CommRingCat.{u})

/-- Actual cochain contraction of L tensor (Q tensor K). -/
def originalLeftLineContractionComplexIso :=
  cochainContractionIso _ _ (originalLeftLineContractionIso R)

/-- Actual cochain contraction of L tensor (K tensor Q), with original braiding. -/
def originalRightLineContractionComplexIso :=
  cochainContractionIso _ _ (originalRightLineContractionIso R)

/-- Actual bounded-below contraction of L tensor (Q tensor K). -/
def originalLeftLineContractionPlusIso :=
  plusContractionIso _ _ (originalLeftLineContractionIso R)

/-- Actual bounded-below contraction of L tensor (K tensor Q), with original braiding. -/
def originalRightLineContractionPlusIso :=
  plusContractionIso _ _ (originalRightLineContractionIso R)

/-- The original associator, determinant pairing and left unit occur in every degree. -/
lemma originalLeftLineContractionPlusIso_hom_f
    (K : CochainComplex.Plus (twoChartLine R).Modules) (n : ℤ) :
    ((originalLeftLineContractionPlusIso R).hom.app K).hom.f n =
      (originalLineAssociatorIso R).hom.app (K.obj.X n) ≫
        (moduleTensorCoefficientMap (twoChartLine R) (tautologicalLinePairing R)).app
          (K.obj.X n) ≫
        (SheafOfModulesOfCommRing.tensorLeftUnitIso (twoChartLine R).sheaf).hom.app
          (K.obj.X n) := by
  exact (plusContractionIso_hom_f _ _ (originalLeftLineContractionIso R) K n).trans
    (originalLeftLineContractionIso_hom R (K.obj.X n))

/-- The right contraction first uses the original braiding inside the left tensor. -/
lemma originalRightLineContractionPlusIso_hom_f
    (K : CochainComplex.Plus (twoChartLine R).Modules) (n : ℤ) :
    ((originalRightLineContractionPlusIso R).hom.app K).hom.f n =
      (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
        ((moduleTensorSymmetryNatIso (twoChartLine R) (tautologicalQuotientLine R)).hom.app
          (K.obj.X n)) ≫
        (originalLeftLineContractionIso R).hom.app (K.obj.X n) := by
  exact (plusContractionIso_hom_f _ _ (originalRightLineContractionIso R) K n).trans rfl

end Quillen.Scheme.ProjectiveLine
