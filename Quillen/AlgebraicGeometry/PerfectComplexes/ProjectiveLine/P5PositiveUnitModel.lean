/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.PullbackPushforward
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PullbackPushforward
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5PositiveUnitAffine
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeCoefficientsZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativePhi

/-! # The literal native positive model and its original canonical unit

The accepted original native first summand is followed by the same Godement
total and ordinary direct image. The original geometric unit and augmentation
are lifted by their literal underlying maps to the full flasque-perfect model.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open AlgebraicGeometry.Scheme.ProjectiveLine


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

/-- Actual native geometric pullback followed by the same original Godement total. -/
def firstTotal (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj X.obj ⥤ FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj :=
  P5NativePhi.first X ⋙ FlasqueBoundedBelow.total (nativeLineFunctor.obj X).obj

lemma firstTotal_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq (firstTotal X) :=
  (P5NativePhi.first_exact X).comp
    (FlasqueBoundedBelow.total_exact (nativeLineFunctor.obj X).obj)

/-- The actual native positive coefficient p_*T(pFlat* A). -/
def positive (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj X.obj ⥤ FlasqueBoundedBelow.Obj X.obj :=
  firstTotal X ⋙ P5NativeCoefficients.G0 X

lemma positive_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (positive X) := (firstTotal_exact X).comp (P5NativeCoefficients.G0_exact X)

/-- The same canonical cochain unit, lifted only through the actual full model predicate. -/
def positiveUnit (X : QuasiCompactSchemes.{u}) :
    𝟭 (FlasqueBoundedBelow.Obj X.obj) ⟶ positive X where
  app K := ObjectProperty.homMk
    (((AlgebraicGeometry.Scheme.Modules.Godement.pullbackPushforwardPlusUnit (nativeProjection.app
      X).hom).app
      ((FlasqueCoefficients.toPlus X.obj).obj K)).hom)
  naturality {_ _} f := by
    apply ObjectProperty.hom_ext
    exact congrArg (fun g => g.hom)
      ((AlgebraicGeometry.Scheme.Modules.Godement.pullbackPushforwardPlusUnit (nativeProjection.app
        X).hom).naturality
        ((FlasqueCoefficients.toPlus X.obj).map f))

/-- The degreewise geometric unit and pushed original augmentation are retained literally. -/
lemma positiveUnit_hom (X : QuasiCompactSchemes.{u}) (A : FlasqueBoundedBelow.Obj X.obj) :
    ((positiveUnit X).app A).hom =
      ((AlgebraicGeometry.Scheme.Modules.Plus.pullbackPushforwardUnit (nativeProjection.app
        X).hom).app
        ((FlasqueCoefficients.toPlus X.obj).obj A)).hom ≫
      ((Scheme.Modules.pushforward (nativeProjection.app X).hom).mapHomologicalComplex
        (.up ℤ)).map ((godementTotalUnit (nativeLineFunctor.obj X).obj).app
          ((AlgebraicGeometry.Scheme.Modules.Complex.pullback (nativeProjection.app X).hom).obj
            A.obj)) := rfl

end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
