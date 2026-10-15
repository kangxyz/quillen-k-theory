/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeNegativeVanishing
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativePhi
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeCoefficientsOne
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasquePhiOffDiagonal

/-! # Actual original native off-diagonal weak-zero maps

The native derived calculation only certifies acyclicity. The literal natural
zero chain maps give vanishing of the original K-maps, retaining both original
Godement augmentations and the prescribed right tensor and signed shift.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open AlgebraicGeometry.Scheme.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeEntries
open FlasqueCoefficients

/-- The standard derived-category instance for sheaves of modules on `Y`. -/
local instance nativeOffDiagonalDerived (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Y.Modules := HasDerivedCategory.standard _

/-- Actual totalization of the original structure summand. -/
def firstTotal (X : QuasiCompactSchemes.{u}) :=
  P5NativePhi.first X ⋙ FlasqueBoundedBelow.total (nativeLineFunctor.obj X).obj

lemma firstTotal_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq (firstTotal X) :=
  (P5NativePhi.first_exact X).comp (FlasqueBoundedBelow.total_exact _)

/-- Actual totalization of the original left negative-line summand. -/
def secondTotal (X : QuasiCompactSchemes.{u}) :=
  P5NativePhi.second X ⋙ FlasqueBoundedBelow.total (nativeLineFunctor.obj X).obj

lemma secondTotal_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq (secondTotal X) :=
  (P5NativePhi.second_exact X).comp (FlasqueBoundedBelow.total_exact _)

/-- The original raw second summand has zero derived projection on every flasque input. -/
lemma second_derivedZero (X : QuasiCompactSchemes.{u}) (K : FlasqueBoundedBelow.Obj X.obj) :
    IsZero ((derivedPushforwardPlus (nativeProjection.app X).hom).obj
      (DerivedCategory.Plus.Q.obj ((boundedToPlus (nativeLineFunctor.obj X).obj).obj
        ((P5NativePhi.second X).obj K)))) :=
  negative_derivedZero X ((toPlus X.obj).obj K) K.property.1.1

/-- The original total augmentation and installed G0 unit identify the actual acyclic output. -/
lemma G0_secondTotal_derivedZero (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj X.obj) :
    IsZero (DerivedCategory.Plus.Q.obj ((toPlus X.obj).obj
      ((P5NativeCoefficients.G0 X).obj ((secondTotal X).obj K)))) := by
  let P := (nativeLineFunctor.obj X).obj
  let C := (boundedToPlus P).obj ((P5NativePhi.second X).obj K)
  have : IsIso (DerivedCategory.Plus.Q.map ((godementTotalPlusUnit P).app C)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso P.Modules) _
      (godementTotalPlusUnit_quasiIso P C)
  have ht := (second_derivedZero X K).of_iso
    ((derivedPushforwardPlus (nativeProjection.app X).hom).mapIso
      (asIso (DerivedCategory.Plus.Q.map ((godementTotalPlusUnit P).app C))).symm)
  exact ht.of_iso ((P5NativeCoefficients.G0DerivedIso X).app ((secondTotal X).obj K))

/-- Actual right tensor of the original forward total augmentation. -/
def firstRightTensorUnit (X : QuasiCompactSchemes.{u}) (K : FlasqueBoundedBelow.Obj X.obj) :
    (moduleTensorByLineRight (nativeTautologicalLine X)).mapCochainComplexPlus.obj
        ((boundedToPlus (nativeLineFunctor.obj X).obj).obj ((P5NativePhi.first X).obj K)) ⟶
      (P5NativeCoefficients.rightTensorPlus X).obj ((firstTotal X).obj K) :=
  ObjectProperty.homMk
    ((AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (nativeTautologicalLine X)).map
      ((godementTotalUnit (nativeLineFunctor.obj X).obj).app
        ((boundedToPlus (nativeLineFunctor.obj X).obj).obj ((P5NativePhi.first X).obj K)).obj))

lemma firstRightTensorUnit_quasiIso (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj X.obj) : QuasiIso (firstRightTensorUnit X K).hom := by
  let P := (nativeLineFunctor.obj X).obj
  let C := (boundedToPlus P).obj ((P5NativePhi.first X).obj K)
  let : QuasiIso ((godementTotalPlusUnit P).app C).hom := godementTotalPlusUnit_quasiIso P C
  change QuasiIso ((AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (nativeTautologicalLine
    X)).map
    ((godementTotalPlusUnit P).app C).hom)
  infer_instance

/-- Original symmetry and the forward total unit identify the lower off-diagonal acyclicity. -/
lemma rightTensor_firstTotal_derivedZero (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj X.obj) :
    IsZero ((derivedPushforwardPlus (nativeProjection.app X).hom).obj
      (DerivedCategory.Plus.Q.obj
        ((P5NativeCoefficients.rightTensorPlus X).obj ((firstTotal X).obj K)))) := by
  let P := (nativeLineFunctor.obj X).obj
  let C := (boundedToPlus P).obj ((P5NativePhi.first X).obj K)
  let N := (boundedToPlus P).obj ((P5NativePhi.second X).obj K)
  let M := (moduleTensorByLineRight (nativeTautologicalLine X)).mapCochainComplexPlus.obj C
  let e : N ≅ M := (CochainComplex.plus P.Modules).isoMk
    ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeftRightIso (nativeTautologicalLine X)).app
      C.obj)
  have hm := (second_derivedZero X K).of_iso
    ((derivedPushforwardPlus (nativeProjection.app X).hom).mapIso
      (DerivedCategory.Plus.Q.mapIso e.symm))
  have : IsIso (DerivedCategory.Plus.Q.map (firstRightTensorUnit X K)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso P.Modules) _
      (firstRightTensorUnit_quasiIso X K)
  exact hm.of_iso ((derivedPushforwardPlus (nativeProjection.app X).hom).mapIso
    (asIso (DerivedCategory.Plus.Q.map (firstRightTensorUnit X K))).symm)

/-- The installed original G1 comparison retains its original signed shift. -/
lemma G1_firstTotal_derivedZero (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj X.obj) :
    IsZero (DerivedCategory.Plus.Q.obj ((toPlus X.obj).obj
      ((P5NativeCoefficients.G1 X).obj ((firstTotal X).obj K)))) := by
  have hs := (shiftFunctor (DerivedCategory.Plus X.obj.Modules) (1 : ℤ)).map_isZero
    (rightTensor_firstTotal_derivedZero X K)
  exact hs.of_iso ((P5NativeCoefficients.G1DerivedIso X).app ((firstTotal X).obj K))

/-- The original upper off-diagonal exact functor. -/
def G0Second (X : QuasiCompactSchemes.{u}) := secondTotal X ⋙ P5NativeCoefficients.G0 X

lemma G0Second_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (G0Second X) := (secondTotal_exact X).comp (P5NativeCoefficients.G0_exact X)

/-- The original lower off-diagonal exact functor. -/
def G1First (X : QuasiCompactSchemes.{u}) := firstTotal X ⋙ P5NativeCoefficients.G1 X

lemma G1First_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (G1First X) := (firstTotal_exact X).comp (P5NativeCoefficients.G1_exact X)

/-- The literal natural zero transformation proves the original upper entry vanishes, including K0.
-/
theorem G0Second_KMap_eq_one (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    Waldhausen.KMap (G0Second_exact X) n = 1 :=
  FlasquePhiEntries.KMap_eq_one_of_derivedZero (FlasqueBoundedBelow.waldhausen X.obj)
    X.obj (G0Second X) (G0Second_exact X) (G0_secondTotal_derivedZero X) n

/-- The literal natural zero transformation proves the original lower entry vanishes, including K0.
-/
theorem G1First_KMap_eq_one (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    Waldhausen.KMap (G1First_exact X) n = 1 :=
  FlasquePhiEntries.KMap_eq_one_of_derivedZero (FlasqueBoundedBelow.waldhausen X.obj)
    X.obj (G1First X) (G1First_exact X) (G1_firstTotal_derivedZero X) n

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeEntries
