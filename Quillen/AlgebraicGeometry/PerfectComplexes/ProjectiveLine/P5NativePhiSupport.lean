/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.AcyclicSupport
public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativePhiObjects
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportClosure

/-! # Native Phi support on the actual inverse-image base open

The pullback/restriction comparison uses the literal native projection and
inverse-image open. Exact left line tensor, the actual coproduct comparison and
the original total augmentation preserve acyclicity on that same open. No
compactness of the open, quasi-separatedness or source-term quasicoherence is used.
-/
@[expose] public section
open Quillen


-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePhi
export AlgebraicGeometry.Scheme.Modules.Complex
  (coprod_acyclic)
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePhi

end



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePhi

/-- The original ambient two-summand formula preserves support on the literal inverse image. -/
lemma rawBeforeTotal_preservesSupport (X : QuasiCompactSchemes.{u}) (Z : X.obj.Opens)
    (A B : FlasqueBoundedBelow.Obj X.obj)
    (hA : ((restrict Z.ι).obj A.obj).Acyclic) (hB : ((restrict Z.ι).obj B.obj).Acyclic) :
    ((restrict ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).obj
      ((rawBeforeTotal X).obj (A, B))).Acyclic := by
  exact coprod_preservesSupport ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι _ _
    (flatPullback_preservesSupport (nativeProjection.app X).hom Z A.obj hA)
    (leftTensor_preservesSupport ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι
      (nativeTautologicalLine X) _
      (flatPullback_preservesSupport (nativeProjection.app X).hom Z B.obj hB))

/-- The same support property holds for the actual original bounded-model coproduct. -/
lemma beforeTotal_preservesSupport (X : QuasiCompactSchemes.{u}) (Z : X.obj.Opens)
    (A B : FlasqueBoundedBelow.Obj X.obj)
    (hA : ((restrict Z.ι).obj A.obj).Acyclic) (hB : ((restrict Z.ι).obj B.obj).Acyclic) :
    ((restrict ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).obj
      ((beforeTotal X).obj (A, B)).obj).Acyclic := by
  have hab := rawBeforeTotal_preservesSupport X Z A B hA hB
  intro n
  exact (hab n).of_iso
    ((restrict ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).mapIso
      ((beforeTotalComplexIso X).app (A, B))).symm

/-- Original native Phi preserves support on exactly the inverse-image base open. -/
lemma Phi_preservesSupport (X : QuasiCompactSchemes.{u}) (Z : X.obj.Opens)
    (A B : FlasqueBoundedBelow.Obj X.obj)
    (hA : ((restrict Z.ι).obj A.obj).Acyclic) (hB : ((restrict Z.ι).obj B.obj).Acyclic) :
    ((restrict ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).obj
      ((Phi X).obj (A, B)).obj).Acyclic := by
  let : QuasiIso ((PhiUnit X).app (A, B)).hom := PhiUnit_weak X (A, B)
  exact (restrictAcyclic_iff_of_quasiIso ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι
    ((PhiUnit X).app (A, B)).hom).mp (beforeTotal_preservesSupport X Z A B hA hB)

/-- The existing unbounded perfect two-summand functor has the same actual open support. -/
lemma nativeTwoSummands_preservesSupport (X : QuasiCompactSchemes.{u}) (Z : X.obj.Opens)
    (A B : Perfect X.obj) (hA : ((restrict Z.ι).obj A.obj).Acyclic)
    (hB : ((restrict Z.ι).obj B.obj).Acyclic) :
    ((restrict ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).obj
      ((nativeTwoSummands X).obj (A, B)).obj).Acyclic := by
  let i := (locallyPerfect (nativeLineFunctor.obj X).obj).ι
  let : PreservesFiniteBiproducts i := inferInstance
  let : PreservesBinaryBiproducts i := preservesBinaryBiproducts_of_preservesBiproducts i
  let : PreservesColimitsOfShape (Discrete WalkingPair) i :=
    preservesBinaryCoproducts_of_preservesBinaryBiproducts i
  have hab := coprod_preservesSupport ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι _ _
    (flatPullback_preservesSupport (nativeProjection.app X).hom Z A.obj hA)
    (leftTensor_preservesSupport ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι
      (nativeTautologicalLine X) _
      (flatPullback_preservesSupport (nativeProjection.app X).hom Z B.obj hB))
  intro n
  exact (hab n).of_iso
    ((restrict ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).mapIso (asIso
      (coprodComparison i ((nativeFirstSummand X).obj A) ((nativeSecondSummand X).obj B))))

end Quillen.PerfectComplexes.ProjectiveLine.P5NativePhi
