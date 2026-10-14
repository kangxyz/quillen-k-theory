/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativePhiObjects
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportClosure

/-! # Native Phi support on the actual inverse-image base open

The pullback/restriction comparison uses the literal native projection and
inverse-image open. Exact left line tensor, the actual coproduct comparison and
the original total augmentation preserve acyclicity on that same open. No
compactness of the open, quasi-separatedness or source-term quasicoherence is used.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.Scheme Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePhi

/-- Genuine flat pullback preserves acyclicity of the original cochain complex. -/
lemma flatPullback_acyclic {P Y : Scheme.{u}} (f : P ⟶ Y) [Flat f]
    (A : Complex Y) (hA : A.Acyclic) : ((pullbackComplex f).obj A).Acyclic := by
  intro n
  exact (hA n).map (Scheme.Modules.pullback f)

/-- Actual flat pullback preserves support on exactly the inverse-image base open. -/
lemma flatPullback_preservesSupport {P Y : Scheme.{u}} (f : P ⟶ Y) [Flat f]
    (Z : Y.Opens) (A : Complex Y) (hA : ((restrict Z.ι).obj A).Acyclic) :
    ((restrict (f ⁻¹ᵁ Z).ι).obj ((pullbackComplex f).obj A)).Acyclic := by
  have ha := flatPullback_acyclic (f ∣_ Z) ((restrict Z.ι).obj A) hA
  intro n
  exact (ha n).of_iso ((pullbackComplexRestrictIso f Z).app A).symm

/-- The original left tensor/restriction comparison, without changing the tensor order. -/
def leftTensorRestrictionIso {U P : Scheme.{u}} (j : U ⟶ P) [IsOpenImmersion j]
    (L : P.Modules) :
    tensorByLineComplex L ⋙ restrict j ≅ restrict j ⋙ tensorByLineComplex (L.restrict j) :=
  (Functor.mapHomologicalComplexCompIso (tensorRestrictionNatIso j L) _).symm

/-- Exact left tensor by the actual finite locally free line preserves acyclicity. -/
lemma leftTensor_acyclic {P : Scheme.{u}} (L : P.Modules) [IsFiniteLocallyFree P L]
    (A : Complex P) (hA : A.Acyclic) : ((tensorByLineComplex L).obj A).Acyclic := by
  intro n
  exact (hA n).map (moduleTensorLeftFunctor P L)

/-- Left tensor preserves acyclicity on that specified actual open. -/
lemma leftTensor_preservesSupport {U P : Scheme.{u}} (j : U ⟶ P) [IsOpenImmersion j]
    (L : P.Modules) [IsFiniteLocallyFree P L] (A : Complex P)
    (hA : ((restrict j).obj A).Acyclic) :
    ((restrict j).obj ((tensorByLineComplex L).obj A)).Acyclic := by
  have ha := leftTensor_acyclic (L.restrict j) ((restrict j).obj A) hA
  intro n
  exact (ha n).of_iso ((leftTensorRestrictionIso j L).app A).symm

/-- The actual ambient cochain coproduct of acyclic complexes is acyclic. -/
lemma coprod_acyclic {P : Scheme.{u}} (A B : Complex P) (hA : A.Acyclic) (hB : B.Acyclic) :
    (A ⨿ B).Acyclic := by
  intro n
  rw [exactAt_iff_isZero_homology]
  let F := homologyFunctor P.Modules (.up ℤ) n
  let : PreservesFiniteBiproducts F := inferInstance
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  let : PreservesColimitsOfShape (Discrete WalkingPair) F :=
    preservesBinaryCoproducts_of_preservesBinaryBiproducts F
  exact (coprod_isZero (A.homology n) (B.homology n)
    (hA n).isZero_homology (hB n).isZero_homology).of_iso
      (asIso (coprodComparison F A B)).symm

/-- Actual restriction of the original selected cochain coproduct preserves acyclicity. -/
lemma coprod_preservesSupport {U P : Scheme.{u}} (j : U ⟶ P) [IsOpenImmersion j]
    (A B : Complex P) (hA : ((restrict j).obj A).Acyclic)
    (hB : ((restrict j).obj B).Acyclic) : ((restrict j).obj (A ⨿ B)).Acyclic := by
  have hab := coprod_acyclic ((restrict j).obj A) ((restrict j).obj B) hA hB
  intro n
  exact (hab n).of_iso (asIso (coprodComparison (restrict j) A B))

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
