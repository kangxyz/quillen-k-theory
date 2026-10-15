/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativePhi

/-! # Literal native Phi objects, original coproduct comparisons and bounds

The chosen coproduct in the original bounded model is retained. Its comparison
with the ambient cochain coproduct is the actual categorical coproduct comparison;
Godement total maps that comparison without changing the original Phi functor.
-/
@[expose] public section
open Quillen


-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePhi
export CategoryTheory.Limits
  (coprod_isZero)
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePhi

end



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePhi

instance boundedComplexInclusion_preservesBinaryCoproducts (P : Scheme.{u}) :
    PreservesColimitsOfShape (Discrete WalkingPair) (BoundedBelow.objects P).ι := by
  let : PreservesFiniteBiproducts (BoundedBelow.objects P).ι := inferInstance
  let : PreservesBinaryBiproducts (BoundedBelow.objects P).ι :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  exact preservesBinaryCoproducts_of_preservesBinaryBiproducts _

/-- The original ambient cochain coproduct, retaining the actual left tensor order. -/
def rawBeforeTotal (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj ⥤
      Complex (nativeLineFunctor.obj X).obj :=
  Waldhausen.Additivity.sumFunctor
    (CategoryTheory.Prod.fst _ _ ⋙ (FlasqueBoundedBelow.objects X.obj).ι ⋙
      pullbackComplex (nativeProjection.app X).hom)
    (CategoryTheory.Prod.snd _ _ ⋙ (FlasqueBoundedBelow.objects X.obj).ι ⋙
      pullbackComplex (nativeProjection.app X).hom ⋙
      tensorByLineComplex (nativeTautologicalLine X))

/-- The original cochain/full-subcategory categorical coproduct comparison. -/
def boundedComplexSumIso {C : Type v} [Category C] (P : Scheme.{u})
    (H F : C ⥤ BoundedBelow.Obj P) :
    Waldhausen.Additivity.sumFunctor (H ⋙ (BoundedBelow.objects P).ι)
        (F ⋙ (BoundedBelow.objects P).ι) ≅
      Waldhausen.Additivity.sumFunctor H F ⋙ (BoundedBelow.objects P).ι :=
  NatIso.ofComponents
    (fun K => asIso (coprodComparison (BoundedBelow.objects P).ι (H.obj K) (F.obj K)))
    (fun f => (coprodComparison_natural (BoundedBelow.objects P).ι (H.map f) (F.map f)).symm)

/-- The actual cochain/full-subcategory coproduct comparison, in the original order. -/
def beforeTotalComplexIso (X : QuasiCompactSchemes.{u}) :
    beforeTotal X ⋙ (BoundedBelow.objects (nativeLineFunctor.obj X).obj).ι ≅
      rawBeforeTotal X :=
  (boundedComplexSumIso (nativeLineFunctor.obj X).obj
    (CategoryTheory.Prod.fst _ _ ⋙ first X) (CategoryTheory.Prod.snd _ _ ⋙ second X)).symm

/-- Before total the selected original bounded coproduct is used literally. -/
lemma beforeTotal_obj (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj) :
    (beforeTotal X).obj K = ((first X).obj K.1 ⨿ (second X).obj K.2) := rfl

/-- The original selected coproduct map retains both original module maps. -/
lemma beforeTotal_map (X : QuasiCompactSchemes.{u})
    {K M : FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj} (f : K ⟶ M) :
    (beforeTotal X).map f = coprod.map ((first X).map f.1) ((second X).map f.2) := rfl

/-- The underlying original Phi complex is the actual Godement total of that selected sum. -/
lemma Phi_obj_underlying (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj) :
    ((Phi X).obj K).obj =
      (godementTotal (nativeLineFunctor.obj X).obj).obj ((beforeTotal X).obj K).obj := rfl

/-- Phi retains the original sum maps followed by the actual original Godement total map. -/
lemma Phi_map_underlying (X : QuasiCompactSchemes.{u})
    {K M : FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj} (f : K ⟶ M) :
    ((Phi X).map f).hom =
      (godementTotal (nativeLineFunctor.obj X).obj).map ((beforeTotal X).map f).hom := rfl

/-- The actual total augmentation component, without replacing its original source sum. -/
lemma PhiUnit_hom (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj) :
    ((PhiUnit X).app K).hom =
      (godementTotalUnit (nativeLineFunctor.obj X).obj).app ((beforeTotal X).obj K).obj := rfl

/-- Mapping the actual coproduct comparison identifies the literal ambient formula for Phi. -/
def PhiComplexIso (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj) :
    ((Phi X).obj K).obj ≅
      (godementTotal (nativeLineFunctor.obj X).obj).obj
        (((pullbackComplex (nativeProjection.app X).hom).obj K.1.obj) ⨿
          ((tensorByLineComplex (nativeTautologicalLine X)).obj
            ((pullbackComplex (nativeProjection.app X).hom).obj K.2.obj))) :=
  (godementTotal (nativeLineFunctor.obj X).obj).mapIso ((beforeTotalComplexIso X).app K)

/-- Both original summands retain a given common strict lower bound. -/
lemma rawBeforeTotal_isStrictlyGE (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj) (a : ℤ)
    [K.1.obj.IsStrictlyGE a] [K.2.obj.IsStrictlyGE a] :
    ((rawBeforeTotal X).obj K).IsStrictlyGE a := by
  let A := (pullbackComplex (nativeProjection.app X).hom).obj K.1.obj
  let B := (tensorByLineComplex (nativeTautologicalLine X)).obj
    ((pullbackComplex (nativeProjection.app X).hom).obj K.2.obj)
  have hA : A.IsStrictlyGE a := by dsimp [A, pullbackComplex]; infer_instance
  have hB : B.IsStrictlyGE a := by
    dsimp [B, tensorByLineComplex, pullbackComplex]
    infer_instance
  let := hA
  let := hB
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  have hzero := coprod_isZero (A.X n) (B.X n)
    (CochainComplex.isZero_of_isStrictlyGE A a n hn)
    (CochainComplex.isZero_of_isStrictlyGE B a n hn)
  exact hzero.of_iso (asIso
    (coprodComparison (HomologicalComplex.eval _ (.up ℤ) n) A B)).symm

/-- The actual original bounded coproduct keeps the same specified strict lower bound. -/
lemma beforeTotal_isStrictlyGE (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj) (a : ℤ)
    [K.1.obj.IsStrictlyGE a] [K.2.obj.IsStrictlyGE a] :
    ((beforeTotal X).obj K).obj.IsStrictlyGE a := by
  let := rawBeforeTotal_isStrictlyGE X K a
  exact CochainComplex.isStrictlyGE_of_iso ((beforeTotalComplexIso X).app K).symm a

/-- The actual original Godement total retains that same bound. -/
lemma Phi_isStrictlyGE (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj) (a : ℤ)
    [K.1.obj.IsStrictlyGE a] [K.2.obj.IsStrictlyGE a] :
    ((Phi X).obj K).obj.IsStrictlyGE a := by
  let := beforeTotal_isStrictlyGE X K a
  exact FlasqueBoundedBelow.total_isStrictlyGE _ _ a

end Quillen.PerfectComplexes.ProjectiveLine.P5NativePhi
