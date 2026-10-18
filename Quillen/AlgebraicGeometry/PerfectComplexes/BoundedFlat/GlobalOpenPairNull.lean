/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalOpenPairDiagram
public import Quillen.Waldhausen.SConstruction.Iterated.DiagramZeroNull

/-! # The original selected-zero null for genuine global open-pair Models -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Complex
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- Actual supported sections have acyclic original evaluation after geometric restriction. -/
theorem pairRestriction_acyclic (A : Scheme.OpenPairs.{u})
    (S : (supported (X := op A.obj.right) A.obj.hom).FullSubcategory) :
    (((globalEvaluation (op A.obj.left)).obj
      ((globalModel.map A.obj.hom.op).functor.obj S.obj)).obj).Acyclic := by
  let e := (restrictIsoPullbackComplex A.obj.hom).app
      (((globalEvaluation (op A.obj.right)).obj S.obj).obj) ≪≫
    (boundedFlatPerfect A.obj.left).ι.mapIso ((evaluationPullbackIso A.obj.hom).app S.obj)
  intro n
  exact (S.property n).of_iso e

/-- The unique map from the unchanged original global zero to supported inclusion. -/
def pairZeroToOpen (A : Scheme.OpenPairs.{u}ᵒᵖ) :
    (zeroHom (pairSupported.obj A) (pairOpen.obj A)).functor ⟶
      (pairForget.app A ≫ pairChangeWeak.app A).functor where
  app S := (pairOpen.obj A).waldhausen.isZero.to_
    ((pairForget.app A ≫ pairChangeWeak.app A).functor.obj S)
  naturality _ _ _ := (pairOpen.obj A).waldhausen.isZero.eq_of_src _ _

/-- The original zero-to-inclusion map is weak for actual geometric open detection. -/
theorem pairZeroToOpen_weak (A : Scheme.OpenPairs.{u}ᵒᵖ) (S : pairSupported.obj A) :
    (pairOpen.obj A).waldhausen.weq ((pairZeroToOpen A).app S) := by
  apply (Structure.withInverseImageWeak_weq_iff (pairRestriction.app A).exact _).mpr
  have hZ : IsZero (((globalEvaluation (op A.unop.obj.left)).obj
      ((pairRestriction.app A).functor.obj (pairAmbient.obj A).waldhausen.zero)).obj) :=
    (boundedFlatPerfect A.unop.obj.left).ι.map_isZero
      ((globalEvaluation_exact (op A.unop.obj.left)).zero
        ((pairRestriction.app A).exact.zero (pairAmbient.obj A).waldhausen.isZero))
  change QuasiIso ((globalEvaluation (op A.unop.obj.left)).map
    ((pairRestriction.app A).functor.map ((pairZeroToOpen A).app S))).hom
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt _ n
    (HomologicalComplex.acyclic_of_isZero _ hZ n)).mpr (pairRestriction_acyclic A.unop S n)

/-- Reverse the same original weak zero-to-inclusion realization, at every open pair. -/
def pairSupportedOpenNull :
    DiagramNullHomotopy (Functor.whiskerRight pairForget prespectrumFunctor)
      (Functor.whiskerRight pairChangeWeak prespectrumFunctor) :=
  modelDiagramZeroNull (C := pairSupported) (F := pairAmbient) (G := pairOpen)
    pairForget pairChangeWeak pairZeroToOpen pairZeroToOpen_weak

namespace ParameterModels
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The same original zero transformation on the actual parameter pair. -/
def zeroToOpen (X : Scheme.{u}ᵒᵖ) :
    (zeroHom ((supported f).obj X) ((openModel f).obj X)).functor ⟶
      ((forget f).app X ≫ (changeWeak f).app X).functor :=
  pairZeroToOpen (op (GlobalSupportedParameter.pair f X.unop))

/-- Actual geometric support proves weak zero-to-inclusion at every parameter. -/
theorem zeroToOpen_weak (X : Scheme.{u}ᵒᵖ) (S : (supported f).obj X) :
    ((openModel f).obj X).waldhausen.weq ((zeroToOpen f X).app S) :=
  pairZeroToOpen_weak (op (GlobalSupportedParameter.pair f X.unop)) S

/-- The original reversed weak-zero realization on the complete scheme-parameter diagram. -/
def supportedOpenNull :
    DiagramNullHomotopy (Functor.whiskerRight (forget f) prespectrumFunctor)
      (Functor.whiskerRight (changeWeak f) prespectrumFunctor) :=
  modelDiagramZeroNull (C := supported f) (F := ambient Q) (G := openModel f)
    (forget f) (changeWeak f) (zeroToOpen f) (zeroToOpen_weak f)

end ParameterModels
end Quillen.PerfectComplexes.GlobalSectionChangeIndex
