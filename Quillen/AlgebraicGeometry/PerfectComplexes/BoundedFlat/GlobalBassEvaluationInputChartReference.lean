/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputMixedDesc
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputRectanglePreNodes
public import Quillen.Waldhausen.SConstruction.Iterated.ModelReferenceReanchor

/-!
# Actual chart references in the mixed global evaluation diagram

A polynomial chart with its proved Laurent projection equation transports the original
double-square reference into the fixed mixed Laurent reference. All nodes retain their
complete Model arrows and anchor isomorphisms.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputChartReference
open GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The actual chart equation transports the strict total reference, before any evaluation. -/
def chartSourceIso : (InputMixedDesc.sourceMap g).functor ≅
    (InputTripleNodes.sourceMap (laurent.map g) (k.app Y) (projection.app Y)).functor :=
  eqToIso (congrArg (fun j : laurent.obj X ⟶ Y =>
    (globalModel.map j.op ≫ evaluationModel (op (laurent.obj X))).functor)
      (congrArg (fun j => laurent.map g ≫ j) (hk Y)).symm)

/-- Complete nodes in the original mixed Laurent reference. -/
abbrev Node := Σ F : globalModel.obj (op Y) ⟶
    modelOf (boundedFlatPerfectWaldhausen (laurent.obj X)),
  (InputMixedDesc.sourceMap g).functor ≅ F.functor

/-- The original Y chart after its actual raw Laurent postmap and chart reference transport. -/
def postNode (i : Fin 5) : Node g :=
  ModelSimplex.reanchorNodes (chartSourceIso g k hk)
    (InputTripleNodes.postNode (laurent.map g) (k.app Y) (projection.app Y)) i

/-- The original X chart with both geometric squares and its actual strict premap retained. -/
def preNode (i : Fin 5) : Node g :=
  ModelSimplex.reanchorNodes (chartSourceIso g k hk)
    (InputRectangleNodes.preNode (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g)) i

/-- Every original raw rectangle node with its complete Laurent reference transport. -/
def rawNode (i : Fin 18) : Node g :=
  ModelSimplex.reanchorNodes (chartSourceIso g k hk)
    (InputRectangleNodes.rawNode (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g)) i

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputChartReference
