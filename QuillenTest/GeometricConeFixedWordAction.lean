/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.GeometricConeFixedWordAction

/-!
# Whole-time regression for actual fixed cone words

The input point belongs to the original finite cone iterate, and the action time remains
free. The transformation is the already specified geometric word with its original casts.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.KTheory.Bass
open FiniteConeTopology NaturalTrack GeometricConeFixedWords
open scoped unitInterval
universe u w

example {U : Scheme.{u}} (q : U ⟶ integerBase)
    {F : Scheme.{u}ᵒᵖ ⥤ Quillen.LoopPrespectrum.{w}}
    (A : Track (baseProductFunctor q).op (NatTrans.op (baseProductProjection q)) F)
    (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((iterate squareFunctor i F).obj X).space n) :
    ((A.cones (L := (baseProductFunctor q).op)
      (c := NatTrans.op (baseProductProjection q))
      squareFunctor (interchange q) (squareIso_projection q) i).homotopy X).level n
        (r, ((wordAt i F).hom.app X).map n x) =
      ((wordAt i F).hom.app ((baseProductFunctor q).op.obj X)).map n
        (((A.cones (L := (baseProductFunctor q).op)
      (c := NatTrans.op (baseProductProjection q))
      squareFunctor (interchange q) (squareIso_projection q) i).homotopy X).level n
          (r, x)) :=
  congrArg (fun k => k.map n x) (wordAt_equivariant q A i X r)

#print axioms Quillen.KTheory.Bass.GeometricConeFixedWords.wordAt_succ_hom
#print axioms Quillen.KTheory.Bass.GeometricConeFixedWords.betaAt_succ_hom
#print axioms Quillen.KTheory.Bass.GeometricConeFixedWords.betaAt_equivariant
#print axioms Quillen.KTheory.Bass.GeometricConeFixedWords.wordAt_equivariant
