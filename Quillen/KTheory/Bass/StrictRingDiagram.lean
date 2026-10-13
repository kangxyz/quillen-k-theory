/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Polynomial.LaurentSquare
public import Quillen.KTheory.Bass.StrictDiagram

/-!
# The strict polynomial and Laurent Bass endofunctor

The actual coefficient inclusions and the two distinct Laurent charts specify the evaluation
square. The construction closes on strict spectrum-valued ring diagrams and their strict natural
transformations. A supplied seed arrow is iterated by this same endofunctor. Instantiating the
original geometric K-theory seed still requires a proved rectification and comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u w
namespace Quillen.KTheory.Bass

/-- Bass on strict ring diagrams, using the literal polynomial and Laurent coefficient square. -/
def strictRingDiagramFunctor :
    (CommRingCat.{u} ⥤ LoopPrespectrum.{w}) ⥤ (CommRingCat.{u} ⥤ LoopPrespectrum.{w}) :=
  strictDiagramFunctor PolynomialBaseChange.laurentSquareFunctor

/-- Every iterate is again a strict ring diagram with an action on every coefficient map. -/
def strictRingDiagramIterate (n : ℕ) :
    (CommRingCat.{u} ⥤ LoopPrespectrum.{w}) ⥤ (CommRingCat.{u} ⥤ LoopPrespectrum.{w}) :=
  strictDiagramIterate PolynomialBaseChange.laurentSquareFunctor n

/-- Apply the nth Bass endofunctor to the supplied seed, without introducing a new unit. -/
def strictRingDiagramTransition {F : CommRingCat.{u} ⥤ LoopPrespectrum.{w}}
    (η : F ⟶ strictRingDiagramFunctor.obj F) (n : ℕ) :
    (strictRingDiagramIterate n).obj F ⟶ (strictRingDiagramIterate (n + 1)).obj F :=
  strictDiagramTransition PolynomialBaseChange.laurentSquareFunctor η n

/-- The iterated original seed commutes literally with every coefficient map. -/
theorem strictRingDiagramTransition_naturality
    {F : CommRingCat.{u} ⥤ LoopPrespectrum.{w}}
    (η : F ⟶ strictRingDiagramFunctor.obj F) (n : ℕ)
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    ((strictRingDiagramIterate n).obj F).map f ≫
        (strictRingDiagramTransition η n).app S =
      (strictRingDiagramTransition η n).app R ≫
        ((strictRingDiagramIterate (n + 1)).obj F).map f :=
  (strictRingDiagramTransition η n).naturality f

end Quillen.KTheory.Bass
