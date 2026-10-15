/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Polynomial.LaurentUnderSquare
public import Quillen.KTheory.Bass.StrictRingDiagram

/-!
# Restricting the original strict Bass diagrams to algebras over a fixed ring

The original Laurent square over Under R forgets to the same ring square. Restriction
therefore commutes with the actual Bass endofunctor and every iterate. The seed construction
retains the original natural arrow, using only the specified functor equality at its target.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u w
namespace Quillen.KTheory.Bass

/-- Restriction of an original ring diagram along the literal Under.forget functor. -/
def strictRingDiagramRestriction (R : CommRingCat.{u}) :
    (CommRingCat.{u} ⥤ LoopPrespectrum.{w}) ⥤ (Under R ⥤ LoopPrespectrum.{w}) :=
  (Functor.whiskeringLeft (Under R) CommRingCat LoopPrespectrum).obj (Under.forget R)

/-- Restricting original Laurent squares commutes literally with the same cone-loop functor. -/
theorem strictRingDiagramRestriction_comp_bass (R : CommRingCat.{u}) :
    strictRingDiagramRestriction.{u,w} R ⋙
        strictDiagramFunctor (CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor R) =
      strictRingDiagramFunctor ⋙ strictRingDiagramRestriction R := rfl

/-- Every original finite iterate restricts by the same literal diagram functor equality. -/
theorem strictRingDiagramRestriction_comp_iterate (R : CommRingCat.{u}) (n : ℕ) :
    strictRingDiagramRestriction.{u,w} R ⋙
        strictDiagramIterate (CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor R) n =
      strictRingDiagramIterate n ⋙ strictRingDiagramRestriction R := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change strictRingDiagramRestriction R ⋙
      (strictDiagramFunctor (CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor R) ⋙
        strictDiagramIterate (CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor R) n) =
      (strictRingDiagramFunctor ⋙ strictRingDiagramIterate n) ⋙ strictRingDiagramRestriction R
    rw [← Functor.assoc, strictRingDiagramRestriction_comp_bass, Functor.assoc, ih,
      ← Functor.assoc]

/-- The restricted original seed retains the given arrow and only its proved endpoint equality. -/
def strictRingDiagramUnderSeed (R : CommRingCat.{u})
    {F : CommRingCat.{u} ⥤ LoopPrespectrum.{w}} (η : F ⟶ strictRingDiagramFunctor.obj F) :
    Under.forget R ⋙ F ⟶
      (strictDiagramFunctor (CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor R)).obj
        (Under.forget R ⋙ F) :=
  (strictRingDiagramRestriction R).map η ≫
    eqToHom (congrArg (fun H ↦ H.obj F) (strictRingDiagramRestriction_comp_bass R).symm)

/-- The actual component of the restricted seed is the unchanged original ring component. -/
theorem strictRingDiagramUnderSeed_app (R : CommRingCat.{u})
    {F : CommRingCat.{u} ⥤ LoopPrespectrum.{w}} (η : F ⟶ strictRingDiagramFunctor.obj F)
    (a : Under R) : (strictRingDiagramUnderSeed R η).app a = η.app a.right := rfl

end Quillen.KTheory.Bass
