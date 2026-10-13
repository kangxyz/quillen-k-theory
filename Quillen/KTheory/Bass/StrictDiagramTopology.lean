/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Bass.StrictDiagram
public import Quillen.Topology.Prespectrum.StrictSquareTopology

/-!
# Point-set closure under every actual strict Bass iterate

T1 separation and genuine chosen-point HEP propagate through the existing Bass endofunctor
and every iterate. The induction ranges over strict diagrams and uses the original four
corners, double-cylinder point, cone point and compact-open loop point at each step.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- Every original Bass value retains T1 separation at each level. -/
instance strictDiagramFunctorSpaceT1Space (F : C ⥤ LoopPrespectrum.{w})
    [∀ X k, T1Space ((F.obj X).space k)] (X : C) (k : ℕ) :
    T1Space ((((strictDiagramFunctor Q).obj F).obj X).space k) :=
  @LoopPrespectrum.StrictSquare.loopedConeSpaceT1Space
    (F.mapArrow.mapArrow.obj (Q.obj X)) k
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).left.left).space k)))
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).left.right).space k)))
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).right.left).space k)))
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).right.right).space k)))

/-- The original chosen points remain well-based through the literal Bass construction. -/
theorem strictDiagramFunctor_point_homotopyExtensionProperty (F : C ⥤ LoopPrespectrum.{w})
    [∀ X k, T1Space ((F.obj X).space k)]
    (h : ∀ X k, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point k))))
    (X : C) (k : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
      ((((strictDiagramFunctor Q).obj F).obj X).point k))) :=
  @LoopPrespectrum.StrictSquare.loopedCone_point_homotopyExtensionProperty
    (F.mapArrow.mapArrow.obj (Q.obj X)) k
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).left.left).space k)))
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).left.right).space k)))
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).right.left).space k)))
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).right.right).space k)))
    (h (Q.obj X).left.left k) (h (Q.obj X).left.right k)
    (h (Q.obj X).right.left k) (h (Q.obj X).right.right k)

/-- No new separation premise is needed at later stages of the same original iteration. -/
instance strictDiagramIterateSpaceT1Space (n : ℕ) (F : C ⥤ LoopPrespectrum.{w})
    [∀ X k, T1Space ((F.obj X).space k)] (X : C) (k : ℕ) :
    T1Space ((((strictDiagramIterate Q n).obj F).obj X).space k) := by
  induction n generalizing F with
  | zero => exact inferInstanceAs (T1Space ((F.obj X).space k))
  | succ n ih => exact ih ((strictDiagramFunctor Q).obj F)

/-- Every iterated point has genuine HEP, proved from the initial diagram's original points. -/
theorem strictDiagramIterate_point_homotopyExtensionProperty (n : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) [∀ X k, T1Space ((F.obj X).space k)]
    (h : ∀ X k, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point k))))
    (X : C) (k : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
      ((((strictDiagramIterate Q n).obj F).obj X).point k))) := by
  induction n generalizing F with
  | zero => exact h X k
  | succ n ih =>
    exact ih ((strictDiagramFunctor Q).obj F)
      (strictDiagramFunctor_point_homotopyExtensionProperty Q F h)

end Quillen.KTheory.Bass
