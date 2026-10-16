/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.Square
public import Aglib.CategoryTheory.Limits.Shapes.SequentialSystem.SignCorrection
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassSuccessor
public import Quillen.Topology.Prespectrum.StableShift
public import Mathlib.CategoryTheory.Whiskering

/-!
# Signed stable groups of the original Bass successor

The actual successor comparison followed by the signed parameter-loop shift identifies the
unchanged stage i+1 group with its original stage-i square cone group. Naturality retains the
original coefficient cone maps. The stage formula displays the alternating sign and the
actual signed-system tail; the bottom-degree specialization includes its integer transport.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The actual successor followed by the signed parameter-loop shift, naturally in coefficients. -/
def boundedFlatAffineSectionBassStableSuccessorIso (i : ℕ) (d : ℤ) :
    boundedFlatAffineSectionBassDiagram.{u} (i + 1) ⋙ stableHomotopyFunctor d ≅
      boundedFlatAffineSectionBassConeDiagram i ⋙ stableHomotopyFunctor (d + 1) :=
  Functor.isoWhiskerRight (boundedFlatAffineSectionBassSuccessorIso i) (stableHomotopyFunctor d) ≪≫
    NatIso.ofComponents
      (fun R => parameterStableHomotopyIso ((boundedFlatAffineSectionBassConeDiagram i).obj R) d)
      (fun f => parameterStableHomotopyIso_naturality
        ((boundedFlatAffineSectionBassConeDiagram i).map f) d)

/-- Its component uses the original successor map before the genuine signed loop shift. -/
theorem boundedFlatAffineSectionBassStableSuccessorIso_hom_app (i : ℕ) (d : ℤ)
    (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassStableSuccessorIso i d).hom.app R =
      (stableHomotopyFunctor d).map ((boundedFlatAffineSectionBassSuccessorIso i).hom.app R) ≫
        (parameterStableHomotopyIso ((boundedFlatAffineSectionBassConeDiagram i).obj R) d).hom :=
  rfl

/-- Naturality keeps the literal stage-i coefficient square and its unchanged cone map. -/
theorem boundedFlatAffineSectionBassStableSuccessorIso_naturality (i : ℕ) (d : ℤ)
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (stableHomotopyFunctor d).map ((boundedFlatAffineSectionBassDiagram (i + 1)).map f) ≫
        (boundedFlatAffineSectionBassStableSuccessorIso i d).hom.app S =
      (boundedFlatAffineSectionBassStableSuccessorIso i d).hom.app R ≫
        (stableHomotopyFunctor (d + 1)).map
          (mappingConeMap (strictSquareComparisonFunctor.map
            ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.map
              (laurentSquareMap f)))) :=
  (boundedFlatAffineSectionBassStableSuccessorIso i d).hom.naturality f

/-- Every original stable-stage representative retains its actual sign and tail reindexing. -/
theorem boundedFlatAffineSectionBassStableSuccessorIso_ι_hom (i : ℕ) (d : ℤ)
    (R : CommRingCat.{u}) (n : ℕ) :
    stableHomotopyι ((boundedFlatAffineSectionBassDiagram (i + 1)).obj R) d n ≫
        (boundedFlatAffineSectionBassStableSuccessorIso i d).hom.app R =
      (stableSystemMap ((boundedFlatAffineSectionBassSuccessorIso i).hom.app R) d).app n ≫
        (CategoryTheory.Limits.SequentialSystem.alternatingIso n
          (parameterStableStageIso ((boundedFlatAffineSectionBassConeDiagram i).obj R) d n)).hom ≫
        (shiftedStableReindexIso ((boundedFlatAffineSectionBassConeDiagram i).obj R) d n).hom ≫
        stableHomotopyι ((boundedFlatAffineSectionBassConeDiagram i).obj R) (d + 1)
          (parameterStableOffset d + n) := by
  rw [boundedFlatAffineSectionBassStableSuccessorIso_hom_app, ← Category.assoc,
    stableHomotopyι_naturality, Category.assoc]
  exact congrArg
    (fun k =>
      (stableSystemMap ((boundedFlatAffineSectionBassSuccessorIso i).hom.app R) d).app n ≫ k)
    (parameterStableHomotopyIso_ι_hom ((boundedFlatAffineSectionBassConeDiagram i).obj R) d n)

/-- The integer equality used to reach the original stage-i bottom degree. -/
theorem boundedFlatAffineSectionBass_bottom_successor_degree (i : ℕ) :
    -((i + 1 : ℕ) : ℤ) + 1 = -(i : ℤ) := by omega

/-- The original next-stage bottom group is the original cone group at degree minus i. -/
def boundedFlatAffineSectionBassBottomSuccessorIso (i : ℕ) :
    boundedFlatAffineSectionBassDiagram.{u} (i + 1) ⋙
        stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) ≅
      boundedFlatAffineSectionBassConeDiagram i ⋙ stableHomotopyFunctor (-(i : ℤ)) :=
  boundedFlatAffineSectionBassStableSuccessorIso i (-((i + 1 : ℕ) : ℤ)) ≪≫
    Functor.isoWhiskerLeft (boundedFlatAffineSectionBassConeDiagram i)
      (eqToIso (congrArg (fun d : ℤ => stableHomotopyFunctor.{u + 1} d)
        (boundedFlatAffineSectionBass_bottom_successor_degree i)))

/-- The bottom component displays the actual integer-degree transport after the signed shift. -/
theorem boundedFlatAffineSectionBassBottomSuccessorIso_hom_app (i : ℕ) (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassBottomSuccessorIso i).hom.app R =
      (boundedFlatAffineSectionBassStableSuccessorIso i (-((i + 1 : ℕ) : ℤ))).hom.app R ≫
        eqToHom (congrArg
          (fun d : ℤ => stableHomotopyGroup ((boundedFlatAffineSectionBassConeDiagram i).obj R) d)
          (boundedFlatAffineSectionBass_bottom_successor_degree i)) := by
  simp only [boundedFlatAffineSectionBassBottomSuccessorIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, eqToIso.hom,
    eqToHom_app]

/-- Bottom-degree coefficient naturality retains the original cone coefficient arrow. -/
theorem boundedFlatAffineSectionBassBottomSuccessorIso_naturality (i : ℕ)
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedFlatAffineSectionBassDiagram (i + 1)).map f) ≫
        (boundedFlatAffineSectionBassBottomSuccessorIso i).hom.app S =
      (boundedFlatAffineSectionBassBottomSuccessorIso i).hom.app R ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          (mappingConeMap (strictSquareComparisonFunctor.map
            ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.map
              (laurentSquareMap f)))) :=
  (boundedFlatAffineSectionBassBottomSuccessorIso i).hom.naturality f

end Quillen.PerfectComplexes
