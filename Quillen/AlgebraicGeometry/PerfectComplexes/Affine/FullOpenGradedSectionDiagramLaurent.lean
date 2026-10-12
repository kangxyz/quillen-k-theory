/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionDiagramLaurent
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenGradedSectionDiagram

/-!
# The same original Laurent track on quotient-graded full-open sections

The actual graded Model diagram has the unchanged section functors and inherited zeros.
It therefore uses the accepted original forward-T automorphism, with its exact coefficient
square. Original realization gives the whole graded Laurent track at every interval value.
No contraction or compatibility with the normalized localization null is asserted here.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The original target Laurent unit acts on the actual quotient-graded coefficient functor. -/
def boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso (a : Under R) :
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor ≅
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor :=
  Quillen.FunctorIdentityAutomorphism.onFunctor
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor
    (boundedFlatAffineFullOpenSectionLaurentUnitIso j a)

/-- Changing the weakness leaves the actual underlying Laurent automorphism unchanged. -/
theorem boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso_eq
    (a : Under R) :
    boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a =
      boundedFlatAffineFullOpenSectionDiagramLaurentPullbackUnitIso j a := rfl

/-- The original Laurent coefficient square commutes for the actual graded Models. -/
theorem boundedFlatAffineFullOpenGradedSectionDiagramLaurentModelSquare {a b : Under R}
    (f : a ⟶ b) :
    (boundedFlatAffineFullOpenGradedSectionModelFunctor j).map ((laurentUnderCoefficient R).app a) ≫
        (boundedFlatAffineFullOpenGradedSectionModelFunctor j).map ((laurentUnderFunctor R).map f) =
      (boundedFlatAffineFullOpenGradedSectionModelFunctor j).map f ≫
        (boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
          ((laurentUnderCoefficient R).app b) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
    ((laurentUnderCoefficient R).naturality f).symm

/-- The actual coefficient square intertwines the same original Laurent automorphisms. -/
theorem boundedFlatAffineFullOpenGradedSectionDiagramLaurentModelUnitSquare {a b : Under R}
    (f : a ⟶ b) :
    Functor.whiskerRight
        (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a).hom
        ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
          ((laurentUnderFunctor R).map f)).functor ≫
        eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineFullOpenGradedSectionDiagramLaurentModelSquare j f)) =
      eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineFullOpenGradedSectionDiagramLaurentModelSquare j f)) ≫
        Functor.whiskerLeft ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map f).functor
          (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j b).hom := by
  unfold boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso
  exact Quillen.FunctorIdentityAutomorphism.onFunctor_whisker_square
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app b)).functor
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map f).functor
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderFunctor R).map f)).functor
    (eqToHom (congrArg Model.Hom.functor
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentModelSquare j f)))
    (boundedFlatAffineFullOpenSectionLaurentUnitIso j a)
    (boundedFlatAffineFullOpenSectionLaurentUnitIso j b)
    (boundedFlatAffineFullOpenSectionLaurentUnitIso_coefficient j f)

/-- The original scalar action gives the whole actual graded Laurent coefficient track. -/
def boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy (a : Under R) :
    Homotopy
      ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a))
      ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a)) :=
  prespectrumIsoHomotopy
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a))
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a)

/-- Every original coefficient map preserves every level and the identical unit-action time. -/
theorem boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
        ((laurentUnderFunctor R).map f)).map n
        ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j b).level n
        (t, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n x) :=
  prespectrumIsoHomotopy_square_apply
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a))
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app b))
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map f)
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map ((laurentUnderFunctor R).map f))
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a)
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j b)
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentModelSquare j f)
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentModelUnitSquare j f) n t x

end Quillen.PerfectComplexes
