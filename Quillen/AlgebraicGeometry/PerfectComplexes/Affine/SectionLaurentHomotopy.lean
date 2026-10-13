/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionPrespectrum
public import Quillen.CategoryTheory.Functor.IdentityAutomorphismSquare
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIsoNaturality

/-!
# The original Laurent-unit loop on the strict section prespectrum

The original Laurent automorphism supplies the entire structure-compatible iterated-S loop.
Its actual coefficient square gives literal naturality at every homotopy time, including
all positive realizations and the unchanged degree-zero compact-open loop space.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The actual Laurent restriction model square commutes strictly for every coefficient map. -/
theorem boundedFlatAffineSectionLaurentModelSquare {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatAffineSectionModelMap (laurentCoefficient R) ≫
        boundedFlatAffineSectionModelMap (laurentMap f) =
      boundedFlatAffineSectionModelMap f ≫
        boundedFlatAffineSectionModelMap (laurentCoefficient S) := by
  change boundedFlatAffineSectionModelFunctor.map (laurentCoefficient R) ≫
      boundedFlatAffineSectionModelFunctor.map (laurentMap f) =
    boundedFlatAffineSectionModelFunctor.map f ≫
      boundedFlatAffineSectionModelFunctor.map (laurentCoefficient S)
  rw [← Functor.map_comp, ← Functor.map_comp, laurent_square]

private theorem sectionLaurentPullbackUnitIso_eq (R : CommRingCat.{u}) :
    boundedFlatAffineSectionLaurentPullbackUnitIso R =
      Quillen.FunctorIdentityAutomorphism.onFunctor
        (boundedFlatAffineSectionsMap (laurentCoefficient R))
        (boundedFlatAffineSectionLaurentUnitIso R) := rfl

/-- The same literal model equality intertwines the original Laurent automorphisms. -/
theorem boundedFlatAffineSectionLaurentModelUnitSquare {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Functor.whiskerRight (boundedFlatAffineSectionLaurentPullbackUnitIso R).hom
        (boundedFlatAffineSectionsMap (laurentMap f)) ≫
        eqToHom (congrArg Model.Hom.functor (boundedFlatAffineSectionLaurentModelSquare f)) =
      eqToHom (congrArg Model.Hom.functor (boundedFlatAffineSectionLaurentModelSquare f)) ≫
        Functor.whiskerLeft (boundedFlatAffineSectionsMap f)
          (boundedFlatAffineSectionLaurentPullbackUnitIso S).hom := by
  rw [sectionLaurentPullbackUnitIso_eq, sectionLaurentPullbackUnitIso_eq]
  exact Quillen.FunctorIdentityAutomorphism.onFunctor_whisker_square
    (boundedFlatAffineSectionsMap (laurentCoefficient R))
    (boundedFlatAffineSectionsMap (laurentCoefficient S))
    (boundedFlatAffineSectionsMap f) (boundedFlatAffineSectionsMap (laurentMap f))
    (eqToHom (congrArg Model.Hom.functor (boundedFlatAffineSectionLaurentModelSquare f)))
    (boundedFlatAffineSectionLaurentUnitIso R) (boundedFlatAffineSectionLaurentUnitIso S)
    (boundedFlatAffineSectionLaurentUnitIso_coefficient f)

/-- The unchanged original Laurent coordinate acts on the entire strict section prespectrum. -/
def boundedFlatAffineSectionLaurentUnitHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedFlatAffineSectionPrespectrumFunctor.map (laurentCoefficient R))
      (boundedFlatAffineSectionPrespectrumFunctor.map (laurentCoefficient R)) :=
  prespectrumIsoHomotopy (boundedFlatAffineSectionModelMap (laurentCoefficient R))
    (boundedFlatAffineSectionLaurentPullbackUnitIso R)

/-- Coefficient naturality retains every original interval value at every prespectrum level. -/
theorem boundedFlatAffineSectionLaurentUnitHomotopy_naturality_apply
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) (t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionPrespectrumFunctor.map (laurentMap f)).map n
        ((boundedFlatAffineSectionLaurentUnitHomotopy R).level n (t, x)) =
      (boundedFlatAffineSectionLaurentUnitHomotopy S).level n
        (t, (boundedFlatAffineSectionPrespectrumFunctor.map f).map n x) := by
  exact prespectrumIsoHomotopy_square_apply
    (boundedFlatAffineSectionModelMap (laurentCoefficient R))
    (boundedFlatAffineSectionModelMap (laurentCoefficient S))
    (boundedFlatAffineSectionModelMap f) (boundedFlatAffineSectionModelMap (laurentMap f))
    (boundedFlatAffineSectionLaurentPullbackUnitIso R)
    (boundedFlatAffineSectionLaurentPullbackUnitIso S)
    (boundedFlatAffineSectionLaurentModelSquare f)
    (boundedFlatAffineSectionLaurentModelUnitSquare f) n t x

end Quillen.PerfectComplexes
