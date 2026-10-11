/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionLaurentUnit
public import Quillen.Algebra.Polynomial.LaurentUnderSquare
public import Quillen.CategoryTheory.Functor.IdentityAutomorphismSquare

/-!
# Original Laurent tracks on the fixed-open supported coefficient diagram

The actual supported Model functor carries the genuine Laurent coefficient square in Under R.
The already proved original scalar coefficient equation supplies its automorphism square.
Realization therefore gives literal naturality at every original homotopy time, including
level zero. No homotopy naturality or seed compatibility is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.Scheme.AffineOpenPair
open Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original Laurent action on the unchanged supported coefficient Model arrow. -/
def boundedFlatAffineSupportedDiagramLaurentPullbackUnitIso (a : Under R) :
    ((boundedFlatAffineSupportedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor ≅
    ((boundedFlatAffineSupportedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor :=
  Quillen.FunctorIdentityAutomorphism.onFunctor
    ((boundedFlatAffineSupportedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor
    (boundedFlatAffineSupportedSectionLaurentUnitIso
      (inclusion j ((laurentUnderFunctor R).obj a)))

/-- The actual fixed-base Laurent coefficient square remains a literal Model square. -/
theorem boundedFlatAffineSupportedDiagramLaurentModelSquare {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderCoefficient R).app a) ≫
        (boundedFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderFunctor R).map f) =
      (boundedFlatAffineSupportedSectionModelFunctor j).map f ≫
        (boundedFlatAffineSupportedSectionModelFunctor j).map
          ((laurentUnderCoefficient R).app b) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (boundedFlatAffineSupportedSectionModelFunctor j).map
    ((laurentUnderCoefficient R).naturality f).symm

/-- The literal Model square intertwines the unchanged original Laurent automorphisms. -/
theorem boundedFlatAffineSupportedDiagramLaurentModelUnitSquare {a b : Under R} (f : a ⟶ b) :
    Functor.whiskerRight (boundedFlatAffineSupportedDiagramLaurentPullbackUnitIso j a).hom
        ((boundedFlatAffineSupportedSectionModelFunctor j).map
          ((laurentUnderFunctor R).map f)).functor ≫
        eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineSupportedDiagramLaurentModelSquare j f)) =
      eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineSupportedDiagramLaurentModelSquare j f)) ≫
        Functor.whiskerLeft ((boundedFlatAffineSupportedSectionModelFunctor j).map f).functor
          (boundedFlatAffineSupportedDiagramLaurentPullbackUnitIso j b).hom :=
  Quillen.FunctorIdentityAutomorphism.onFunctor_whisker_square _ _ _ _ _ _ _
    (boundedFlatAffineSupportedSectionLaurentUnitIso_coefficient
      (inclusion j ((laurentUnderFunctor R).obj a))
      (inclusion j ((laurentUnderFunctor R).obj b)) f.right
      (openMap j ((laurentUnderFunctor R).map f))
      (openMap_inclusion j ((laurentUnderFunctor R).map f)))

/-- The whole Laurent loop of the original fixed-open coefficient prespectrum. -/
def boundedFlatAffineSupportedDiagramLaurentHomotopy (a : Under R) :
    Homotopy
      ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a))
      ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a)) :=
  prespectrumIsoHomotopy
    ((boundedFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderCoefficient R).app a))
    (boundedFlatAffineSupportedDiagramLaurentPullbackUnitIso j a)

/-- The diagram loop is precisely the original supported Laurent action on its actual pair square.
-/
theorem boundedFlatAffineSupportedDiagramLaurentHomotopy_eq (a : Under R) :
    boundedFlatAffineSupportedDiagramLaurentHomotopy j a =
      boundedFlatAffineSupportedSectionLaurentUnitHomotopy
        (inclusion j a) (inclusion j ((laurentUnderFunctor R).obj a))
        (openMap j ((laurentUnderCoefficient R).app a))
        (openMap_inclusion j ((laurentUnderCoefficient R).app a)) := rfl

/-- Every original coefficient map preserves every interval value of the actual Laurent loop. -/
theorem boundedFlatAffineSupportedDiagramLaurentHomotopy_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).map
        ((laurentUnderFunctor R).map f)).map n
        ((boundedFlatAffineSupportedDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedFlatAffineSupportedDiagramLaurentHomotopy j b).level n
        (t, ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).map f).map n x) :=
  prespectrumIsoHomotopy_square_apply
    ((boundedFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderCoefficient R).app a))
    ((boundedFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderCoefficient R).app b))
    ((boundedFlatAffineSupportedSectionModelFunctor j).map f)
    ((boundedFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderFunctor R).map f))
    (boundedFlatAffineSupportedDiagramLaurentPullbackUnitIso j a)
    (boundedFlatAffineSupportedDiagramLaurentPullbackUnitIso j b)
    (boundedFlatAffineSupportedDiagramLaurentModelSquare j f)
    (boundedFlatAffineSupportedDiagramLaurentModelUnitSquare j f) n t x

end Quillen.PerfectComplexes
