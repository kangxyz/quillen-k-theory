/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentHomotopy
public import Quillen.Algebra.Polynomial.LaurentUnderSquare

/-!
# The original Laurent-unit track on relative-open sections

The coarse Model diagram uses exactly the original section functors and scalar automorphisms.
The actual original Laurent coefficient equation proves the transformation square; its original
realization supplies the whole coefficient-natural loop, including degree zero. The genuine
fixed-open pullbacks and both original Laurent legs remain unchanged.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original target Laurent unit acts on the unchanged relative-open coefficient functor. -/
def boundedFlatAffineSectionOpenDiagramLaurentPullbackUnitIso (a : Under R) :
    ((boundedFlatAffineSectionOpenModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor ≅
    ((boundedFlatAffineSectionOpenModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor :=
  Quillen.FunctorIdentityAutomorphism.onFunctor
    ((boundedFlatAffineSectionOpenModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor
    (boundedFlatAffineSectionLaurentUnitIso a.right)

/-- The coarse action is exactly the existing original section Laurent pullback action. -/
theorem boundedFlatAffineSectionOpenDiagramLaurentPullbackUnitIso_eq (a : Under R) :
    boundedFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a =
      boundedFlatAffineSectionLaurentPullbackUnitIso a.right := rfl

/-- The unchanged Laurent coefficient square is a literal square of actual coarse Models. -/
theorem boundedFlatAffineSectionOpenDiagramLaurentModelSquare {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app a) ≫
        (boundedFlatAffineSectionOpenModelFunctor j).map ((laurentUnderFunctor R).map f) =
      (boundedFlatAffineSectionOpenModelFunctor j).map f ≫
        (boundedFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app b) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (boundedFlatAffineSectionOpenModelFunctor j).map
    ((laurentUnderCoefficient R).naturality f).symm

/-- The actual coarse coefficient square intertwines the same original Laurent automorphisms. -/
theorem boundedFlatAffineSectionOpenDiagramLaurentModelUnitSquare {a b : Under R} (f : a ⟶ b) :
    Functor.whiskerRight (boundedFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a).hom
        ((boundedFlatAffineSectionOpenModelFunctor j).map
          ((laurentUnderFunctor R).map f)).functor ≫
        eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineSectionOpenDiagramLaurentModelSquare j f)) =
      eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineSectionOpenDiagramLaurentModelSquare j f)) ≫
        Functor.whiskerLeft ((boundedFlatAffineSectionOpenModelFunctor j).map f).functor
          (boundedFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j b).hom :=
  Quillen.FunctorIdentityAutomorphism.onFunctor_whisker_square _ _ _ _ _ _ _
    (boundedFlatAffineSectionLaurentUnitIso_coefficient f.right)

/-- The original scalar action supplies the entire relative-open Laurent loop. -/
def boundedFlatAffineSectionOpenDiagramLaurentHomotopy (a : Under R) :
    Homotopy
      ((boundedFlatAffineSectionOpenPrespectrumFunctor j).map ((laurentUnderCoefficient R).app a))
      ((boundedFlatAffineSectionOpenPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a)) :=
  prespectrumIsoHomotopy
    ((boundedFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app a))
    (boundedFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a)

/-- Every coefficient map preserves the whole original Laurent track at the identical time. -/
theorem boundedFlatAffineSectionOpenDiagramLaurentHomotopy_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineSectionOpenPrespectrumFunctor j).map
        ((laurentUnderFunctor R).map f)).map n
        ((boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedFlatAffineSectionOpenDiagramLaurentHomotopy j b).level n
        (t, ((boundedFlatAffineSectionOpenPrespectrumFunctor j).map f).map n x) :=
  prespectrumIsoHomotopy_square_apply
    ((boundedFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app a))
    ((boundedFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app b))
    ((boundedFlatAffineSectionOpenModelFunctor j).map f)
    ((boundedFlatAffineSectionOpenModelFunctor j).map ((laurentUnderFunctor R).map f))
    (boundedFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a)
    (boundedFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j b)
    (boundedFlatAffineSectionOpenDiagramLaurentModelSquare j f)
    (boundedFlatAffineSectionOpenDiagramLaurentModelUnitSquare j f) n t x

end Quillen.PerfectComplexes
