/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionLaurentUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionModel
public import Quillen.CategoryTheory.Functor.IdentityAutomorphismSquare
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIsoNaturality

/-!
# The original Laurent-unit track on the actual full-open section diagram

The actual zero-preserving Laurent coefficient Model map carries the pointwise original
forward-unit automorphism. Its literal Model square and actual categorical automorphism square
retain the original coefficient maps and endpoint equality transports. Their realization gives
the whole coefficient-natural prespectrum track, including degree zero and all structure data.
The original normalized null and inherited Bass seed comparisons remain separate obligations.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original target Laurent unit acts on the actual full-open coefficient functor. -/
def boundedFlatAffineFullOpenSectionDiagramLaurentPullbackUnitIso (a : Under R) :
    ((boundedFlatAffineFullOpenSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor ≅
    ((boundedFlatAffineFullOpenSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor :=
  Quillen.FunctorIdentityAutomorphism.onFunctor
    ((boundedFlatAffineFullOpenSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor
    (boundedFlatAffineFullOpenSectionLaurentUnitIso j a)

/-- The original Laurent coefficient square commutes for the actual full-open Models. -/
theorem boundedFlatAffineFullOpenSectionDiagramLaurentModelSquare {a b : Under R}
    (f : a ⟶ b) :
    (boundedFlatAffineFullOpenSectionModelFunctor j).map ((laurentUnderCoefficient R).app a) ≫
        (boundedFlatAffineFullOpenSectionModelFunctor j).map ((laurentUnderFunctor R).map f) =
      (boundedFlatAffineFullOpenSectionModelFunctor j).map f ≫
        (boundedFlatAffineFullOpenSectionModelFunctor j).map
          ((laurentUnderCoefficient R).app b) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (boundedFlatAffineFullOpenSectionModelFunctor j).map
    ((laurentUnderCoefficient R).naturality f).symm

/-- The actual coefficient square intertwines the same original Laurent automorphisms. -/
theorem boundedFlatAffineFullOpenSectionDiagramLaurentModelUnitSquare {a b : Under R}
    (f : a ⟶ b) :
    Functor.whiskerRight
        (boundedFlatAffineFullOpenSectionDiagramLaurentPullbackUnitIso j a).hom
        ((boundedFlatAffineFullOpenSectionModelFunctor j).map
          ((laurentUnderFunctor R).map f)).functor ≫
        eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineFullOpenSectionDiagramLaurentModelSquare j f)) =
      eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineFullOpenSectionDiagramLaurentModelSquare j f)) ≫
        Functor.whiskerLeft ((boundedFlatAffineFullOpenSectionModelFunctor j).map f).functor
          (boundedFlatAffineFullOpenSectionDiagramLaurentPullbackUnitIso j b).hom := by
  unfold boundedFlatAffineFullOpenSectionDiagramLaurentPullbackUnitIso
  exact Quillen.FunctorIdentityAutomorphism.onFunctor_whisker_square
    ((boundedFlatAffineFullOpenSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).functor
    ((boundedFlatAffineFullOpenSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app b)).functor
    ((boundedFlatAffineFullOpenSectionModelFunctor j).map f).functor
    ((boundedFlatAffineFullOpenSectionModelFunctor j).map
      ((laurentUnderFunctor R).map f)).functor
    (eqToHom (congrArg Model.Hom.functor
      (boundedFlatAffineFullOpenSectionDiagramLaurentModelSquare j f)))
    (boundedFlatAffineFullOpenSectionLaurentUnitIso j a)
    (boundedFlatAffineFullOpenSectionLaurentUnitIso j b)
    (boundedFlatAffineFullOpenSectionLaurentUnitIso_coefficient j f)

/-- The original scalar action gives the whole actual full-open Laurent coefficient track. -/
def boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy (a : Under R) :
    Homotopy
      ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a))
      ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a)) :=
  prespectrumIsoHomotopy
    ((boundedFlatAffineFullOpenSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a))
    (boundedFlatAffineFullOpenSectionDiagramLaurentPullbackUnitIso j a)

/-- Every original coefficient map preserves every level and the identical unit-action time. -/
theorem boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map
        ((laurentUnderFunctor R).map f)).map n
        ((boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j b).level n
        (t, ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map f).map n x) :=
  prespectrumIsoHomotopy_square_apply
    ((boundedFlatAffineFullOpenSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a))
    ((boundedFlatAffineFullOpenSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app b))
    ((boundedFlatAffineFullOpenSectionModelFunctor j).map f)
    ((boundedFlatAffineFullOpenSectionModelFunctor j).map ((laurentUnderFunctor R).map f))
    (boundedFlatAffineFullOpenSectionDiagramLaurentPullbackUnitIso j a)
    (boundedFlatAffineFullOpenSectionDiagramLaurentPullbackUnitIso j b)
    (boundedFlatAffineFullOpenSectionDiagramLaurentModelSquare j f)
    (boundedFlatAffineFullOpenSectionDiagramLaurentModelUnitSquare j f) n t x

end Quillen.PerfectComplexes
