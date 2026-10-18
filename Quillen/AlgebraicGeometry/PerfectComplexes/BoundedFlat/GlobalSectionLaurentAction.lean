/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionLaurentScalar
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassSeed

/-! # The original Laurent action on global section rows -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass Quillen.LoopPrespectrum
open Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}}

/-- The actual coefficient row of the global section Model diagram. -/
def globalRow (P : Over (Spec R)) : Under R ⥤ Model.{u+1} :=
  row P ⋙ AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R ⋙ globalModel

/-- Original restriction from the global row to the existing coefficient-first row. -/
def rowRestriction (P : Over (Spec R)) :
    globalRow P ⟶ boundedFlatCoefficientSectionModelRow P :=
  Functor.whiskerLeft (row P) (coefficientRestriction R)

/-- The same forward Laurent coordinate lifted through global identity evaluation. -/
def globalLaurentUnit (P : Over (Spec R)) (a : Under R) :
    𝟭 ((globalRow P).obj ((laurentUnderFunctor R).obj a)) ≅
      𝟭 ((globalRow P).obj ((laurentUnderFunctor R).obj a)) :=
  globalUnit ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj
    (op P, (laurentUnderFunctor R).obj a))
    (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
      (laurentGlobalUnit a.right))

/-- The original Laurent coordinate is preserved under every coefficient arrow. -/
theorem globalLaurentUnit_naturality (P : Over (Spec R)) {a b : Under R} (g : a ⟶ b) :
    Preserves ((globalRow P).map ((laurentUnderFunctor R).map g)).functor
      (globalLaurentUnit P a) (globalLaurentUnit P b) := by
  exact globalUnit_reindex_of_eq
    ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).map
      (show (op P, (laurentUnderFunctor R).obj a) ⟶
          (op P, (laurentUnderFunctor R).obj b) from
        (𝟙 (op P), (laurentUnderFunctor R).map g)))
    _ _ (globalLaurentScalar_map P g)

/-- The global Laurent action uses the original forward coordinate and no chosen replacement. -/
def globalLaurentAction (P : Over (Spec R)) : LaurentSeed.ModelAction (globalRow P) where
  unit := globalLaurentUnit P
  naturality := globalLaurentUnit_naturality P

/-- Actual restriction preserves the original Laurent action at every coefficient. -/
theorem rowRestriction_unit (P : Over (Spec R)) (a : Under R) :
    Preserves ((rowRestriction P).app ((laurentUnderFunctor R).obj a)).functor
      ((globalLaurentAction P).unit a)
      ((boundedFlatCoefficientAmbientLaurentAction P).unit a) := by
  dsimp only [rowRestriction, Functor.whiskerLeft_app, globalLaurentAction,
    globalLaurentUnit, boundedFlatCoefficientAmbientLaurentAction,
    boundedFlatCoefficientSectionLaurentUnitIso]
  exact coefficientRestriction_unit_preserves R (op P, (laurentUnderFunctor R).obj a)
    (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
      (laurentGlobalUnit a.right))

/-- Every value of the original Laurent track commutes with actual restriction. -/
theorem rowRestriction_track (P : Over (Spec R)) (a : Under R) (n : ℕ)
    (t : unitInterval) (x : (prespectrum ((globalRow P).obj a)).space n) :
    (prespectrumMap ((rowRestriction P).app ((laurentUnderFunctor R).obj a))).map n
      (((globalLaurentAction P).track.homotopy a).level n (t, x)) =
    ((boundedFlatCoefficientAmbientLaurentAction P).track.homotopy a).level n
      (t, (prespectrumMap ((rowRestriction P).app a)).map n x) :=
  LaurentSeed.ModelAction.track_square (globalLaurentAction P)
    (boundedFlatCoefficientAmbientLaurentAction P) (rowRestriction P)
    (rowRestriction_unit P) a n t x

/-- The original scalar/null seed commutes with actual restriction as a whole natural map. -/
theorem rowRestriction_seed (P : Over (Spec R)) :
    (globalLaurentAction P).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (rowRestriction P) prespectrumFunctor) =
    Functor.whiskerRight (rowRestriction P) prespectrumFunctor ≫
      (boundedFlatCoefficientAmbientLaurentAction P).track.seed :=
  LaurentSeed.Track.seed_square _ _ _ (rowRestriction_track P)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
