/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarCofiberProjectionTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarCofiberInclusionDiagonal
public import Quillen.Waldhausen.Additivity.EndpointTransformationSquare
public import Quillen.Topology.Realization.HomotopySquare
public import Quillen.Waldhausen.SConstruction.Iterated.RelativeHomotopyRealization

/-!
# Whole ordinary and diagonal scalar projection triangles

The actual small-model level-one triangle is transported through its original homeomorphisms.
Every point, both homotopy times and the full relative boundary are retained. The old diagonal
inclusion cylinder is identified through the actual bisimplicial diagonal isomorphism, before
passing to homotopy groups or cancelling subdivision.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.Waldhausen.Additivity Quillen.LoopPrespectrum
open scoped Topology Simplicial
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
local notation "V" => perfectWaldhausen X
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "hF" => changeWeak_exact (perfectOpenNested j)
local notation "hM" =>
  Additivity.IsCofibrationSequence.exactG (perfectOpenScalarCofibrationSequence j r)

/-- The actual ordinary scalar cylinder after its original canonical conjugation. -/
def perfectOpenScalarNormalizedRealizationHomotopy :
    (deloopingMap (hF).rebase).hom.Homotopy (deloopingMap (hF).rebase).hom :=
  weakNaturalTransformationRealizationHomotopy V W (hF).rebase (hF).rebase
    (normalizedWeakTransformation hF hF (perfectGlobalScalar X r))
    (normalizedWeakTransformation_weak hF hF (perfectGlobalScalar X r)
      (perfectGlobalScalar_openWeak j r q hq))

/-- The entire normalized scalar realization track is the same original spectrum level one. -/
theorem perfectOpenScalarNormalizedRealizationHomotopy_level_one
    (t : unitInterval) (x : (V).Delooping) :
    (perfectOpenScalarPrespectrumHomotopy j r q hq).level 1
        (t, (V).smallModelDeloopingHomeomorph x) =
      (W).smallModelDeloopingHomeomorph
        (perfectOpenScalarNormalizedRealizationHomotopy j r q hq (t, x)) :=
  originalPrespectrumTransformationHomotopy_level_one V W _ _ _ _ _ _ t x

/-- The original half-time concatenation survives the same level-one transport pointwise. -/
theorem perfectOpenScalarProjectionConcatenation_level_one
    (t : unitInterval) (x : (V).Delooping) :
    ((perfectOpenScalarInclusionHomotopy j r q hq).trans
        (perfectOpenScalarProjectionHomotopy j r)).level 1
        (t, (V).smallModelDeloopingHomeomorph x) =
      (W).smallModelDeloopingHomeomorph
        (((perfectOpenScalarInclusionRealizationHomotopy j r q hq).trans
          (perfectOpenScalarProjectionRealizationHomotopy j r)) (t, x)) := by
  change (((perfectOpenScalarInclusionHomotopy j r q hq).levelHomotopy 1).trans
    ((perfectOpenScalarProjectionHomotopy j r).levelHomotopy 1))
    (t, (V).smallModelDeloopingHomeomorph x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact perfectOpenScalarInclusionHomotopy_level_one j r q hq _ x
  · exact perfectOpenScalarProjectionHomotopy_level_one j r _ x

/-- The literal ordinary map underlying the transported level-one triangle. -/
def perfectOpenScalarProjectionRealizationTriangleMap :
    C(unitInterval × (unitInterval × (V).Delooping), (W).Delooping) :=
  ContinuousMap.comp
    (β := (originalPrespectrum W).space 1)
    (toContinuousMap (W).smallModelDeloopingHomeomorph.symm)
    (ContinuousMap.comp
      (β := unitInterval × (unitInterval × (originalPrespectrum V).space 1))
      (toContinuousMap ((perfectOpenScalarProjectionCompositionTrack j r q hq).level 1))
      (ContinuousMap.prodMap (ContinuousMap.id unitInterval)
        (ContinuousMap.prodMap (ContinuousMap.id unitInterval)
          (toContinuousMap (V).smallModelDeloopingHomeomorph))))

/-- Identity at the continuous-map level, before evaluating either time. -/
private theorem scalarTriangleMap_eq :
    perfectOpenScalarProjectionRealizationTriangleMap j r q hq =
      ContinuousMap.comp
        (β := (originalPrespectrum W).space 1)
        (toContinuousMap (W).smallModelDeloopingHomeomorph.symm)
        (ContinuousMap.comp
          (β := unitInterval × (unitInterval × (originalPrespectrum V).space 1))
          (toContinuousMap ((perfectOpenScalarProjectionCompositionTrack j r q hq).level 1))
          (ContinuousMap.prodMap (ContinuousMap.id unitInterval)
            (ContinuousMap.prodMap (ContinuousMap.id unitInterval)
              (toContinuousMap (V).smallModelDeloopingHomeomorph)))) := rfl

/-- Keep the exact endpoint type while checking evaluation with a variable triangle. -/
private theorem scalarTriangleLiteral_apply_of
    (J : ((perfectOpenScalarPrespectrumHomotopy j r q hq).level 1).HomotopyRel
      (((perfectOpenScalarInclusionHomotopy j r q hq).trans
        (perfectOpenScalarProjectionHomotopy j r)).level 1)
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = (originalPrespectrum V).point 1})
    (a t : unitInterval) (x : (V).Delooping) :
    (
      ContinuousMap.comp
        (β := (originalPrespectrum W).space 1)
        (toContinuousMap (W).smallModelDeloopingHomeomorph.symm)
        (ContinuousMap.comp
          (β := unitInterval × (unitInterval × (originalPrespectrum V).space 1))
          (toContinuousMap J)
          (ContinuousMap.prodMap (ContinuousMap.id unitInterval)
            (ContinuousMap.prodMap (ContinuousMap.id unitInterval)
              (toContinuousMap (V).smallModelDeloopingHomeomorph))))) (a, (t, x)) =
      (W).smallModelDeloopingHomeomorph.symm
        (J (a, (t, (V).smallModelDeloopingHomeomorph x))) := rfl

/-- The underlying ordinary map keeps both original times and every point. -/
theorem perfectOpenScalarProjectionRealizationTriangleMap_apply
    (a t : unitInterval) (x : (V).Delooping) :
    perfectOpenScalarProjectionRealizationTriangleMap j r q hq (a, (t, x)) =
      (W).smallModelDeloopingHomeomorph.symm
        ((perfectOpenScalarProjectionCompositionTrack j r q hq).level 1
          (a, (t, (V).smallModelDeloopingHomeomorph x))) :=
  (congrArg
    (fun F : C(unitInterval × (unitInterval × (V).Delooping), (W).Delooping) =>
      F (a, (t, x))) (scalarTriangleMap_eq j r q hq)).trans
    (scalarTriangleLiteral_apply_of j r q hq
      ((perfectOpenScalarProjectionCompositionTrack j r q hq).level 1) a t x)


/-- The zero endpoint is the original normalized scalar cylinder. -/
theorem perfectOpenScalarProjectionRealizationTriangleMap_zero
    (z : unitInterval × (V).Delooping) :
    perfectOpenScalarProjectionRealizationTriangleMap j r q hq (0, z) =
      perfectOpenScalarNormalizedRealizationHomotopy j r q hq z := by
  rw [perfectOpenScalarProjectionRealizationTriangleMap_apply]
  exact
    (congrArg (W).smallModelDeloopingHomeomorph.symm
      (((perfectOpenScalarProjectionCompositionTrack j r q hq).level 1).apply_zero
        (z.1, (V).smallModelDeloopingHomeomorph z.2))).trans
      ((congrArg (W).smallModelDeloopingHomeomorph.symm
        (perfectOpenScalarNormalizedRealizationHomotopy_level_one j r q hq z.1 z.2)).trans
          ((W).smallModelDeloopingHomeomorph.symm_apply_apply _))

/-- The one endpoint is the original concatenation of inclusion and projection. -/
theorem perfectOpenScalarProjectionRealizationTriangleMap_one
    (z : unitInterval × (V).Delooping) :
    perfectOpenScalarProjectionRealizationTriangleMap j r q hq (1, z) =
      ((perfectOpenScalarInclusionRealizationHomotopy j r q hq).trans
        (perfectOpenScalarProjectionRealizationHomotopy j r)) z := by
  rw [perfectOpenScalarProjectionRealizationTriangleMap_apply]
  exact
    (congrArg (W).smallModelDeloopingHomeomorph.symm
      (((perfectOpenScalarProjectionCompositionTrack j r q hq).level 1).apply_one
        (z.1, (V).smallModelDeloopingHomeomorph z.2))).trans
      ((congrArg (W).smallModelDeloopingHomeomorph.symm
        (perfectOpenScalarProjectionConcatenation_level_one j r q hq z.1 z.2)).trans
          ((W).smallModelDeloopingHomeomorph.symm_apply_apply _))

/-- The same endpoint-and-basepoint union is fixed for every triangle time. -/
theorem perfectOpenScalarProjectionRealizationTriangleMap_relative
    (a : unitInterval) (z : unitInterval × (V).Delooping)
    (hz : z.1 = 0 ∨ z.1 = 1 ∨ z.2 = (V).kBasepoint) :
    perfectOpenScalarProjectionRealizationTriangleMap j r q hq (a, z) =
      perfectOpenScalarNormalizedRealizationHomotopy j r q hq z := by
  rw [perfectOpenScalarProjectionRealizationTriangleMap_apply]
  let J := (perfectOpenScalarProjectionCompositionTrack j r q hq).level 1
  have hz' : z.1 = 0 ∨ z.1 = 1 ∨
      (V).smallModelDeloopingHomeomorph z.2 = (originalPrespectrum V).point 1 := by
    rcases hz with hz | hz | hz
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr ((congrArg (V).smallModelDeloopingHomeomorph hz).trans
        (V).smallModelDeloopingHomeomorph_basepoint))
  exact (congrArg (W).smallModelDeloopingHomeomorph.symm (J.eq_fst a hz')).trans
    ((congrArg (W).smallModelDeloopingHomeomorph.symm
      (perfectOpenScalarNormalizedRealizationHomotopy_level_one j r q hq z.1 z.2)).trans
        ((W).smallModelDeloopingHomeomorph.symm_apply_apply _))

/-- The actual whole triangle on original ordinary spaces, relative to both endpoints and zero. -/
def perfectOpenScalarProjectionRealizationTriangle :
    (perfectOpenScalarNormalizedRealizationHomotopy j r q hq).toContinuousMap.HomotopyRel
      ((perfectOpenScalarInclusionRealizationHomotopy j r q hq).trans
        (perfectOpenScalarProjectionRealizationHomotopy j r)).toContinuousMap
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = (V).kBasepoint} where
  toContinuousMap := perfectOpenScalarProjectionRealizationTriangleMap j r q hq
  map_zero_left := perfectOpenScalarProjectionRealizationTriangleMap_zero j r q hq
  map_one_left := perfectOpenScalarProjectionRealizationTriangleMap_one j r q hq
  prop' a z hz := perfectOpenScalarProjectionRealizationTriangleMap_relative j r q hq a z hz

/-- Both times of the ordinary triangle are literally the original level-one triangle. -/
theorem perfectOpenScalarProjectionRealizationTriangle_apply
    (a t : unitInterval) (x : (V).Delooping) :
    perfectOpenScalarProjectionRealizationTriangle j r q hq (a, (t, x)) =
      (W).smallModelDeloopingHomeomorph.symm
        ((perfectOpenScalarProjectionCompositionTrack j r q hq).level 1
          (a, (t, (V).smallModelDeloopingHomeomorph x))) :=
  perfectOpenScalarProjectionRealizationTriangleMap_apply j r q hq a t x


end Quillen.PerfectComplexes
