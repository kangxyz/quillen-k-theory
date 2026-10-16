/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.UnitTrackPostcompSimplex

/-! Clients of the actual chosen postcomposition unit track, its six full reference nodes,
whole primitive surfaces, original endpoints and independent loop/structure coordinates. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.LoopPrespectrum Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.UnitTrackPostcompSimplex Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace QuillenTest.UnitTrackPostcompSimplex
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(Y, ⊤))ˣ)

/-- Every original relative comparison point is recovered in every level. -/
theorem whole_family (n : ℕ) (t s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    prespectrumSimplexFamily (simplex f g r) n
      (UnitPrismParameters.parameter (t, s), x) =
      (boundedFlatPerfectUnitTrackPostcomp f g r).level n (t, (s, x)) :=
  native_lift f g r n t s x

/-- At level zero the input loop time stays independent of both relative coordinates. -/
theorem level_zero_input_loop (t s q : unitInterval)
    (x : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Z)))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Z)))) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen X)))
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen X))) from
      (boundedFlatPerfectUnitTrackPostcomp f g r).level 0 (t, (s, x))) q =
    stageSimplexBarycentric (simplex f g r) 0 (UnitPrismParameters.parameter (t, s), x q) := by
  exact (congrArg (fun y : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space 0 ↦
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen X)))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen X))) from y) q)
        (whole_family f g r 0 t s x)).symm.trans
      (prespectrumSimplexFamily_zero_apply _ _ _ _)

/-- The initial face is the original left-associated (G.trans N).trans D route. -/
theorem original_source (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    prespectrumSimplexFamily (simplex f g r) n
      ((((edge 0 1).trans (edge 1 2)).trans (edge 2 5)) s, x) =
    (((geometricTrack f g).trans (normalizationTrack f g)).trans
      (finalUnitTrack f g r)).level n (s, x) :=
  HomotopyLift.source _ (native_lift f g r) n s x

/-- The final face is the source unit followed by the unchanged binary comparison. -/
theorem original_target (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    prespectrumSimplexFamily (simplex f g r) n
      (((edge 0 3).trans ((edge 3 4).trans (edge 4 5))) s, x) =
    ((sourceUnitTrack f g r).trans ((geometricTrack f g).trans
      (normalizationTrack f g))).level n (s, x) :=
  HomotopyLift.target _ (native_lift f g r) n s x

/-- The actual original based line is fixed throughout the entire scalar surface. -/
theorem original_based_line (n : ℕ) (t s : unitInterval) :
    (boundedFlatPerfectUnitTrackPostcomp f g r).level n
      (t, (s, (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).point n)) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen X)).point n :=
  (native_lift f g r n t s _).symm.trans
    (prespectrumSimplexFamily_point (simplex f g r) n _)

/-- Comparison, path and original structure times remain independent. -/
theorem independent_structure (n : ℕ) (t s q : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    prespectrumSimplexFamily (simplex f g r) (n + 1)
      (UnitPrismParameters.parameter (t, s),
        (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).structureMap n x q) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen X)).structureMap n
      ((boundedFlatPerfectUnitTrackPostcomp f g r).level n (t, (s, x))) q :=
  (native_lift f g r (n + 1) t s _).trans
    ((boundedFlatPerfectUnitTrackPostcomp f g r).comm n t s x q)

/-- JG is the entire original equality-transported geometric pasting. -/
theorem whole_geometric_surface (n : ℕ) (t s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    prespectrumSimplexFamily (simplex f g r) n
      (UnitPrismParameters.geometric (t, s), x) =
      (geometricPasting f g r).level n (t, (s, x)) :=
  geometricPasting_lift f g r n t s x

/-- JN retains both ordered triangles and its original full endpoint transport. -/
theorem whole_normalization_surface (n : ℕ) (t s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    prespectrumSimplexFamily (simplex f g r) n
      (UnitPrismParameters.normalization (t, s), x) =
      (normalizationPasting f g r).level n (t, (s, x)) :=
  normalizationPasting_lift f g r n t s x

/-- The middle unit-shifted node is identified with its full actual reference. -/
theorem full_middle_reference : nodes f g r 4 =
    ⟨BinaryNormalizationSimplex.intermediateMap f g,
      sourceUnit f g r ≪≫ BinaryNormalizationSimplex.first f g⟩ :=
  UnitPrismNodes.middle_reference _ _ _ _ _ _ _ _ (small_geometric_unit f g r)

/-- The final unit-shifted node keeps the original alternative full reference. -/
theorem full_final_reference : nodes f g r 5 =
    ⟨BinaryNormalizationSimplex.targetMap f g,
      (BinaryNormalizationSimplex.first f g ≪≫ middleUnit f g r) ≪≫
        BinaryNormalizationSimplex.second f g⟩ :=
  UnitPrismNodes.final_reference _ _ _ _ _ _ _ _ (small_normalization_unit f g r)

end QuillenTest.UnitTrackPostcompSimplex
