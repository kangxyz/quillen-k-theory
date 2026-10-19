/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityMap
public import Quillen.Topology.Prespectrum.NullLoopNaturality

/-!
# The literal positive-cone support of the global raw identity seed

The unchanged global source-null and forward seed factor through the actual positive-chart
cone. Its strict inclusion retains every original cylinder time. The original raw input map
also preserves this support, without modifying its chart comparison or either null leg.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputIdentityPositive
variable (X : Scheme.{u})

/-- The genuine positive-chart arrow whose cone supports the original seed. -/
abbrev chart := boundedFlatPerfectPrespectrumMap (plus.app X)

/-- The strict positive-chart square uses the actual span inclusion and Laurent identity. -/
def inclusionSquare : Arrow.mk (chart X) ⟶ Arrow.mk (comparison X) :=
  Arrow.homMk
    (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (projection.app X))
      (boundedFlatPerfectPrespectrumMap (projection.app X))) (𝟙 _)
    (by apply Hom.ext; funext n; ext x; rfl)

/-- The positive cone enters through its strict square, with no extra path segment. -/
def inclusion : mappingCone (chart X) ⟶ mappingCone (comparison X) :=
  mappingConeMap (inclusionSquare X)

/-- The supported Laurent inclusion is literally the original one. -/
theorem inclusion_inclusion :
    mappingConeInclusion (chart X) ≫ inclusion X = mappingConeInclusion (comparison X) := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- Every positive cylinder point retains its original height and polynomial point. -/
theorem inclusion_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj X))).space n) :
    (inclusion X).map n (ReducedMappingCone.cylinder _ _ ((chart X).map n) (s, x)) =
      ReducedMappingCone.cylinder _ _ ((comparison X).map n)
        (s, (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (projection.app X))
          (boundedFlatPerfectPrespectrumMap (projection.app X))).map n x) := rfl

/-- Both original null legs already live in the positive cone. -/
def sourceNull : Homotopy
    (boundedFlatPerfectPrespectrumMap (laurentProjection.app X) ≫
      mappingConeInclusion (chart X))
    (zeroHom (originalPrespectrum (boundedFlatPerfectWaldhausen X)) (mappingCone (chart X))) :=
  ((plusHomotopy X).postcomp (mappingConeInclusion (chart X))).trans
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (projection.app X))
      (mappingConeHomotopy (chart X)))

/-- The complete supported null evaluates to the fixed original two-leg source-null. -/
theorem sourceNull_factor (n : ℕ) :
    ((sourceNull X).postcomp (inclusion X)).level n =
      (GlobalRawBass.sourceNull X).level n := by
  change ((((plusHomotopy X).postcomp (mappingConeInclusion (chart X))).trans
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (projection.app X))
      (mappingConeHomotopy (chart X)))).postcomp (inclusion X)).level n = _
  rw [Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr <;> rfl

/-- An auxiliary factor of the existing transition, using its original unit and null word. -/
def seed : originalPrespectrum (boundedFlatPerfectWaldhausen X) ⟶
    parameterLooping (mappingCone (chart X)) :=
  ((unitHomotopy X).postcomp (mappingConeInclusion (chart X))).nullLoopMap (sourceNull X)

/-- The actual positive seed maps exactly to the fixed global transition. -/
theorem seed_factor : seed X ≫ parameterLoopingMap (inclusion X) = transition X := by
  have h := Homotopy.nullLoopMap_naturality
    (𝟙 (originalPrespectrum (boundedFlatPerfectWaldhausen X))) (inclusion X)
    ((unitHomotopy X).postcomp (mappingConeInclusion (chart X)))
    ((unitHomotopy X).postcomp (mappingConeInclusion (comparison X)))
    (sourceNull X) (GlobalRawBass.sourceNull X)
    (fun _ ↦ rfl) (sourceNull_factor X)
  simpa only [Category.id_comp, seed, transition] using h

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual positive input cone map uses the original positive geometric square. -/
def coneMap : mappingCone (chart Y) ⟶ mappingCone (chart X) :=
  mappingConeSquareMap (chart Y) (chart X)
    (boundedFlatPerfectPrespectrumMap (polynomial.map g))
    (boundedFlatPerfectPrespectrumMap (laurent.map g)) (plusSquareHomotopy g)

/-- Both halves of the actual positive input null factor to the fixed whole input null. -/
theorem coneMapNull_factor (n : ℕ) :
    ((mappingConeSquareNullHomotopy (chart Y) (chart X)
      (boundedFlatPerfectPrespectrumMap (polynomial.map g))
      (boundedFlatPerfectPrespectrumMap (laurent.map g)) (plusSquareHomotopy g)).postcomp
        (inclusion X)).level n =
    (Homotopy.precomp
      (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (projection.app Y))
        (boundedFlatPerfectPrespectrumMap (projection.app Y)))
      (mappingConeSquareNullHomotopy (comparison Y) (comparison X) (spanMap g)
        (boundedFlatPerfectPrespectrumMap (laurent.map g))
        (inputComparisonHomotopy g))).level n := by
  simp only [mappingConeSquareNullHomotopy, Homotopy.postcomp_trans, Homotopy.precomp_trans]
  apply Homotopy.trans_level_congr <;> rfl

/-- The original raw cone map preserves the strict positive support on all cone points. -/
theorem coneMap_factor :
    inclusion Y ≫ GlobalRawBass.coneMap g = coneMap g ≫ inclusion X := by
  apply mappingCone_hom_ext
  · apply Hom.ext
    funext n
    ext x
    rfl
  · intro n s x
    exact (DFunLike.congr_fun (coneMapNull_factor g n) (s, x)).symm

end Quillen.PerfectComplexes.GlobalRawBass.InputIdentityPositive
