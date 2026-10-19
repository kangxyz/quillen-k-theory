/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputPasting
public import Quillen.Topology.Prespectrum.PushoutMovingHomotopy
public import Quillen.Topology.Prespectrum.ConeHomotopySquare
public import Quillen.Topology.Prespectrum.HomotopySquareInterchange
public import Quillen.Topology.Prespectrum.HomotopySquareBoundary

/-!
# The independently constructed global raw Bass input map

The genuine original geometric overlap descends through the actual polynomial double cylinder,
Laurent comparison, reduced cone and parameter loops. This constructs `GlobalRawBass.map`
contravariantly for each scheme arrow, including all chart and cylinder values. No strict
functor, identity/composition law, or higher raw tower is asserted.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The target track is the whole original polynomial-span cylinder followed by Bass comparison. -/
theorem inputTargetDescTrack_level (n : ℕ) :
    (inputTargetDescTrack g).level n =
      ((HomotopyPushout.mapSquareHomotopy
        (boundedFlatPerfectPrespectrumMap (projection.app Y))
        (boundedFlatPerfectPrespectrumMap (projection.app Y))
        (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap g)
        (boundedFlatPerfectPrespectrumMap (polynomial.map g))
        (boundedFlatPerfectPrespectrumMap (polynomial.map g))
        (polynomialSquareHomotopy g)
          (polynomialSquareHomotopy g)).postcomp
          (comparison X)).level n := by
  simp only [inputTargetDescTrack, Homotopy.cast_level,
    inputTargetTrack, HomotopyPushout.mapSquareHomotopy,
    Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- The source descent equals the literal original Bass comparison followed by Laurent change. -/
theorem inputSourceDesc_eq :
    HomotopyPushout.desc
      (boundedFlatPerfectPrespectrumMap (projection.app Y))
      (boundedFlatPerfectPrespectrumMap (projection.app Y))
      (boundedFlatPerfectPrespectrumMap (plus.app Y) ≫
        boundedFlatPerfectPrespectrumMap (laurent.map g))
      (boundedFlatPerfectPrespectrumMap (minus.app Y) ≫
        boundedFlatPerfectPrespectrumMap (laurent.map g))
      (inputSourceDescTrack g) =
    comparison Y ≫
      boundedFlatPerfectPrespectrumMap (laurent.map g) := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    rfl

/-- The target descent equals the original polynomial-span map followed by Bass comparison. -/
theorem inputTargetDesc_eq :
    HomotopyPushout.desc
      (boundedFlatPerfectPrespectrumMap (projection.app Y))
      (boundedFlatPerfectPrespectrumMap (projection.app Y))
      (boundedFlatPerfectPrespectrumMap (polynomial.map g) ≫
        boundedFlatPerfectPrespectrumMap (plus.app X))
      (boundedFlatPerfectPrespectrumMap (polynomial.map g) ≫
        boundedFlatPerfectPrespectrumMap (minus.app X))
      (inputTargetDescTrack g) =
    spanMap g ≫ comparison X
      := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    exact DFunLike.congr_fun (inputTargetDescTrack_level g n) (s, x)

/-- The actual geometric moving square descends to the two unchanged scheme-arrow composites. -/
def inputComparisonHomotopy :
    Homotopy (comparison Y ≫
      boundedFlatPerfectPrespectrumMap (laurent.map g))
      (spanMap g ≫ comparison X) :=
  (HomotopyPushout.descSquareHomotopy
    (boundedFlatPerfectPrespectrumMap (projection.app Y))
    (boundedFlatPerfectPrespectrumMap (projection.app Y))
    (plusSquareHomotopy g) (minusSquareHomotopy g)
    (inputDescPasting g).toSquare).cast
      (inputSourceDesc_eq g) (inputTargetDesc_eq g)

/-- The left polynomial endpoint moves through its unchanged positive Laurent square. -/
theorem inputComparisonHomotopy_inl (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (polynomial.obj Y))).space n) :
    (inputComparisonHomotopy g).level n
      (r, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (projection.app Y))
        (boundedFlatPerfectPrespectrumMap (projection.app Y))).map n x) =
      (plusSquareHomotopy g).level n (r, x) := rfl

/-- The right polynomial endpoint moves through its distinct negative Laurent square. -/
theorem inputComparisonHomotopy_inr (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (polynomial.obj Y))).space n) :
    (inputComparisonHomotopy g).level n
      (r, (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (projection.app Y))
        (boundedFlatPerfectPrespectrumMap (projection.app Y))).map n x) =
      (minusSquareHomotopy g).level n (r, x) := rfl

/-- The whole actual cylinder retains the square constructed from the proved geometric pasting. -/
theorem inputComparisonHomotopy_cylinder (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    (inputComparisonHomotopy g).level n
      (r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (projection.app Y))
        (boundedFlatPerfectPrespectrumMap (projection.app Y)) n (s, x)) =
      (inputDescPasting g).toSquare.level n (r, (s, x)) := rfl

/-- The original relative comparison is recovered on every collapsed parameter-square point. -/
theorem inputComparisonHomotopy_collapse (n : ℕ)
    (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    (inputComparisonHomotopy g).level n
      ((Quillen.ThreeSideSquare.collapse z).1, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (projection.app Y))
        (boundedFlatPerfectPrespectrumMap (projection.app Y)) n
          ((Quillen.ThreeSideSquare.collapse z).2, x)) =
      (inputDescPasting g).level n (z.1, (z.2, x)) :=
  (inputDescPasting g).toSquare_collapse n z x

/-- The genuine comparison-map homotopy induces an actual map of the original Bass square cones. -/
def coneMap :
    mappingCone (comparison Y) ⟶
      mappingCone (comparison X) :=
  mappingConeSquareMap _ _ (spanMap g)
    (boundedFlatPerfectPrespectrumMap (laurent.map g))
    (inputComparisonHomotopy g)

/-- Parameter-correct looping gives a map between the actual one-step Bass spectra. -/
def map : step Y ⟶ step X :=
  parameterLoopingMap (coneMap g)

/-- The literal Laurent inclusion commutes with the actual scheme-arrow cone map. -/
lemma coneMap_inclusion :
    mappingConeInclusion (comparison Y) ≫
      coneMap g =
      boundedFlatPerfectPrespectrumMap (laurent.map g) ≫
        mappingConeInclusion (comparison X) :=
  mappingConeSquareMap_inclusion _ _ _ _ _

/-- The whole cone cylinder retains the actual input comparison and target cone null track. -/
lemma coneMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (projection.app Y))
      (boundedFlatPerfectPrespectrumMap (projection.app Y))).space n) :
    (coneMap g).map n
      (ReducedMappingCone.cylinder _ _ ((comparison Y).map n)
        (s, x)) =
    (((inputComparisonHomotopy g).postcomp
      (mappingConeInclusion (comparison X))).trans
      (Homotopy.precomp (spanMap g)
        (mappingConeHomotopy (comparison X)))).level n (s, x) :=
          rfl

/-- The unchanged positive source leg maps to its literal polynomial endpoint. -/
theorem sourceLeg_spanMap :
    sourceLeg Y ≫ spanMap g =
      (boundedFlatPerfectPrespectrumMap (projection.app Y) ≫
        boundedFlatPerfectPrespectrumMap
          (polynomial.map g)) ≫
          HomotopyPushout.inl
            (boundedFlatPerfectPrespectrumMap (projection.app X))
            (boundedFlatPerfectPrespectrumMap (projection.app X)) := by
  unfold sourceLeg
  rw [Category.assoc, inl_spanMap, Category.assoc]

/-- The original geometric polynomial square moves the unchanged positive source leg. -/
def sourceLegInputHomotopy :
    Homotopy
      (sourceLeg Y ≫ spanMap g)
      (boundedFlatPerfectPrespectrumMap g ≫
        sourceLeg X) :=
  ((polynomialSquareHomotopy g).postcomp
    (HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (projection.app X))
      (boundedFlatPerfectPrespectrumMap (projection.app X)))).cast
      (sourceLeg_spanMap g).symm (Category.assoc _ _ _)

/-- Source movement and the original raw cone contraction keep their parameters independent. -/
def sourceLegInputConeSquare :=
  Homotopy.Square.interchange (sourceLegInputHomotopy g)
    (mappingConeHomotopy (comparison X))

theorem sourceLegInputConeSquare_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    (sourceLegInputConeSquare g).level n (r, (s, x)) =
      (mappingConeHomotopy (comparison X)).level n
        (s, (sourceLegInputHomotopy g).level n (r, x)) := rfl

/-- The positive source-leg movement retains its complete original cone boundary. -/
def sourceLegInputConeBoundary :=
  (sourceLegInputConeSquare g).toBoundary

/-- Parameter looping applies the same raw cone map at each independent loop coordinate. -/
theorem map_apply (n : ℕ) (s : unitInterval)
    (x : (parameterLooping
      (mappingCone (comparison Y))).space n) :
    Path.toContinuousMap ((map g).map n x) s =
      (coneMap g).map n (Path.toContinuousMap x s) := rfl

end Quillen.PerfectComplexes.GlobalRawBass
