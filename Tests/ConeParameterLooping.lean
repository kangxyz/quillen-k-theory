/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.ModelDiagramConeParameterLooping
public import Quillen.Waldhausen.SConstruction.Iterated.ConeParameterLooping

/-!
# Original loop-cofiber consumers

The tests retain the actual target inclusion, independent homotopy/loop/structure coordinates,
arbitrary signed stable degrees, and original finite-stage coefficient arrows. The actual Model
and finite-stage connectivity conditions are discharged by the imported original theorems.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open Quillen Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.Tests.ConeParameterLooping

/-- The complete original homotopy retains all three independent parameters. -/
theorem original_three_parameters {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f g) (n : ℕ) (s t r : unitInterval)
    (γ : Path (E.point n) (E.point n)) :
    Path.toContinuousMap (H.parameterLooping.level (n + 1)
      (s, (parameterLooping E).structureMap n γ t)) r =
      F.structureMap n (H.level n (s, γ r)) t :=
  H.comm n s (γ r) t

/-- The comparison is exactly the original inclusion on every target loop. -/
theorem original_target_loop {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (n : ℕ)
    (γ : Path (F.point n) (F.point n)) (t : unitInterval) :
    Path.toContinuousMap ((mappingConeParameterLoopingComparison f).map n
      ((mappingConeInclusion (parameterLoopingMap f)).map n γ)) t =
      (mappingConeInclusion f).map n (γ t) := rfl

/-- Unchanged coefficient arrows at every actual finite stage have signed loop-cofiber bijections.
-/
theorem original_finite_stage_coefficient_bijective {C : Type u} [Category.{v} C]
    (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ Model.{w}) (i : ℕ)
    {X Y : C} (a : X ⟶ Y) (d : ℤ) :
    Function.Bijective ((stableHomotopyFunctor d).map (mappingConeParameterLoopingComparison
      ((((KTheory.Bass.strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))).map a))) := by
  let := KTheory.Bass.modelDiagramIterate_mappingConeParameterLoopingComparison_isStableEquivalence
    Q i i F F X Y ((((KTheory.Bass.strictDiagramIterate Q i).obj
      (F ⋙ prespectrumFunctor))).map a) d
  exact ConcreteCategory.bijective_of_isIso _

/-- Signed boundary and signed loop shift are retained on every individual original class. -/
theorem original_signed_boundary {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hΩe : IsStableEquivalence (mappingConeFiberComparison (parameterLoopingMap f)))
    (d : ℤ) (x : stableHomotopyGroup (mappingCone (parameterLoopingMap f)) (d + 1)) :
    (parameterStableHomotopyIso (homotopyFiber (mappingConeInclusion f)) d).hom
      ((stableHomotopyFunctor d).map
        (homotopyFiberParameterLoopingIso (mappingConeInclusion f)).hom
        (stableFiberConnecting (parameterLoopingMap (mappingConeInclusion f)) d
          ((stableHomotopyFunctor (d + 1)).map (mappingConeParameterLoopingComparison f) x))) =
      (stableHomotopyFunctor (d + 1)).map (mappingConeFiberComparison f)
        ((parameterStableHomotopyIso E d).hom
          (stableMappingConeConnecting (parameterLoopingMap f) hΩe d x)) :=
  ConcreteCategory.congr_hom (mappingConeParameterLoopingComparison_connecting_shift f hΩe d) x

end Quillen.Tests.ConeParameterLooping
