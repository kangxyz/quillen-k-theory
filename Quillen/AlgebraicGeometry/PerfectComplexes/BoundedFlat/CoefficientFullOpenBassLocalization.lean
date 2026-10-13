/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassTelescope

/-!
# Constructed global native full-open section-completion localization

The original supported telescope cone compares to the actual fine full-open section
telescope by composing its constructed coarse comparison with the unchanged stable
restriction. The same postcomposed whole null supplies the original fiber lift and signed
boundary. This is localization for these constructed section-completion objects; classical
nonconnective K-theory identification and completed geometric evaluation remain separate.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange Quillen.KTheory.Bass Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The original ambient-to-open map followed by the same full-open telescope restriction. -/
def boundedFlatCoefficientAmbientBassTelescopeFullOpen :
    boundedFlatCoefficientAmbientBassTelescopeFunctor Q ⟶
      boundedFlatCoefficientFullOpenBassTelescopeFunctor f :=
  boundedFlatCoefficientAmbientBassTelescopeOpen f ≫
    boundedFlatCoefficientOpenBassTelescopeRestriction f

/-- The finite composite is exactly the iterate of original native section restriction. -/
theorem boundedFlatCoefficientAmbientBassFullOpen_eq_original (i : ℕ) :
    boundedFlatCoefficientAmbientBassOpen f i ≫ boundedFlatCoefficientOpenBassRestriction f i =
      (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (Functor.whiskerRight (boundedFlatCoefficientSectionModelRestriction f)
          prespectrumFunctor) := by
  have hM : boundedFlatCoefficientOpenChangeWeakModelTransformation f ≫
      boundedFlatCoefficientOpenRestrictionModelTransformation f =
    boundedFlatCoefficientSectionModelRestriction f := by
    apply NatTrans.ext
    funext a
    apply Model.Hom.ext
    change 𝟭 _ ⋙ boundedFlatCoefficientOpenRestriction f a =
      boundedFlatCoefficientSectionsMap (i := (Opposite.op Q, a)) (k := (Opposite.op P, a))
        (f.op, 𝟙 a)
    exact Functor.id_comp _
  have h : boundedFlatCoefficientAmbientOpenPrespectrumTransformation f ≫
      boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f =
    Functor.whiskerRight (boundedFlatCoefficientSectionModelRestriction f) prespectrumFunctor := by
    apply NatTrans.ext
    funext a
    exact (prespectrumFunctor.map_comp _ _).symm.trans
      (congrArg prespectrumFunctor.map (NatTrans.congr_app hM a))
  exact ((strictDiagramIterate (laurentUnderSquareFunctor R) i).map_comp _ _).symm.trans
    (congrArg ((strictDiagramIterate (laurentUnderSquareFunctor R) i).map) h)

/-- Every actual ambient finite inclusion retains the original native restriction component. -/
theorem boundedFlatCoefficientAmbientBassTelescopeInclusion_fullOpen (i : ℕ) :
    boundedFlatCoefficientAmbientBassTelescopeInclusion Q i ≫
        boundedFlatCoefficientAmbientBassTelescopeFullOpen f =
      (boundedFlatCoefficientAmbientBassOpen f i ≫ boundedFlatCoefficientOpenBassRestriction f i) ≫
        boundedFlatCoefficientFullOpenBassTelescopeInclusion f i := by
  dsimp only [boundedFlatCoefficientAmbientBassTelescopeFullOpen]
  rw [← Category.assoc, boundedFlatCoefficientAmbientBassTelescopeInclusion_open,
    Category.assoc, boundedFlatCoefficientOpenBassTelescopeInclusion_restriction, ← Category.assoc]

/-- Postcompose the same supported localization null with the original fine restriction. -/
def boundedFlatCoefficientSupportedBassTelescopeFullOpenNull :
    DiagramNullHomotopy (boundedFlatCoefficientSupportedBassTelescopeForget f)
      (boundedFlatCoefficientAmbientBassTelescopeFullOpen f) where
  homotopy a :=
    (((boundedFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a).postcomp
      ((boundedFlatCoefficientOpenBassTelescopeRestriction f).app a)).cast
        (Category.assoc _ _ _)
        (by
          apply Hom.ext
          funext m
          ext x
          exact ((boundedFlatCoefficientOpenBassTelescopeRestriction f).app a).map_point m)
  naturality {a b} g m s x := by
    change ((boundedFlatCoefficientFullOpenBassTelescopeFunctor f).map g).map m
        (((boundedFlatCoefficientOpenBassTelescopeRestriction f).app a).map m
          (((boundedFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a).level m
            (s, x))) =
      ((boundedFlatCoefficientOpenBassTelescopeRestriction f).app b).map m
        (((boundedFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy b).level m
          (s, ((boundedFlatCoefficientSupportedBassTelescopeFunctor f).map g).map m x))
    exact (congrArg (fun g ↦ g.map m
      (((boundedFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a).level m (s, x)))
      ((boundedFlatCoefficientOpenBassTelescopeRestriction f).naturality g)).symm.trans
        (congrArg (fun y ↦
          ((boundedFlatCoefficientOpenBassTelescopeRestriction f).app b).map m y)
          ((boundedFlatCoefficientSupportedBassTelescopeOpenNull f).naturality g m s x))

/-- Every postcomposed null value retains its original time and the same restriction map. -/
theorem boundedFlatCoefficientSupportedBassTelescopeFullOpenNull_level
    (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientSupportedBassTelescopeFunctor f).obj a).space m) :
    ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a).level m (s, x) =
      ((boundedFlatCoefficientOpenBassTelescopeRestriction f).app a).map m
        (((boundedFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a).level m (s, x)) :=
  rfl

/-- The actual supported cone comparison lands in the constructed fine full-open telescope. -/
def boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap :
    mappingConeDiagram (boundedFlatCoefficientSupportedBassTelescopeForget f) ⟶
      boundedFlatCoefficientFullOpenBassTelescopeFunctor f :=
  boundedFlatCoefficientSupportedBassTelescopeOpenConeMap f ≫
    boundedFlatCoefficientOpenBassTelescopeRestriction f

/-- The composite is exactly the original cone descent for the same postcomposed whole null. -/
theorem boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_eq_desc (a : Under R) :
    (boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a =
      mappingConeDesc ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
        ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
        ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a) := by
  apply mappingCone_hom_ext
  · apply Hom.ext
    funext m
    ext x
    rfl
  · intro m s x
    rfl

/-- The original ambient inclusion face is the actual fine full-open restriction. -/
theorem boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_inclusion (a : Under R) :
    mappingConeInclusion ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a) ≫
        (boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a =
      (boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a := by
  rw [boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_eq_desc]
  exact mappingConeInclusion_desc _ _ _

/-- Cone time and original supported telescope height retain the same finite native restriction. -/
theorem boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedBassDiagram f i).obj a).space m) :
    ((boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a).map m
      (Quillen.ReducedMappingCone.cylinder
        (((boundedFlatCoefficientSupportedBassTelescopeFunctor f).obj a).point m)
        (((boundedFlatCoefficientAmbientBassTelescopeFunctor Q).obj a).point m)
        (((boundedFlatCoefficientSupportedBassTelescopeForget f).app a).map m)
        (s, Telescope.cylinder
          (fun n ↦ (boundedFlatCoefficientSupportedBassDiagram f n).obj a)
          (fun n ↦ (boundedFlatCoefficientSupportedBassTransition f n).app a) m i (t, x))) =
      Telescope.cylinder (fun n ↦ (boundedFlatCoefficientFullOpenBassDiagram f n).obj a)
        (fun n ↦ (boundedFlatCoefficientFullOpenBassTransition f n).app a) m i
          (t, ((boundedFlatCoefficientOpenBassRestriction f i).app a).map m
            (((boundedFlatCoefficientSupportedBassOpenNull f i).homotopy a).level m (s, x))) := rfl

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The supported telescope cone and fine full-open completion agree in every signed degree. -/
theorem boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a) :=
  (boundedFlatCoefficientSupportedBassTelescopeOpenConeMap_isStableEquivalence f a).comp
    (boundedFlatCoefficientOpenBassTelescopeRestriction_isStableEquivalence f a)

/-- The original supported class maps to the fiber by the same constructed whole null. -/
def boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap (a : Under R) :
    (boundedFlatCoefficientSupportedBassTelescopeFunctor f).obj a ⟶
      homotopyFiber ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a) :=
  homotopyFiberLift ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
    ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
    ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a)

omit [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] in
/-- Projection from the same whole-null fiber lift is precisely original support forgetting. -/
theorem boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_projection (a : Under R) :
    boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap f a ≫
        homotopyFiberProjection ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a) =
      (boundedFlatCoefficientSupportedBassTelescopeForget f).app a :=
  homotopyFiberLift_projection _ _ _

/-- This actual supported fiber comparison is stable in every original integer degree. -/
theorem boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence (boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap f a) :=
  homotopyFiberLift_isStableEquivalence_of_coneDesc _ _ _
    (boundedFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a)
    ((boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_eq_desc f a) ▸
      boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence f a)

omit [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] in
/-- The original signed connecting map agrees through this same whole-null fiber comparison. -/
theorem boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_connecting
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a) ≫
      stableFiberConnecting ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a) d =
    stableMappingConeConnecting ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
      (boundedFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d ≫
        (stableHomotopyFunctor d).map
          (boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap f a) := by
  rw [boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_eq_desc]
  exact mappingConeDesc_connecting _ _ _
    (boundedFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d

end Quillen.PerfectComplexes
