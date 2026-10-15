/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFiberBassTelescope

/-!
# Auxiliary-supported global native full-open section-completion localization

The original auxiliary fiber is supported on the complement of the union of
auxiliary open support and the actual open immersion range. Its constructed
native telescope cone compares to the fine full-open supported section telescope
through the same coarse comparison and the original stable restriction. The
same postcomposed whole null gives the actual fiber lift and the signed boundary.
This result concerns these section-completion objects; identification with
classical nonconnective K-theory remains separate.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original supported restriction with the actual fine source and target structures. -/
def boundedFlatCoefficientSupportedFineRestrictionModelMap (a : Under R) :
    boundedFlatCoefficientSupportedAmbientModel T a ⟶
      boundedFlatCoefficientSupportedFullOpenModel f T a where
  functor := boundedFlatCoefficientSupportedOpenRestriction f T a
  exact := boundedFlatCoefficientSupportedOpenRestriction_fine_exact f T a
  zero := (boundedFlatCoefficientSupportedOpenRestrictionModelMap f T a).zero

/-- Fine-supported native restriction is natural through the original coefficient squares. -/
def boundedFlatCoefficientSupportedFineRestrictionModelTransformation :
    boundedFlatCoefficientSupportedAmbientModelFunctor T ⟶
      boundedFlatCoefficientSupportedFullOpenModelFunctor f T where
  app := boundedFlatCoefficientSupportedFineRestrictionModelMap f T
  naturality a b g := by
    apply Model.Hom.ext
    exact boundedFlatCoefficientSupportedOpenRestriction_square f T g

/-- The original ambient-to-open map followed by the same full-open telescope restriction. -/
def boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen :
    boundedFlatCoefficientSupportedAmbientBassTelescopeFunctor T ⟶
      boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T :=
  boundedFlatCoefficientSupportedAmbientBassTelescopeOpen f T ≫
    boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T

omit [IsOpenImmersion f.left] in
/-- The finite composite is exactly the iterate of original native section restriction. -/
theorem boundedFlatCoefficientSupportedAmbientBassFullOpen_eq_original (i : ℕ) :
    boundedFlatCoefficientSupportedAmbientBassOpen f T i ≫
      boundedFlatCoefficientSupportedOpenBassRestriction f T i =
      (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (Functor.whiskerRight
          (boundedFlatCoefficientSupportedFineRestrictionModelTransformation f T)
          prespectrumFunctor) := by
  have hM : boundedFlatCoefficientSupportedOpenChangeWeakModelTransformation f T ≫
      boundedFlatCoefficientSupportedOpenRestrictionModelTransformation f T =
    boundedFlatCoefficientSupportedFineRestrictionModelTransformation f T := by
    apply NatTrans.ext
    funext a
    apply Model.Hom.ext
    change 𝟭 _ ⋙ boundedFlatCoefficientSupportedOpenRestriction f T a =
      boundedFlatCoefficientSupportedOpenRestriction f T a
    exact Functor.id_comp _
  have h : boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T ≫
      boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T =
    Functor.whiskerRight (boundedFlatCoefficientSupportedFineRestrictionModelTransformation f T)
      prespectrumFunctor := by
    apply NatTrans.ext
    funext a
    exact (prespectrumFunctor.map_comp _ _).symm.trans
      (congrArg prespectrumFunctor.map (NatTrans.congr_app hM a))
  exact ((strictDiagramIterate (laurentUnderSquareFunctor R) i).map_comp _ _).symm.trans
    (congrArg ((strictDiagramIterate (laurentUnderSquareFunctor R) i).map) h)

omit [IsOpenImmersion f.left] in
/-- Every actual ambient finite inclusion retains the original native restriction component. -/
theorem boundedFlatCoefficientSupportedAmbientBassTelescopeInclusion_fullOpen (i : ℕ) :
    boundedFlatCoefficientSupportedAmbientBassTelescopeInclusion T i ≫
        boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T =
      (boundedFlatCoefficientSupportedAmbientBassOpen f T i ≫
        boundedFlatCoefficientSupportedOpenBassRestriction f T i) ≫
        boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T i := by
  dsimp only [boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen]
  rw [← Category.assoc, boundedFlatCoefficientSupportedAmbientBassTelescopeInclusion_open,
    Category.assoc, boundedFlatCoefficientSupportedOpenBassTelescopeInclusion_restriction,
    ← Category.assoc]

/-- Postcompose the same supported localization null with the original fine restriction. -/
def boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull :
    DiagramNullHomotopy (boundedFlatCoefficientSupportedFiberBassTelescopeForget f T)
      (boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T) where
  homotopy a :=
    (((boundedFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a).postcomp
      ((boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a)).cast
        (Category.assoc _ _ _)
        (by
          apply Hom.ext
          funext m
          ext x
          exact ((boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a).map_point
            m)
  naturality {a b} g m s x := by
    change ((boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).map g).map m
        (((boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a).map m
          (((boundedFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a).level m
            (s, x))) =
      ((boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app b).map m
        (((boundedFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy b).level m
          (s, ((boundedFlatCoefficientSupportedFiberBassTelescopeFunctor f T).map g).map m x))
    exact (congrArg (fun g ↦ g.map m
      (((boundedFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a).level m (s, x)))
      ((boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).naturality g)).symm.trans
        (congrArg (fun y ↦
          ((boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app b).map m y)
          ((boundedFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).naturality g m s x))

/-- Every postcomposed null value retains its original time and the same restriction map. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull_level
    (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientSupportedFiberBassTelescopeFunctor f T).obj a).space m) :
    ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a).level m
        (s, x) =
      ((boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a).map m
        (((boundedFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a).level m
          (s, x)) :=
  rfl

/-- The actual supported cone comparison lands in the constructed fine full-open telescope. -/
def boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap :
    mappingConeDiagram (boundedFlatCoefficientSupportedFiberBassTelescopeForget f T) ⟶
      boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T :=
  boundedFlatCoefficientSupportedFiberBassTelescopeOpenConeMap f T ≫
    boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T

/-- The composite is exactly the original cone descent for the same postcomposed whole null. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_eq_desc (a : Under R) :
    (boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a =
      mappingConeDesc ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        ((boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
        ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a) := by
  apply mappingCone_hom_ext
  · apply Hom.ext
    funext m
    ext x
    rfl
  · intro m s x
    rfl

/-- The original ambient inclusion face is the actual fine full-open restriction. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_inclusion (a : Under R) :
    mappingConeInclusion ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a) ≫
        (boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a =
      (boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a := by
  rw [boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_eq_desc]
  exact mappingConeInclusion_desc _ _ _

/-- Cone time and original supported telescope height retain the same finite native restriction. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedFiberBassDiagram f T i).obj a).space m) :
    ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a).map m
      (Quillen.ReducedMappingCone.cylinder
        (((boundedFlatCoefficientSupportedFiberBassTelescopeFunctor f T).obj a).point m)
        (((boundedFlatCoefficientSupportedAmbientBassTelescopeFunctor T).obj a).point m)
        (((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a).map m)
        (s, Telescope.cylinder
          (fun n ↦ (boundedFlatCoefficientSupportedFiberBassDiagram f T n).obj a)
          (fun n ↦ (boundedFlatCoefficientSupportedFiberBassTransition f T n).app a) m i (t, x))) =
      Telescope.cylinder (fun n ↦ (boundedFlatCoefficientSupportedFullOpenBassDiagram f T n).obj a)
        (fun n ↦ (boundedFlatCoefficientSupportedFullOpenBassTransition f T n).app a) m i
          (t, ((boundedFlatCoefficientSupportedOpenBassRestriction f T i).app a).map m
            (((boundedFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a).level m
              (s, x))) := rfl

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
  [CompactSpace T]

/-- The supported telescope cone and fine full-open completion agree in every signed degree. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence
      ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a) :=
  (boundedFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_isStableEquivalence f T a).comp
    (boundedFlatCoefficientSupportedOpenBassTelescopeRestriction_isStableEquivalence f T a)

/-- The original supported class maps to the fiber by the same constructed whole null. -/
def boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap (a : Under R) :
    (boundedFlatCoefficientSupportedFiberBassTelescopeFunctor f T).obj a ⟶
      homotopyFiber ((boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a) :=
  homotopyFiberLift ((boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
    ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
    ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a)

omit [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
  [CompactSpace T] in
/-- Projection from the same whole-null fiber lift is precisely original support forgetting. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_projection (a : Under R) :
    boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f T a ≫
        homotopyFiberProjection
          ((boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a) =
      (boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a :=
  homotopyFiberLift_projection _ _ _

/-- This actual supported fiber comparison is stable in every original integer degree. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence (boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f T a) :=
  homotopyFiberLift_isStableEquivalence_of_coneDesc _ _ _
    (boundedFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence f T a)
    ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_eq_desc f T a) ▸
      boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_isStableEquivalence f T a)

omit [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
  [CompactSpace T] in
/-- The original signed connecting map agrees through this same whole-null fiber comparison. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_connecting
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a) ≫
      stableFiberConnecting
          ((boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a) d =
    stableMappingConeConnecting
      ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
      (boundedFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence f T a)
        d ≫
        (stableHomotopyFunctor d).map
          (boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f T a) := by
  rw [boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_eq_desc]
  exact mappingConeDesc_connecting _ _ _
    (boundedFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence f T a) d

end Quillen.PerfectComplexes
