/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassRestrictionCofiber
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassTelescopeOpenCofiber

/-!
# Constructed affine full-open section-completion localization

The original supported telescope cone compares to the actual fine full-open section
telescope by composing its constructed coarse comparison with the unchanged stable
restriction. The same postcomposed whole null supplies the original fiber lift and signed
boundary. This is localization for these constructed section-completion objects; classical
nonconnective K-theory identification and completed geometric evaluation remain separate.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j]

/-- The original ambient-to-open map followed by the same full-open telescope restriction. -/
def boundedFlatAffineSectionBassTelescopeFullOpen :
    Under.forget R ⋙ boundedFlatAffineSectionBassTelescopeFunctor ⟶
      boundedFlatAffineFullOpenSectionBassTelescopeFunctor j :=
  boundedFlatAffineSectionBassTelescopeOpen j ≫
    boundedFlatAffineSectionFullOpenBassTelescopeRestriction j

/-- Postcompose the same supported localization null with the original fine restriction. -/
def boundedFlatAffineSupportedSectionBassTelescopeFullOpenNull :
    DiagramNullHomotopy (boundedFlatAffineSupportedSectionBassTelescopeForget j)
      (boundedFlatAffineSectionBassTelescopeFullOpen j) where
  homotopy a :=
    (((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a).postcomp
      ((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).app a)).cast
        (Category.assoc _ _ _)
        (by
          apply Hom.ext
          funext m
          ext x
          exact ((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).app a).map_point m)
  naturality {a b} f m s x := by
    change ((boundedFlatAffineFullOpenSectionBassTelescopeFunctor j).map f).map m
        (((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).app a).map m
          (((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a).level m
            (s, x))) =
      ((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).app b).map m
        (((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy b).level m
          (s, ((boundedFlatAffineSupportedSectionBassTelescopeFunctor j).map f).map m x))
    exact (congrArg (fun g ↦ g.map m
      (((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a).level m (s, x)))
      ((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).naturality f)).symm.trans
        (congrArg (fun y ↦
          ((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).app b).map m y)
          ((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).naturality f m s x))

/-- Every postcomposed null value retains its original time and the same restriction map. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeFullOpenNull_level
    (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassTelescopeFunctor j).obj a).space m) :
    ((boundedFlatAffineSupportedSectionBassTelescopeFullOpenNull j).homotopy a).level m (s, x) =
      ((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).app a).map m
        (((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a).level m (s, x)) :=
  rfl

/-- The actual supported cone comparison lands in the constructed fine full-open telescope. -/
def boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap :
    mappingConeDiagram (boundedFlatAffineSupportedSectionBassTelescopeForget j) ⟶
      boundedFlatAffineFullOpenSectionBassTelescopeFunctor j :=
  boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap j ≫
    boundedFlatAffineSectionFullOpenBassTelescopeRestriction j

/-- The composite is exactly the original cone descent for the same postcomposed whole null. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap_eq_desc (a : Under R) :
    (boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap j).app a =
      mappingConeDesc ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a)
        ((boundedFlatAffineSectionBassTelescopeFullOpen j).app a)
        ((boundedFlatAffineSupportedSectionBassTelescopeFullOpenNull j).homotopy a) := by
  apply mappingCone_hom_ext
  · apply Hom.ext
    funext m
    ext x
    rfl
  · intro m s x
    rfl

/-- The original ambient inclusion face is the actual fine full-open restriction. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap_inclusion (a : Under R) :
    mappingConeInclusion ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a) ≫
        (boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap j).app a =
      (boundedFlatAffineSectionBassTelescopeFullOpen j).app a := by
  rw [boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap_eq_desc]
  exact mappingConeInclusion_desc _ _ _

variable [CompactSpace U]

/-- The supported telescope cone and fine full-open completion agree in every signed degree. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap j).app a) :=
  (boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap_isStableEquivalence j a).comp
    (boundedFlatAffineSectionFullOpenBassTelescopeRestriction_isStableEquivalence j a)

/-- The original supported class maps to the fiber by the same constructed whole null. -/
def boundedFlatAffineSupportedSectionBassTelescopeFullOpenFiberMap (a : Under R) :
    (boundedFlatAffineSupportedSectionBassTelescopeFunctor j).obj a ⟶
      homotopyFiber ((boundedFlatAffineSectionBassTelescopeFullOpen j).app a) :=
  homotopyFiberLift ((boundedFlatAffineSectionBassTelescopeFullOpen j).app a)
    ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a)
    ((boundedFlatAffineSupportedSectionBassTelescopeFullOpenNull j).homotopy a)

/-- This actual supported fiber comparison is stable in every original integer degree. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeFullOpenFiberMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence (boundedFlatAffineSupportedSectionBassTelescopeFullOpenFiberMap j a) :=
  homotopyFiberLift_isStableEquivalence_of_coneDesc _ _ _
    (boundedFlatAffineSupportedSectionBassTelescopeForget_coneFiber_isStableEquivalence j a)
    ((boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap_eq_desc j a) ▸
      boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap_isStableEquivalence j a)

omit [CompactSpace U] in
/-- The original signed connecting map agrees through this same whole-null fiber comparison. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap_connecting
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap j).app a) ≫
      stableFiberConnecting ((boundedFlatAffineSectionBassTelescopeFullOpen j).app a) d =
    stableMappingConeConnecting ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a)
      (boundedFlatAffineSupportedSectionBassTelescopeForget_coneFiber_isStableEquivalence j a) d ≫
        (stableHomotopyFunctor d).map
          (boundedFlatAffineSupportedSectionBassTelescopeFullOpenFiberMap j a) := by
  rw [boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap_eq_desc]
  exact mappingConeDesc_connecting _ _ _
    (boundedFlatAffineSupportedSectionBassTelescopeForget_coneFiber_isStableEquivalence j a) d

end Quillen.PerfectComplexes
