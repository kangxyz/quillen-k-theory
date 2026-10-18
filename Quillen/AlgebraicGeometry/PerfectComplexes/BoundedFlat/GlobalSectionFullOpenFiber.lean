/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionFullOpenNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalLocalizationTelescopeSquares
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalLocalizationTelescopeStable
public import Quillen.Topology.Prespectrum.ConeDescStableEquivalence

/-! # The actual global full-open localization fiber comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex.FullOpenTelescope
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The actual strict ambient/full-open comparison square. -/
def fiberSquare (a : Under R) : Arrow.mk ((openMap f).app a) ⟶
    Arrow.mk ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a) :=
  Arrow.homMk ((telescopeRestriction Q).app a) ((telescopeRestriction P).app a)
    (congrArg (fun η => η.app a) (openMap_square f)).symm

/-- The original global support inclusion lifts by its constructed complete null. -/
def fiberMap (a : Under R) : (SupportedTelescope.globalTelescope f).obj a ⟶
    homotopyFiber ((openMap f).app a) :=
  homotopyFiberLift ((openMap f).app a) ((LocalizationTelescope.forget f).app a)
    ((null f).homotopy a)

/-- The actual comparison retains both the source coordinate and the complete null path. -/
theorem fiberMap_restriction (a : Under R) :
    fiberMap f a ≫ homotopyFiberMap (fiberSquare f a) =
      (SupportedTelescope.telescopeRestriction f).app a ≫
        homotopyFiberLift ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
          ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
          ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun η => (η.app a).map n x) (LocalizationTelescope.forget_square f).symm
  · apply ContinuousMap.ext
    intro s
    exact null_restriction f a n s x

/-- The specified global full-open fiber lift is stable under the original geometric hypotheses. -/
theorem fiberMap_isStableEquivalence [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (a : Under R) : IsStableEquivalence (fiberMap f a) := by
  have hf := boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence f a
  have hb := homotopyFiberMap_isStableEquivalence (fiberSquare f a)
    (telescopeRestriction_isStableEquivalence Q a)
    (telescopeRestriction_isStableEquivalence P a)
  have hc := (SupportedTelescope.telescopeRestriction_isStableEquivalence f a).comp hf
  intro d
  let := hb d
  apply (isIso_comp_right_iff ((stableHomotopyFunctor d).map (fiberMap f a))
    ((stableHomotopyFunctor d).map (homotopyFiberMap (fiberSquare f a)))).mp
  rw [← Functor.map_comp, fiberMap_restriction]
  exact hc d

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.FullOpenTelescope
