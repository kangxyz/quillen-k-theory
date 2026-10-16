/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassSeed
public import Quillen.KTheory.Bass.StrictLaurentSeedStable

/-!
# Original supported and ambient section-seed stable factorizations

The actual supported and ambient Model actions supply their existing complete Laurent tracks.
Their original strict seeds factor through those tracks and their actual strict-square cone
inclusions. The original strict source null is retained; it is not identified with the separate
raw geometric source null. No boundary splitting or supported-cofiber comparison is asserted.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
attribute [local irreducible] boundedFlatCoefficientSupportedModelFunctor
  boundedFlatCoefficientSectionModelRow Quillen.Waldhausen.IteratedS.prespectrumFunctor
variable {R : CommRingCat.{u}}

section Supported
variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The original supported seed uses its actual supported Laurent action and cone inclusion. -/
theorem boundedFlatCoefficientSupportedBassSeed_stableHomotopy (a : Under R) (d : ℤ) :
    LaurentSeed.Track.SeedStableFactorization
      (F := boundedFlatCoefficientSupportedPrespectrumFunctor f)
      (boundedFlatCoefficientSupportedLaurentAction f).track
      (boundedFlatCoefficientSupportedBassSeed f) a d :=
  (boundedFlatCoefficientSupportedLaurentAction f).track.seed_hasStableFactorization a d

/-- The actual supported seed map itself retains the exact parameter-loop shift inverse. -/
theorem boundedFlatCoefficientSupportedBassSeed_stableHomotopy_eq (a : Under R) (d : ℤ) :
    LaurentSeed.Track.SeedStableFormula
      (F := boundedFlatCoefficientSupportedPrespectrumFunctor f)
      (boundedFlatCoefficientSupportedLaurentAction f).track
      (boundedFlatCoefficientSupportedBassSeed f) a d :=
  (boundedFlatCoefficientSupportedLaurentAction f).track.seed_hasStableFormula a d

end Supported

section Ambient
variable (Q : Over (Spec R))

/-- The unchanged ambient section seed factors through its original ambient Laurent action. -/
theorem boundedFlatCoefficientAmbientBassSeed_stableHomotopy (a : Under R) (d : ℤ) :
    LaurentSeed.Track.SeedStableFactorization
      (F := boundedFlatCoefficientAmbientPrespectrumFunctor Q)
      (boundedFlatCoefficientAmbientLaurentAction Q).track
      (boundedFlatCoefficientAmbientBassSeed Q) a d :=
  (boundedFlatCoefficientAmbientLaurentAction Q).track.seed_hasStableFactorization a d

/-- The actual ambient section seed map keeps the same exact inverse degree shift. -/
theorem boundedFlatCoefficientAmbientBassSeed_stableHomotopy_eq (a : Under R) (d : ℤ) :
    LaurentSeed.Track.SeedStableFormula
      (F := boundedFlatCoefficientAmbientPrespectrumFunctor Q)
      (boundedFlatCoefficientAmbientLaurentAction Q).track
      (boundedFlatCoefficientAmbientBassSeed Q) a d :=
  (boundedFlatCoefficientAmbientLaurentAction Q).track.seed_hasStableFormula a d

end Ambient
end Quillen.PerfectComplexes
