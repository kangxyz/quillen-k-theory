/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.PushoutConeFamilyRecovery
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeCubeConsumers

/-!
# Original coefficient-composition cells under parameterized double descent

The actual chosen M composition supplies a one-parameter consumer of the pushout/cone
family interface. Its full Laurent, two polynomial, and overlap cells descend back to
the same original cone homotopy, including every prescribed parameter face. Independent
parameter looping recovers the original Bass-step composition with its fixed clock.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWhole

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The four complete native cell families of the already chosen original M composition. -/
def compositionCells : PushoutConeFamily unitInterval
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientBassSquareComparison P a)
    (mappingCone (boundedFlatCoefficientBassSquareComparison P c)) :=
  PushoutConeFamily.ofHomotopy (coneComposition P u v)

/-- Both quotients recover the entire chosen native composition, at every level and time. -/
theorem compositionCells_desc (n : ℕ) (r : unitInterval)
    (x : (mappingCone (boundedFlatCoefficientBassSquareComparison P a)).space n) :
    (compositionCells P u v).desc n (r, x) = (coneComposition P u v).level n (r, x) :=
  PushoutConeFamily.ofHomotopy_desc (coneComposition P u v) n r x

/-- Every whole parameter restriction preserves the original fixed composition filler. -/
theorem compositionCells_desc_restrict {T : Type*} [TopologicalSpace T]
    [LocallyCompactSpace T] (q : C(T, unitInterval)) (n : ℕ) (t : T)
    (x : (mappingCone (boundedFlatCoefficientBassSquareComparison P a)).space n) :
    ((compositionCells P u v).restrict q).desc n (t, x) =
      (coneComposition P u v).level n (q t, x) :=
  ((compositionCells P u v).desc_restrict q n t x).trans
    (compositionCells_desc P u v n (q t) x)

/-- The initial face is the original direct coefficient map, not a replacement up to homotopy. -/
theorem compositionCells_desc_zero (n : ℕ)
    (x : (mappingCone (boundedFlatCoefficientBassSquareComparison P a)).space n) :
    (compositionCells P u v).desc n (0, x) =
      (boundedFlatCoefficientBassConeMap P (u ≫ v)).map n x :=
  (compositionCells_desc P u v n 0 x).trans ((coneComposition P u v).at_zero n x)

/-- The terminal face retains the original composite of the two coefficient cone maps. -/
theorem compositionCells_desc_one (n : ℕ)
    (x : (mappingCone (boundedFlatCoefficientBassSquareComparison P a)).space n) :
    (compositionCells P u v).desc n (1, x) =
      (boundedFlatCoefficientBassConeMap P u ≫ boundedFlatCoefficientBassConeMap P v).map n x :=
  (compositionCells_desc P u v n 1 x).trans ((coneComposition P u v).at_one n x)

/-- After both descents the separate loop coordinate recovers the original step composition. -/
theorem compositionCells_looped (n : ℕ) (r s : unitInterval)
    (x : (parameterLooping
      (mappingCone (boundedFlatCoefficientBassSquareComparison P a))).space n) :
    Path.toContinuousMap ((compositionCells P u v).looped n (r, x)) s =
      Path.toContinuousMap ((stepComposition P u v).level n (r, x)) s :=
  compositionCells_desc P u v n r (Path.toContinuousMap x s)

end Quillen.PerfectComplexes.BassMWhole
