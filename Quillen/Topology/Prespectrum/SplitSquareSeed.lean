/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.SplitSquareSourceNull
public import Quillen.Topology.Prespectrum.RelativeHomotopyConjugation
public import Quillen.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# Forward seeds for split-square inputs

A specified self-track of the common map gives a forward seed by conjugating with the positive
split source-null. A proved intertwining comparison along an input's common outer square,
together with the derived whole source-null comparison, gives an actual homotopy between the
two seed composites. Comparison, output-loop and structure coordinates remain independent.

The unit intertwining is an explicit hypothesis. No application-specific unit comparison,
localization nullhomotopy, strict functoriality or higher tower is asserted.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.SplitSquare

/-- The specified self-track is conjugated by the positive split source-null. -/
def transition (S : SplitSquare.{u}) (U : Homotopy S.l S.l) : S.A ⟶ S.step :=
  (U.postcomp (mappingConeInclusion S.comparison)).nullLoopMap S.sourceNull

/-- Every output-loop time retains the self-track and both source-null legs. -/
theorem transition_apply (S : SplitSquare.{u}) (U : Homotopy S.l S.l) (n : ℕ)
    (x : S.A.space n) (s : unitInterval) :
    Path.toContinuousMap ((S.transition U).map n x) s =
      ((U.postcomp (mappingConeInclusion S.comparison)).conjugateToZero
        S.sourceNull).level n (s, x) := rfl

namespace Input
variable {S S' : SplitSquare.{u}} (i : Input S S')
  (U : Homotopy S.l S.l) (U' : Homotopy S'.l S'.l)
  (JU : ((U.postcomp i.c).trans i.T).RelHomotopy
    (i.T.trans (Homotopy.precomp i.a U')))

namespace InputSeed

/-- The source self-track after target change and cone inclusion. -/
def oldUnit := (U.postcomp i.c).postcomp (mappingConeInclusion S'.comparison)

/-- The target self-track after source change and cone inclusion. -/
def newUnit := (Homotopy.precomp i.a U').postcomp (mappingConeInclusion S'.comparison)

/-- The supplied intertwining retains every coordinate after target cone inclusion. -/
def unitPasting :
    ((oldUnit i U).trans (InputNull.outerMovement i)).RelHomotopy
      ((InputNull.outerMovement i).trans (newUnit i U')) := by
  simpa only [Homotopy.postcomp_trans, oldUnit, newUnit, InputNull.outerMovement] using
    JU.postcomp (mappingConeInclusion S'.comparison)

/-- The proved unit and source-null pastings compare the two complete null-loop conjugates. -/
def conjugateComparison :=
  Homotopy.RelHomotopy.conjugateNaturality (InputNull.outerMovement i)
    (oldUnit i U) (newUnit i U') (InputNull.originalOldNull i)
    (InputNull.originalNewNull i)
    (unitPasting i U U' JU) (InputNull.originalNullComparison i)

/-- The source loop map is the literal source transition followed by the input step map. -/
lemma source_eq :
    ((oldUnit i U).conjugateToZero (InputNull.originalOldNull i)).zeroLoopMap =
      S.transition U ≫ map i := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((oldUnit i U).conjugateToZero (InputNull.originalOldNull i)).level n (s, x) =
    (((U.postcomp (mappingConeInclusion S.comparison)).conjugateToZero
      S.sourceNull).postcomp (coneMap i)).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.postcomp_trans, Homotopy.postcomp_symm]
  rfl

/-- The target loop map is the literal source input map followed by the target transition. -/
lemma target_eq :
    ((newUnit i U').conjugateToZero (InputNull.originalNewNull i)).zeroLoopMap =
      i.a ≫ S'.transition U' := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((newUnit i U').conjugateToZero (InputNull.originalNewNull i)).level n (s, x) =
    (Homotopy.precomp i.a
      ((U'.postcomp (mappingConeInclusion S'.comparison)).conjugateToZero
        S'.sourceNull)).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.precomp_trans, Homotopy.precomp_symm]
  rfl

end InputSeed

/-- The proved unit intertwining gives a whole homotopy of the specified forward seeds. -/
def transitionInputHomotopy :
    Homotopy (S.transition U ≫ map i) (i.a ≫ S'.transition U') :=
  (InputSeed.conjugateComparison i U U' JU).zeroLoopMapHomotopy.cast
    (InputSeed.source_eq i U) (InputSeed.target_eq i U')

/-- Comparison time and output-loop time retain the complete relative conjugation track. -/
lemma transitionInputHomotopy_apply (n : ℕ) (r s : unitInterval) (x : S.A.space n) :
    Path.toContinuousMap ((transitionInputHomotopy i U U' JU).level n (r, x)) s =
      (InputSeed.conjugateComparison i U U' JU).level n (r, (s, x)) := rfl

end Input
end Quillen.LoopPrespectrum.SplitSquare
