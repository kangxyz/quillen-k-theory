/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.UnitTrackPostcompSimplex
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.UnitTrackPrecompSimplex

/-!
# The actual old and new Laurent unit comparisons on their six-reference families

Both native comparisons are the existing records. The old comparison retains its actual
Laurent-unit equality transport; the new comparison retains the original scheme-square
transport and its ofLevels wrapper. No native lift or extra compatibility is supplied.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputIdentitySeedUnitSimplex

private theorem id_mp_heq {A B : Sort u} (p : A = B) (x : A) :
    HEq (id (p.mp x)) x := by
  cases p
  rfl

private theorem target_transport_lift {V W : Model.{u}} (S : ModelSimplex V W 5)
    {a b : StdSimplex ℝ (Fin 6)} {p q : Path a b} (J : p.Homotopy q)
    {f g : prespectrum V ⟶ prespectrum W} {H K K' : Homotopy f g} (e : K = K')
    (M : H.RelHomotopy K) (M' : H.RelHomotopy K') (hM : HEq M' M)
    (h : HomotopyLift S J M) : HomotopyLift S J M' := by
  subst K'
  cases eq_of_heq hM
  exact h

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The old original six references, with the forward Laurent unit on the source fiber. -/
def oldSimplex := UnitTrackPostcompSimplex.simplex
  (laurent.map g) (laurentProjection.app Y)
  (GlobalSchemeLaurentTrack.laurentScalar (op Y))

/-- The new original six references, with the actual forward unit on the target fiber. -/
def newSimplex := UnitTrackPrecompSimplex.simplex
  (laurentProjection.app X) g
  (GlobalSchemeLaurentTrack.laurentScalar (op X))

private theorem old_target_eq :
    ((boundedFlatPerfectUnitHomotopy
      (laurent.map g ≫ laurentProjection.app Y)
      (Units.map (laurent.map g).appTop.hom.toMonoidHom
        (GlobalSchemeLaurentTrack.laurentScalar (op Y)))).trans
      (InputUnit.oldComposition g)) =
    ((InputUnit.commonUnit g).trans
      (InputUnit.oldComposition g)) := by
  unfold InputUnit.commonUnit
  rw [laurentUnit_map]

private theorem old_comparison_heq :
    HEq (InputUnit.oldComparison g)
      (boundedFlatPerfectUnitTrackPostcomp
        (laurent.map g) (laurentProjection.app Y)
        (GlobalSchemeLaurentTrack.laurentScalar (op Y))) := by
  unfold InputUnit.oldComparison
  exact id_mp_heq _ _

/-- Every point of the existing old comparison has its whole six-reference lift.
The actual Laurent-unit equality only transports the original target track. -/
theorem old_comparison_lift :
    HomotopyLift (oldSimplex g) UnitPrismParameters.parameter
      (InputUnit.oldComparison g) :=
  target_transport_lift (oldSimplex g) UnitPrismParameters.parameter
    (old_target_eq g) _ _ (old_comparison_heq g)
    (UnitTrackPostcompSimplex.native_lift
      (laurent.map g) (laurentProjection.app Y)
      (GlobalSchemeLaurentTrack.laurentScalar (op Y)))

/-- Every point of the existing new comparison retains its original ofLevels transport.
The actual scheme-square equality and its original unit-track congrArg remain in that record. -/
theorem new_comparison_lift :
    HomotopyLift (newSimplex g) UnitPrismParameters.parameter
      (InputUnit.newComparison g) := by
  unfold InputUnit.newComparison
  exact HomotopyLift.ofLevels (newSimplex g)
    (UnitTrackPrecompSimplex.native_lift (laurentProjection.app X) g
      (GlobalSchemeLaurentTrack.laurentScalar (op X))) _ _ _ _

end Quillen.PerfectComplexes.GlobalRawBass.InputIdentitySeedUnitSimplex
