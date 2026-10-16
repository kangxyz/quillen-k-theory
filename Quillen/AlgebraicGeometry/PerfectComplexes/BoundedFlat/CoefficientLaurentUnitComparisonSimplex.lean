/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.UnitTrackPostcompSimplex
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.UnitTrackPrecompSimplex

/-!
# The actual old and new Laurent unit comparisons on their six-reference families

Both native comparisons are the existing records. The old comparison retains its actual
coefficient-unit equality transport; the new comparison retains the original scheme-square
transport and its ofLevels wrapper. No native lift or coefficient compatibility is supplied.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientLaurentUnitComparisonSimplex

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

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The old original six references, with the forward Laurent unit on the source fiber. -/
def oldSimplex := UnitTrackPostcompSimplex.simplex
  (coefficientMap P ((laurentUnderFunctor R).map u)) (laurentProjection P a)
  (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
    (laurentGlobalUnit a.right))

/-- The new original six references, with the actual forward unit on the target fiber. -/
def newSimplex := UnitTrackPrecompSimplex.simplex
  (laurentProjection P b) (coefficientMap P u)
  (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
    (laurentGlobalUnit b.right))

private theorem old_target_eq :
    ((boundedFlatPerfectUnitHomotopy
      (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)
      (Units.map (coefficientMap P ((laurentUnderFunctor R).map u)).appTop.hom.toMonoidHom
        (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
          (laurentGlobalUnit a.right)))).trans
      (CoefficientLaurentUnitTrack.oldComposition P u)) =
    ((CoefficientLaurentUnitTrack.commonUnit P u).trans
      (CoefficientLaurentUnitTrack.oldComposition P u)) := by
  unfold CoefficientLaurentUnitTrack.commonUnit
  rw [boundedFlatCoefficientLaurentUnit_coefficient]

private theorem old_comparison_heq :
    HEq (CoefficientLaurentUnitTrack.oldComparison P u)
      (boundedFlatPerfectUnitTrackPostcomp
        (coefficientMap P ((laurentUnderFunctor R).map u)) (laurentProjection P a)
        (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
          (laurentGlobalUnit a.right))) := by
  unfold CoefficientLaurentUnitTrack.oldComparison
  exact id_mp_heq _ _

/-- Every point of the existing old comparison has its whole six-reference lift.
The coefficient-unit equality only transports the original target track. -/
theorem old_comparison_lift :
    HomotopyLift (oldSimplex P u) UnitPrismParameters.parameter
      (CoefficientLaurentUnitTrack.oldComparison P u) :=
  target_transport_lift (oldSimplex P u) UnitPrismParameters.parameter
    (old_target_eq P u) _ _ (old_comparison_heq P u)
    (UnitTrackPostcompSimplex.native_lift
      (coefficientMap P ((laurentUnderFunctor R).map u)) (laurentProjection P a)
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
        (laurentGlobalUnit a.right)))

/-- Every point of the existing new comparison retains its original ofLevels transport.
The actual scheme-square equality and its original unit-track congrArg remain in that record. -/
theorem new_comparison_lift :
    HomotopyLift (newSimplex P u) UnitPrismParameters.parameter
      (CoefficientLaurentUnitTrack.newComparison P u) := by
  unfold CoefficientLaurentUnitTrack.newComparison
  exact HomotopyLift.ofLevels (newSimplex P u)
    (UnitTrackPrecompSimplex.native_lift (laurentProjection P b) (coefficientMap P u)
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
        (laurentGlobalUnit b.right))) _ _ _ _

end Quillen.PerfectComplexes.CoefficientLaurentUnitComparisonSimplex
