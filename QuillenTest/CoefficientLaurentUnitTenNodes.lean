/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitTenNodes

/-! Whole native Laurent comparisons, full reference joins and complete six-node faces,
including separate lower/shifted routes and independent loop/structure coordinates. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open Quillen.PerfectComplexes Quillen.PerfectComplexes.CoefficientLaurentUnitTenNodes
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.CoefficientLaurentUnitTenNodes
/-- The literal old degree-zero claim, universally quantified over all three independent times
and the entire input loop. The complete simplex, scalar homotopy and native record remain inputs. -/
def ZeroCoordinates {V W : Model.{u}} {k : ℕ} (S : ModelSimplex V W k)
    {a b : StdSimplex ℝ (Fin (k + 1))} {p q : Path a b} (J : p.Homotopy q)
    {f g : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g}
    (M : H.RelHomotopy K) : Prop :=
  ∀ (r s q : unitInterval) (x : Path (stagePoint 0 V) (stagePoint 0 V)),
    (show Path (stagePoint 0 W) (stagePoint 0 W) from M.level 0 (r, (s, x))) q =
      stageSimplexBarycentric S 0 (J (r, s), x q)

/-- The literal all-level basepoint claim. The simplex and scalar homotopy are retained as
parameters even though this particular equality only projects the native relative homotopy. -/
def PointCoordinates {V W : Model.{u}} {k : ℕ} (_S : ModelSimplex V W k)
    {a b : StdSimplex ℝ (Fin (k + 1))} {p q : Path a b} (_J : p.Homotopy q)
    {f g : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g}
    (M : H.RelHomotopy K) : Prop :=
  ∀ (n : ℕ) (r s : unitInterval),
    M.level n (r, (s, (prespectrum V).point n)) = (prespectrum W).point n

/-- The literal structure claim, universally quantified over every level, all three independent
times and the original input. No comparison or compatibility is supplied as a premise. -/
def StructureCoordinates {V W : Model.{u}} {k : ℕ} (S : ModelSimplex V W k)
    {a b : StdSimplex ℝ (Fin (k + 1))} {p q : Path a b} (J : p.Homotopy q)
    {f g : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g}
    (M : H.RelHomotopy K) : Prop :=
  ∀ (n : ℕ) (r s q : unitInterval) (x : (prespectrum V).space n),
    prespectrumSimplexFamily S (n + 1) (J (r, s), (prespectrum V).structureMap n x q) =
      (prespectrum W).structureMap n (M.level n (r, (s, x))) q

section LiftCoordinates
variable {V W : Model.{u}} {k : ℕ} (S : ModelSimplex V W k)
  {a b : StdSimplex ℝ (Fin (k + 1))} {p q : Path a b} (J : p.Homotopy q)
  {f g : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g}
  (M : H.RelHomotopy K) (hJ : HomotopyLift S J M)
include hJ

private theorem lift_zero (r s q : unitInterval)
    (x : Path (stagePoint 0 V) (stagePoint 0 V)) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from M.level 0 (r, (s, x))) q =
      stageSimplexBarycentric S 0 (J (r, s), x q) :=
  (congrArg (fun y : (prespectrum W).space 0 ↦
    (show Path (stagePoint 0 W) (stagePoint 0 W) from y) q)
      (hJ 0 r s x)).symm.trans (prespectrumSimplexFamily_zero_apply S _ _ _)

private theorem lift_point (n : ℕ) (r s : unitInterval) :
    M.level n (r, (s, (prespectrum V).point n)) = (prespectrum W).point n :=
  (hJ n r s _).symm.trans (prespectrumSimplexFamily_point S n _)

private theorem lift_structure (n : ℕ) (r s q : unitInterval)
    (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S (n + 1) (J (r, s), (prespectrum V).structureMap n x q) =
      (prespectrum W).structureMap n (M.level n (r, (s, x))) q :=
  (hJ (n + 1) r s _).trans (M.comm n r s x q)

end LiftCoordinates

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The old whole comparison is the existing transported native record. -/
theorem whole_old : HomotopyLift (simplex P u) oldParameter
    (CoefficientLaurentUnitTrack.oldComparison P u) := old_comparison_lift P u

/-- The new whole comparison retains its original scheme-square and ofLevels transports. -/
theorem whole_new (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u) n (newParameter (r, s), x) =
      (CoefficientLaurentUnitTrack.newComparison P u).level n (r, (s, x)) :=
  new_comparison_lift P u n r s x

/-- The old six-node diagram is preserved as a whole ordered face. -/
theorem old_whole_face : (simplex P u).face oldFace =
    CoefficientLaurentUnitComparisonSimplex.oldSimplex P u := old_face P u

/-- The new whole face contains every reanchored original reference. -/
theorem new_whole_face : (simplex P u).face newFace =
    CoefficientLaurentUnitComparisonSimplex.newSimplex P u := new_face P u

/-- The actual source functor and its reference join together. -/
theorem full_source_join : oldNodes P u 0 = newNodes P u 0 := source_node_join P u

/-- The actual unit-shifted source joins with its complete reference isomorphism. -/
theorem full_unit_source_join : oldNodes P u 3 = newNodes P u 3 := source_unit_node_join P u

/-- Every old full dependent node survives its face embedding. -/
theorem full_old_nodes (i : Fin 6) :
    nodes P u (oldFace.toOrderHom i) = oldNodes P u i := old_nodes P u i

/-- Every new full dependent node survives the proved two-node joining. -/
theorem full_new_nodes (i : Fin 6) :
    nodes P u (newFace.toOrderHom i) = newNodes P u i := new_nodes P u i

/-- The lower old route is lifted separately. -/
theorem lower_old (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u) n (C0 t, x) =
      (CoefficientLaurentUnitTrack.oldComposition P u).level n (t, x) := C0_native P u n t x

/-- The shifted old route keeps its distinct scalar path. -/
theorem shifted_old (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u) n (C1 t, x) =
      (CoefficientLaurentUnitTrack.oldComposition P u).level n (t, x) := C1_native P u n t x

/-- The lower new route keeps the actual endpoint cast. -/
theorem lower_new (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u) n (D0 t, x) =
      (CoefficientLaurentUnitTrack.newComposition P u).level n (t, x) := D0_native P u n t x

/-- The shifted new route is also a full lift, without identifying it with the lower path. -/
theorem shifted_new (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u) n (D1 t, x) =
      (CoefficientLaurentUnitTrack.newComposition P u).level n (t, x) := D1_native P u n t x

/-- The old degree-zero input loop time remains independent of both comparison times. -/
theorem old_level_zero :
    ZeroCoordinates (simplex P u) oldParameter (CoefficientLaurentUnitTrack.oldComparison P u) :=
  lift_zero (simplex P u) oldParameter (CoefficientLaurentUnitTrack.oldComparison P u)
    (whole_old P u)

/-- The new degree-zero loop family retains its own original comparison and independent time. -/
theorem new_level_zero (r s q : unitInterval)
    (x : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))) :
    (show Path
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
          (space (op P, (laurentUnderFunctor R).obj b)))))
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
          (space (op P, (laurentUnderFunctor R).obj b))))) from
      (CoefficientLaurentUnitTrack.newComparison P u).level 0 (r, (s, x))) q =
    stageSimplexBarycentric (simplex P u) 0 (newParameter (r, s), x q) := by
  exact (congrArg (fun y : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj b)))).space 0 ↦
    (show Path
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj b)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj b))))) from y) q)
      (whole_new P u 0 r s x)).symm.trans (prespectrumSimplexFamily_zero_apply _ _ _ _)

/-- The old entire surface fixes the original basepoint. -/
theorem old_point :
    PointCoordinates (simplex P u) oldParameter (CoefficientLaurentUnitTrack.oldComparison P u) :=
  lift_point (simplex P u) oldParameter (CoefficientLaurentUnitTrack.oldComparison P u)
    (whole_old P u)

/-- The new entire surface fixes the original basepoint after its actual transports. -/
theorem new_point (n : ℕ) (r s : unitInterval) :
    (CoefficientLaurentUnitTrack.newComparison P u).level n
      (r, (s, (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n)) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj b)))).point n :=
  (whole_new P u n r s _).symm.trans (prespectrumSimplexFamily_point (simplex P u) n _)

/-- All old comparison, path and structure times stay independent. -/
theorem old_structure :
    StructureCoordinates (simplex P u) oldParameter
      (CoefficientLaurentUnitTrack.oldComparison P u) :=
  lift_structure (simplex P u) oldParameter (CoefficientLaurentUnitTrack.oldComparison P u)
    (whole_old P u)

/-- All new comparison, path and structure times stay independent. -/
theorem new_structure (n : ℕ) (r s q : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u) (n + 1)
      (newParameter (r, s),
        (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x q) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj b)))).structureMap n
      ((CoefficientLaurentUnitTrack.newComparison P u).level n (r, (s, x))) q :=
  (whole_new P u (n + 1) r s _).trans
    ((CoefficientLaurentUnitTrack.newComparison P u).comm n r s x q)

end QuillenTest.CoefficientLaurentUnitTenNodes
