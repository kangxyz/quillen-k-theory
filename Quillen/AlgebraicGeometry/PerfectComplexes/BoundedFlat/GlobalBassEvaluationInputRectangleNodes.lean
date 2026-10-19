/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputTriplePostNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.DoubleSquareMergedSimplex

/-!
# Full evaluated nodes of the original double-square rectangle

The actual 18-node raw rectangle is evaluated using the original total comparison. Its
first and last split triples retain their complete references, including both geometric
square equations. The three original postcomposed evaluation nodes are literal shared nodes.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputRectangleNodes
open GlobalSectionChangeIndex
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- The complete actual evaluated node, with the original total evaluation anchor. -/
def rawNode (i : Fin 18) : InputTripleNodes.Node c q p :=
  ⟨evaluationModel (op A) ≫ (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq i).1,
    evaluationComparisonIso (c ≫ q ≫ p) ≪≫ isoWhiskerLeft (evaluationModel (op A)).functor
      (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq i).2⟩

/-- The first complete triple keeps exactly its original evaluation anchor. -/
theorem first_nodes (i : Fin 8) :
    rawNode p q p' q' a b c hp hq (DoubleSquareMergedSimplex.firstFace.toOrderHom i) =
      InputTripleNodes.rawNode c q p i := by
  have e := (DoubleSquareMergedSimplex.first_nodes p q p' q' a b c hp hq i).trans
    (DoubleSquareCommonSimplex.first_nodes p q p' q' a b c hp hq i)
  unfold rawNode
  rw [e]
  rfl

/-- The actual two square equations transport the strict total reference. -/
def lastSourceIso : (InputTripleNodes.sourceMap c q p).functor ≅
    (InputTripleNodes.sourceMap q' p' a).functor :=
  eqToIso (congrArg (fun t : C' ⟶ A =>
    (globalModel.map t.op ≫ evaluationModel (op C')).functor)
      ((DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm.trans
        (Category.assoc q' p' a)))

private theorem evaluation_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    evaluationComparisonIso f ≪≫ isoWhiskerLeft (evaluationModel (op Y)).functor
      (isoWhiskerLeft AsSmall.down (isoWhiskerRight
        (eqToIso (congrArg boundedFlatNormalizedPullback e)) AsSmall.up)) =
    eqToIso (congrArg (fun t : X ⟶ Y =>
      (globalModel.map t.op ≫ evaluationModel (op X)).functor) e) ≪≫
        evaluationComparisonIso g := by
  subst g
  apply Iso.ext
  ext x
  simp only [Iso.trans_hom, eqToIso.hom, eqToHom_refl, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    NatTrans.id_app, Category.id_comp]
  exact Category.comp_id _

/-- The last triple retains the actual strict reference transport of both squares. -/
def lastNode (i : Fin 8) : InputTripleNodes.Node c q p :=
  ⟨(InputTripleNodes.rawNode q' p' a i).1,
    lastSourceIso p q p' q' a b c hp hq ≪≫ (InputTripleNodes.rawNode q' p' a i).2⟩

/-- Equality of full last-triple nodes includes its original geometric source transport. -/
theorem last_nodes (i : Fin 8) :
    rawNode p q p' q' a b c hp hq (DoubleSquareMergedSimplex.lastFace.toOrderHom i) =
      lastNode p q p' q' a b c hp hq i := by
  have e := (DoubleSquareMergedSimplex.last_nodes p q p' q' a b c hp hq i).trans
    (DoubleSquareCommonSimplex.last_nodes p q p' q' a b c hp hq i)
  unfold rawNode
  rw [e]
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change evaluationComparisonIso (c ≫ q ≫ p) ≪≫
    isoWhiskerLeft (evaluationModel (op A)).functor
      (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
        SplitTripleSimplex.references q' p' a i) = _
  rw [isoWhiskerLeft_trans, ← Iso.trans_assoc]
  rw [show evaluationComparisonIso (c ≫ q ≫ p) ≪≫
      isoWhiskerLeft (evaluationModel (op A)).functor
        (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq) =
      lastSourceIso p q p' q' a b c hp hq ≪≫ evaluationComparisonIso (q' ≫ p' ≫ a) from
    evaluation_transport ((DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm.trans
      (Category.assoc q' p' a))]
  exact Iso.trans_assoc _ _ _

/-- The original postcomposed evaluation total is raw rectangle node two. -/
theorem post_total_node : InputTripleNodes.postNode c q p 1 =
    rawNode p q p' q' a b c hp hq 2 :=
  (InputTripleNodes.post_total_node c q p).trans
    (first_nodes p q p' q' a b c hp hq 2).symm

/-- The original postcomposed geometric intermediate is raw rectangle node three. -/
theorem post_intermediate_node : InputTripleNodes.postNode c q p 2 =
    rawNode p q p' q' a b c hp hq 3 :=
  (InputTripleNodes.post_intermediate_node c q p).trans
    (first_nodes p q p' q' a b c hp hq 3).symm

/-- The original postcomposed fully split target is raw rectangle node eleven. -/
theorem post_target_node : InputTripleNodes.postNode c q p 4 =
    rawNode p q p' q' a b c hp hq 11 :=
  (InputTripleNodes.post_target_node c q p).trans
    (first_nodes p q p' q' a b c hp hq 7).symm

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputRectangleNodes
