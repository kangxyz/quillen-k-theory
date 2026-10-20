/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.StrictSquareNull
public import Quillen.Topology.Prespectrum.SplitSquareSourceNull
public import Quillen.Topology.Prespectrum.RelativeHomotopyStrictSquarePasting

/-!
# Evaluation from an original strict square to a split square

Four actual corner maps and their edge tracks, together with the two proved chart pastings,
map the original strict double cylinder and comparison cone into the split target. The source
remains the given strict square, with its constant overlap and its undelayed source-null.
The two source chart objects and projection tracks need not coincide. This reusable interface
assumes the displayed chart pastings; concrete evaluation producers must prove them.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.StrictSquare

/-- The four actual evaluation corners, edge tracks and whole chart pastings. -/
structure SplitEvaluation (S : Arrow (Arrow LoopPrespectrum.{u})) (R : SplitSquare.{u}) where
  /-- The source-corner evaluation. -/
  a : S.left.left ⟶ R.A
  /-- The positive-chart evaluation. -/
  bp : S.left.right ⟶ R.P
  /-- The negative-chart evaluation. -/
  bm : S.right.left ⟶ R.P
  /-- The common-target evaluation. -/
  c : S.right.right ⟶ R.L
  /-- The positive projection square. -/
  Qp : Homotopy (S.left.hom ≫ bp) (a ≫ R.pi)
  /-- The negative projection square. -/
  Qm : Homotopy (S.hom.left ≫ bm) (a ≫ R.pi)
  /-- The positive chart square. -/
  Hp : Homotopy (S.hom.right ≫ c) (bp ≫ R.p)
  /-- The negative chart square. -/
  Hm : Homotopy (S.right.hom ≫ c) (bm ≫ R.m)
  /-- The diagonal square uses the original positive strict composite. -/
  T : Homotopy ((S.left.hom ≫ S.hom.right) ≫ c) (a ≫ R.l)
  /-- The actual positive chart pasting, without an inserted constant prefix. -/
  Jp :
    (((Homotopy.precomp S.left.hom Hp).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
        (Qp.postcomp R.p)).RelHomotopy
      (T.trans ((Homotopy.precomp a R.Dp).cast rfl (Category.assoc _ _ _).symm))
  /-- The negative chart starts at the same diagonal by the original strict square equation. -/
  Jm :
    (((Homotopy.precomp S.hom.left Hm).cast
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f ↦ f ≫ c) S.hom.w)) (Category.assoc _ _ _).symm).trans
        (Qm.postcomp R.m)).RelHomotopy
      (T.trans ((Homotopy.precomp a R.Dm).cast rfl (Category.assoc _ _ _).symm))

namespace SplitEvaluation
variable {S : Arrow (Arrow LoopPrespectrum.{u})} {R : SplitSquare.{u}}
  (i : SplitEvaluation S R)

/-- The positive moving chart starts at the original strict diagonal. -/
def positiveTrack :=
  (Homotopy.precomp S.left.hom i.Hp).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

/-- The negative moving chart starts at that same diagonal using the whole strict equation. -/
def negativeTrack :=
  (Homotopy.precomp S.hom.left i.Hm).cast
    ((Category.assoc _ _ _).symm.trans (congrArg (fun f ↦ f ≫ i.c) S.hom.w))
    (Category.assoc _ _ _).symm

/-- The complete original source cylinder followed by target evaluation. -/
def sourceTrack := (StrictSquare.track S).postcomp i.c

/-- Both projection tracks surround the target's original positive-backwards/negative overlap. -/
def targetTrack :=
  (i.Qp.postcomp R.p).trans
    (((Homotopy.precomp i.a R.squareHomotopy).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
      (i.Qm.postcomp R.m).symm)

/-- The moving boundary retains the actual uncollapsed negative source leg. -/
def pastedTrack :=
  ((positiveTrack i).trans (targetTrack i)).trans
    ((Homotopy.precomp S.hom.left i.Hm).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).symm

/-- The two proved chart pastings cancel their common original diagonal movement. -/
def boundary :=
  Homotopy.RelHomotopy.pasteStrictSourceSquares i.Jp i.Jm

/-- The split target overlap is precisely the middle of the two chart pastings. -/
theorem middleTrack_level (n : ℕ) :
    ((Homotopy.precomp i.a R.squareHomotopy).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).level n =
    (((Homotopy.precomp i.a R.Dp).cast rfl (Category.assoc _ _ _).symm).symm.trans
      ((Homotopy.precomp i.a R.Dm).cast rfl (Category.assoc _ _ _).symm)).level n := by
  simp only [Homotopy.cast_level, SplitSquare.squareHomotopy,
    Homotopy.precomp_trans, Homotopy.precomp_symm]
  rfl

/-- The original constant source cylinder has the proved full moving boundary. -/
def pasting : (sourceTrack i).RelHomotopy (pastedTrack i) := by
  apply (boundary i).ofLevels
  · intro n
    rfl
  · intro n
    apply Homotopy.trans_level_congr
    · apply Homotopy.trans_level_congr
      · rfl
      · apply Homotopy.trans_level_congr
        · rfl
        · apply Homotopy.trans_level_congr
          · exact middleTrack_level i n
          · rfl
    · rfl

/-- Actual corner evaluations and projection tracks map the original strict source span. -/
def spanMap : StrictSquare.span S ⟶ R.span :=
  HomotopyPushout.mapOfHomotopies S.left.hom S.hom.left R.pi R.pi
    i.a i.bp i.bm i.Qp i.Qm

/-- Source comparison endpoints are grouped for literal quotient descent. -/
def sourceDescTrack := (sourceTrack i).cast (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Target comparison endpoints are grouped for that same quotient descent. -/
def targetDescTrack := (targetTrack i).cast (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Both original moving chart sides retain the actual source projections. -/
def pastedDescTrack :=
  ((Homotopy.precomp S.left.hom i.Hp).trans (targetDescTrack i)).trans
    (Homotopy.precomp S.hom.left i.Hm).symm

/-- The whole chart boundary supplies the complete moving descent square. -/
def descPasting : (sourceDescTrack i).RelHomotopy (pastedDescTrack i) :=
  (pasting i).ofLevels _ _ (fun _ ↦ rfl) (by
    intro n
    apply Homotopy.trans_level_congr
    · apply Homotopy.trans_level_congr <;> rfl
    · rfl)

/-- Every mapped span-cylinder point is followed by the unchanged target comparison. -/
theorem targetDescTrack_level (n : ℕ) :
    (targetDescTrack i).level n =
      ((HomotopyPushout.mapSquareHomotopy S.left.hom S.hom.left R.pi R.pi
        i.a i.bp i.bm i.Qp i.Qm).postcomp R.comparison).level n := by
  simp only [targetDescTrack, Homotopy.cast_level, targetTrack,
    HomotopyPushout.mapSquareHomotopy, Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr
    · rfl
    · exact congrArg (fun H ↦ H.level n) (Homotopy.postcomp_symm i.Qm R.m).symm

/-- Source descent is the literal strict comparison followed by common-target evaluation. -/
theorem sourceDesc_eq :
    HomotopyPushout.desc S.left.hom S.hom.left
      (S.hom.right ≫ i.c) (S.right.hom ≫ i.c) (sourceDescTrack i) =
      StrictSquare.comparison S ≫ i.c := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    rfl

/-- Target descent is the actual span evaluation followed by the original split comparison. -/
theorem targetDesc_eq :
    HomotopyPushout.desc S.left.hom S.hom.left
      (i.bp ≫ R.p) (i.bm ≫ R.m) (targetDescTrack i) = spanMap i ≫ R.comparison := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    exact DFunLike.congr_fun (targetDescTrack_level i n) (s, x)

/-- The original overlap descends to a homotopy between the two actual comparison maps. -/
def comparisonHomotopy :
    Homotopy (StrictSquare.comparison S ≫ i.c) (spanMap i ≫ R.comparison) :=
  (HomotopyPushout.descSquareHomotopy (H₀ := sourceDescTrack i) (H₁ := targetDescTrack i)
    S.left.hom S.hom.left i.Hp i.Hm (descPasting i).toSquare).cast
      (sourceDesc_eq i) (targetDesc_eq i)

/-- The entire positive chart track survives descent. -/
theorem comparisonHomotopy_inl (n : ℕ) (r : unitInterval) (x : S.left.right.space n) :
    (comparisonHomotopy i).level n
      (r, (HomotopyPushout.inl S.left.hom S.hom.left).map n x) =
      i.Hp.level n (r, x) := rfl

/-- The distinct negative chart track also survives descent. -/
theorem comparisonHomotopy_inr (n : ℕ) (r : unitInterval) (x : S.right.left.space n) :
    (comparisonHomotopy i).level n
      (r, (HomotopyPushout.inr S.left.hom S.hom.left).map n x) =
      i.Hm.level n (r, x) := rfl

/-- Both original overlap coordinates remain independent. -/
theorem comparisonHomotopy_cylinder (n : ℕ) (r s : unitInterval) (x : S.left.left.space n) :
    (comparisonHomotopy i).level n
      (r, HomotopyPushout.cylinder S.left.hom S.hom.left n (s, x)) =
      (descPasting i).toSquare.level n (r, (s, x)) := rfl

/-- The complete evaluation square maps the original strict cone to the split cone. -/
def coneMap : mappingCone (StrictSquare.comparison S) ⟶ mappingCone R.comparison :=
  mappingConeSquareMap (StrictSquare.comparison S) R.comparison
    (spanMap i) i.c (comparisonHomotopy i)

/-- Common-target evaluation remains literal on cone inclusion. -/
theorem coneMap_inclusion :
    mappingConeInclusion (StrictSquare.comparison S) ≫ coneMap i =
      i.c ≫ mappingConeInclusion R.comparison :=
  mappingConeSquareMap_inclusion _ _ _ _ _

/-- Parameter looping retains the actual strict one-step source. -/
def map : strictSquareLoopedConeFunctor.obj S ⟶ R.step := parameterLoopingMap (coneMap i)

/-- The original source leg retains the positive source endpoint under span evaluation. -/
theorem sourceLeg_evaluation :
    StrictSquare.sourceLeg S ≫ spanMap i =
      (S.left.hom ≫ i.bp) ≫ HomotopyPushout.inl R.pi R.pi := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- The positive projection track moves the original source leg through the actual target span. -/
def sourceLegHomotopy :
    Homotopy (StrictSquare.sourceLeg S ≫ spanMap i) (i.a ≫ R.sourceLeg) :=
  (i.Qp.postcomp (HomotopyPushout.inl R.pi R.pi)).cast
    (sourceLeg_evaluation i).symm (Category.assoc _ _ _)

/-- Source-leg movement and the unchanged target cone contraction retain both coordinates. -/
def sourceLegConeSquare :=
  Homotopy.Square.interchange (sourceLegHomotopy i) (mappingConeHomotopy R.comparison)

/-- The source-leg cone interchange supplies its whole pasted boundary. -/
def sourceLegConeBoundary := (sourceLegConeSquare i).toBoundary

end SplitEvaluation
end Quillen.LoopPrespectrum.StrictSquare
