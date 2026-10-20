/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.SplitSquareInput
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Source-null comparison for a split-square input

The specified source-null follows the positive split track and then the actual cone contraction.
Its input comparison is derived from the positive chart-pasting hypothesis and the independent
source-leg/cone interchange square. The negative chart pasting is used only through the input
cone map. No localization null or seed comparison is asserted.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.SplitSquare

/-- The specified positive split track followed by the actual cone contraction. -/
def sourceNull (S : SplitSquare.{u}) :
    Homotopy (S.l ≫ mappingConeInclusion S.comparison)
      (zeroHom S.A (mappingCone S.comparison)) := by
  have N := Homotopy.precomp S.sourceLeg (mappingConeHomotopy S.comparison)
  change Homotopy ((S.sourceLeg ≫ S.comparison) ≫ mappingConeInclusion S.comparison)
    (zeroHom _ _) at N
  exact (S.Dp.postcomp (mappingConeInclusion S.comparison)).trans
    (N.cast (congrArg (fun f ↦ f ≫ mappingConeInclusion S.comparison)
      S.sourceLeg_comparison) rfl)

/-- The positive split track occupies the first half and the cone contraction the second half. -/
theorem sourceNull_apply (S : SplitSquare.{u}) (n : ℕ) (s : unitInterval)
    (x : S.A.space n) :
    S.sourceNull.level n (s, x) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        (mappingConeInclusion S.comparison).map n
          (S.Dp.level n
            (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x))
      else (mappingConeHomotopy S.comparison).level n
        (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 hs).le, s.2.2⟩⟩, S.sourceLeg.map n x) := by
  change (ContinuousMap.HomotopyRel.trans _ _) (s, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split <;> rfl

namespace Input
variable {S S' : SplitSquare.{u}} (i : Input S S')

namespace InputNull

/-- The original positive-leg track after target input change and cone inclusion. -/
def oldPositive :=
  (S.Dp.postcomp i.c).postcomp (mappingConeInclusion S'.comparison)

/-- The actual positive input square on the original chart projection. -/
def positiveMovement :=
  ((Homotopy.precomp S.pi i.Hp).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).postcomp
      (mappingConeInclusion S'.comparison)

/-- The original chart input track followed by the positive target leg. -/
def projectionMovement :=
  (i.Q.postcomp S'.p).postcomp (mappingConeInclusion S'.comparison)

/-- The original common target input square after target cone inclusion. -/
def outerMovement :=
  i.T.postcomp (mappingConeInclusion S'.comparison)

/-- The target positive-leg comparison preceded by the original base input map. -/
def newPositive :=
  ((Homotopy.precomp i.a S'.Dp).cast rfl (Category.assoc _ _ _).symm).postcomp
    (mappingConeInclusion S'.comparison)

/-- The supplied positive-chart pasting retains its full cone-image track. -/
def positivePasting :
    ((positiveMovement i).trans (projectionMovement i)).RelHomotopy
      ((oldPositive i).symm.trans ((outerMovement i).trans (newPositive i))) := by
  simpa only [Homotopy.postcomp_trans, Homotopy.postcomp_symm, positiveMovement,
    projectionMovement, oldPositive, outerMovement, newPositive] using
    i.Jp.postcomp (mappingConeInclusion S'.comparison)

/-- Cancel the actual positive-leg inverse to recover the specified three-track route. -/
def straightPositivePasting :
    (((oldPositive i).trans (positiveMovement i)).trans
      (projectionMovement i)).RelHomotopy
        ((outerMovement i).trans (newPositive i)) := by
  let A := oldPositive i
  let B := positiveMovement i
  let Q := projectionMovement i
  let T := (outerMovement i).trans (newPositive i)
  exact (Homotopy.RelHomotopy.transAssoc A B Q).trans
    (((Homotopy.RelHomotopy.refl A).hcomp (positivePasting i)).trans
      ((Homotopy.RelHomotopy.transAssoc A A.symm T).symm.trans
        (((Homotopy.RelHomotopy.reflTransSymm A).symm.hcomp
          (Homotopy.RelHomotopy.refl T)).trans (Homotopy.RelHomotopy.reflTrans T))))

/-- The old source-leg image traverses the original target cone cylinder. -/
def oldCone : Homotopy
    (((S.pi ≫ i.b) ≫ S'.p) ≫ mappingConeInclusion S'.comparison) (zeroHom _ _) :=
  (Homotopy.precomp (S.sourceLeg ≫ spanMap i)
    (mappingConeHomotopy S'.comparison)).cast (by
      apply Hom.ext
      funext n
      ext x
      rfl) rfl

/-- The new source-leg image traverses the same original target cone cylinder. -/
def newCone : Homotopy
    (((i.a ≫ S'.pi) ≫ S'.p) ≫ mappingConeInclusion S'.comparison) (zeroHom _ _) :=
  (Homotopy.precomp (i.a ≫ S'.sourceLeg)
    (mappingConeHomotopy S'.comparison)).cast (by
      apply Hom.ext
      funext n
      ext x
      rfl) rfl

/-- The original source-leg cone square supplies its actual chart-movement pasting. -/
def conePasting :
    (oldCone i).RelHomotopy ((projectionMovement i).trans (newCone i)) := by
  let Z := Homotopy.refl (zeroHom S.A (mappingCone S'.comparison))
  have J : (oldCone i).RelHomotopy
      (((projectionMovement i).trans (newCone i)).trans Z) := by
    refine (sourceLegInputConeBoundary i).ofLevels _ _ ?_ ?_
    · intro n
      rfl
    · intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr
        · apply ContinuousMap.ext
          rintro ⟨s, x⟩
          rfl
        · rfl
      · rfl
  exact J.trans (Homotopy.RelHomotopy.transRefl _)

/-- The supplied positive pasting and actual cone square paste to the target null route. -/
def pastedNullComparison :
    ((oldPositive i).trans ((positiveMovement i).trans (oldCone i))).RelHomotopy
      ((outerMovement i).trans ((newPositive i).trans (newCone i))) := by
  let A := oldPositive i
  let B := positiveMovement i
  let Q := projectionMovement i
  let E := oldCone i
  let G := newCone i
  let L := outerMovement i
  let F := newPositive i
  exact (Homotopy.RelHomotopy.transAssoc A B E).symm.trans
    (((Homotopy.RelHomotopy.refl (A.trans B)).hcomp (conePasting i)).trans
      ((Homotopy.RelHomotopy.transAssoc (A.trans B) Q G).symm.trans
        (((straightPositivePasting i).hcomp (Homotopy.RelHomotopy.refl G)).trans
          (Homotopy.RelHomotopy.transAssoc L F G))))

/-- The source nullhomotopy followed by the actual input cone map. -/
def originalOldNull : Homotopy
    ((S.l ≫ i.c) ≫ mappingConeInclusion S'.comparison) (zeroHom _ _) :=
  (S.sourceNull.postcomp (coneMap i)).cast (by
    apply Hom.ext
    funext n
    ext x
    rfl) (by
      apply Hom.ext
      funext n
      ext x
      exact (coneMap i).map_point n)

/-- The target nullhomotopy preceded by actual base input change. -/
def originalNewNull : Homotopy
    ((i.a ≫ S'.l) ≫ mappingConeInclusion S'.comparison) (zeroHom _ _) :=
  (Homotopy.precomp i.a S'.sourceNull).cast (Category.assoc _ _ _).symm rfl

/-- Every original target-null coordinate is its unchanged positive leg and cone cylinder. -/
lemma originalNewNull_level (n : ℕ) :
    (originalNewNull i).level n = ((newPositive i).trans (newCone i)).level n := by
  unfold originalNewNull
  rw [Homotopy.cast_level]
  change ((Homotopy.precomp i.a (S'.Dp.postcomp (mappingConeInclusion S'.comparison))).trans
      (Homotopy.precomp i.a
        (Homotopy.precomp S'.sourceLeg
          (mappingConeHomotopy S'.comparison)))).level n = _
  apply Homotopy.trans_level_congr <;> rfl

/-- Each mapped old-null coordinate retains the positive leg and actual cone-square map. -/
lemma originalOldNull_level (n : ℕ) :
    (originalOldNull i).level n =
      ((oldPositive i).trans ((positiveMovement i).trans (oldCone i))).level n := by
  unfold originalOldNull
  rw [Homotopy.cast_level]
  change (((S.Dp.postcomp (mappingConeInclusion S.comparison)).trans
      (Homotopy.precomp S.sourceLeg
        (mappingConeHomotopy S.comparison))).postcomp
          (coneMap i)).level n = _
  rw [Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    rfl
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    rfl

/-- The two unchanged target nullhomotopies compare along the actual target input track. -/
def originalNullComparison :
    (originalOldNull i).RelHomotopy ((outerMovement i).trans (originalNewNull i)) := by
  refine (pastedNullComparison i).ofLevels _ _ (originalOldNull_level i) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact originalNewNull_level i n

end InputNull

end Input
end Quillen.LoopPrespectrum.SplitSquare
