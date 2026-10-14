/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Topology.Prespectrum.HomotopySquareComposition
public import Quillen.Topology.Prespectrum.PushoutMovingHomotopy
public import Quillen.Topology.Prespectrum.HomotopySquareBoundary
public import Quillen.Topology.Prespectrum.ConeSquareMapMovingCoherence

/-! Identity descent preserving the exact moving chart tracks and the full original cylinder. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.HomotopyPushout
variable {A B : LoopPrespectrum.{u}} (f : A ⟶ B)

/-- The actual identity cylinder, with the target identities written as in map descent. -/
def identicalLegIdentityTargetTrack :
    Homotopy (f ≫ ((𝟙 B) ≫ inl f f)) (f ≫ ((𝟙 B) ≫ inr f f)) :=
  (glue f f).cast (by simp) (by simp)

/-- Both constant pieces of the identity square's original cylinder contract relatively. -/
def identicalLegIdentityTargetComparison :
    (mapSquareHomotopy f f f f (𝟙 A) (𝟙 B) (𝟙 B)
      (coneSquareIdentityTrack f) (coneSquareIdentityTrack f)).RelHomotopy
        (identicalLegIdentityTargetTrack f) := by
  have J := (Homotopy.RelHomotopy.reflTrans
    ((glue f f).trans (Homotopy.refl _))).trans (Homotopy.RelHomotopy.transRefl (glue f f))
  refine J.ofLevels _ _ ?_ (fun _ ↦ rfl)
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr <;> rfl

variable {a : A ⟶ A} {b : B ⟶ B}
  (H : Homotopy (f ≫ b) (a ≫ f)) (L : Homotopy a (𝟙 A)) (M : Homotopy b (𝟙 B))
  (Q : H.Square (coneSquareIdentityTrack f) (Homotopy.precomp f M) (L.postcomp f))

/-- The complete overlap square has the exact chart units and the unpaused identity cylinder. -/
def identicalLegIdentityCylinderSquare :
    (mapSquareHomotopy f f f f a b b H H).Square (identicalLegIdentityTargetTrack f)
      (Homotopy.precomp f (M.postcomp (inl f f)))
      (Homotopy.precomp f (M.postcomp (inr f f))) :=
  ((identicalLegMovingSquare f f H (coneSquareIdentityTrack f) L M Q).toBoundary.trans
    (((Homotopy.RelHomotopy.refl (Homotopy.precomp f (M.postcomp (inl f f)))).hcomp
      (identicalLegIdentityTargetComparison f)).hcomp
        (Homotopy.RelHomotopy.refl (Homotopy.precomp f (M.postcomp (inr f f))).symm))).toSquare

/-- Descent of the actual identity cylinder and target charts is the literal identity. -/
theorem identicalLegIdentityTargetDesc :
    desc f f ((𝟙 B) ≫ inl f f) ((𝟙 B) ≫ inr f f)
      (identicalLegIdentityTargetTrack f) = 𝟙 (prespectrum f f) := by
  apply hom_ext
  · simp only [inl_desc, Category.id_comp, Category.comp_id]
  · simp only [inr_desc, Category.id_comp, Category.comp_id]
  · intro n s x
    rfl

/-- A genuine original unit square supplies a whole span identity with exact chart tracks. -/
def identicalLegIdentityHomotopy :
    Homotopy (mapOfHomotopies f f f f a b b H H) (𝟙 (prespectrum f f)) :=
  (descSquareHomotopy f f (M.postcomp (inl f f)) (M.postcomp (inr f f))
    (identicalLegIdentityCylinderSquare f H L M Q)).cast rfl (identicalLegIdentityTargetDesc f)

/-- The first complete chart is the specified original unit, without added constant time. -/
theorem identicalLegIdentityHomotopy_inl (n : ℕ) (r : unitInterval) (x : B.space n) :
    (identicalLegIdentityHomotopy f H L M Q).level n (r, (inl f f).map n x) =
      (inl f f).map n (M.level n (r, x)) := rfl

/-- The second complete chart is the same original unit, without added constant time. -/
theorem identicalLegIdentityHomotopy_inr (n : ℕ) (r : unitInterval) (x : B.space n) :
    (identicalLegIdentityHomotopy f H L M Q).level n (r, (inr f f).map n x) =
      (inr f f).map n (M.level n (r, x)) := rfl

/-- Every original cylinder point retains both independent parameters of the constructed square. -/
theorem identicalLegIdentityHomotopy_cylinder (n : ℕ) (r s : unitInterval) (x : A.space n) :
    (identicalLegIdentityHomotopy f H L M Q).level n (r, cylinder f f n (s, x)) =
      (identicalLegIdentityCylinderSquare f H L M Q).level n (r, (s, x)) := rfl

end Quillen.LoopPrespectrum.HomotopyPushout
