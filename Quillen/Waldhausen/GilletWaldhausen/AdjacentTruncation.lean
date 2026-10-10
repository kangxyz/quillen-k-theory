/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.GilletWaldhausen.TruncationCoherence
public import Quillen.Waldhausen.GilletWaldhausen.TruncationLayer
public import Quillen.Waldhausen.GilletWaldhausen.TruncationCofibrationSequence

/-! # The actual adjacent-truncation cofibration sequence

The natural coherence iso turns the internal truncation sequence of
truncLE (n+1) into the actual adjacent sequence
truncLE n → truncLE (n+1) → identityDisk n (cycles (n+1)).
All three functors are genuinely exact, and the relative-cofibration
condition is proved by the generic exact-functor sequence theorem.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace Quillen.Waldhausen.GilletWaldhausen

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The canonical adjacent inclusion, characterized by compatibility with
both original inclusions into the untruncated complex. -/
def adjacentTruncationInclusion (n : ℤ) :
    boundedAcyclicTruncLEFunctor P n ⟶ boundedAcyclicTruncLEFunctor P (n + 1) :=
  (boundedAcyclicTruncLECompIso P n (n + 1) (by omega)).inv ≫
    Functor.whiskerLeft (boundedAcyclicTruncLEFunctor P (n + 1))
      (boundedAcyclicTruncationInclusion P n)

/-- The actual quotient projection, followed by the proved natural disk identification. -/
def adjacentTruncationProjection (n : ℤ) :
    boundedAcyclicTruncLEFunctor P (n + 1) ⟶
      boundedAcyclicCyclesFunctor P (n + 1) ⋙ boundedAcyclicDiskFunctor P n :=
  Functor.whiskerLeft (boundedAcyclicTruncLEFunctor P (n + 1))
    (boundedAcyclicTruncationProjection P n) ≫
    (oneStepLayerDiskIso P n).hom

/-- The adjacent inclusion has exactly the original ambient inclusion as composite. -/
@[reassoc]
theorem adjacentTruncationInclusion_ambient (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    ((adjacentTruncationInclusion P n).app K).hom ≫ K.obj.ιTruncLE (n + 1) =
      K.obj.ιTruncLE n := by
  change ((truncLECompIso (A := A) n (n + 1) (by omega)).inv.app K.obj ≫
      (K.obj.truncLE (n + 1)).ιTruncLE n) ≫ K.obj.ιTruncLE (n + 1) = _
  rw [Category.assoc, ← truncLECompIso_inclusion K.obj n (n + 1) (by omega)]
  simp

/-- The actual adjacent maps compose to zero. -/
@[reassoc]
theorem adjacentTruncation_comp_zero (n : ℤ) :
    adjacentTruncationInclusion P n ≫ adjacentTruncationProjection P n = 0 := by
  apply NatTrans.ext
  funext K
  let S := (acyclicTruncationSequenceFunctor P n).obj
    ((boundedAcyclicTruncLEFunctor P (n + 1)).obj K)
  change ((boundedAcyclicTruncLECompIso P n (n + 1) (by omega)).inv.app K ≫ S.f) ≫
    (S.g ≫ (oneStepLayerDiskIso P n).hom.app K) = 0
  rw [Category.assoc, ← Category.assoc S.f S.g, S.zero, zero_comp, comp_zero]

variable [(abelianExactStructure A).IsExtensionClosed P]

/-- The adjacent sequence is an actual inherited conflation, with its disk quotient. -/
theorem adjacentTruncation_conflation (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    (boundedAcyclicExactStructure P).conflation
      (ShortComplex.mk ((adjacentTruncationInclusion P n).app K)
        ((adjacentTruncationProjection P n).app K)
        (NatTrans.congr_app (adjacentTruncation_comp_zero P n) K)) := by
  let S := (acyclicTruncationSequenceFunctor P n).obj
    ((boundedAcyclicTruncLEFunctor P (n + 1)).obj K)
  let e := ShortComplex.isoMk
    ((boundedAcyclicTruncLECompIso P n (n + 1) (by omega)).app K)
    (Iso.refl S.X₂) ((oneStepLayerDiskIso P n).app K)
    (S₁ := S) (S₂ := ShortComplex.mk ((adjacentTruncationInclusion P n).app K)
      ((adjacentTruncationProjection P n).app K)
      (NatTrans.congr_app (adjacentTruncation_comp_zero P n) K))
    (by simp [adjacentTruncationInclusion, boundedAcyclicTruncationInclusion, S])
    (by simp [adjacentTruncationProjection, boundedAcyclicTruncationProjection, S])
  exact (boundedAcyclicExactStructure P).iso_closed e
    (acyclicTruncationSequenceFunctor_conflation P n _)

/-- The actual adjacent sequence satisfies every structural additivity
hypothesis with isomorphism weak equivalences. -/
theorem adjacentTruncation_isCofibrationSequence (n : ℤ) :
    Additivity.IsCofibrationSequence (ofExactCategory (boundedAcyclicExactStructure P))
      (ofExactCategory (boundedAcyclicExactStructure P))
      (adjacentTruncationInclusion P n) (adjacentTruncationProjection P n) :=
  exactFunctorSequence_isCofibrationSequence _ _ _ _ (adjacentTruncation_comp_zero P n)
    (adjacentTruncation_conflation P n)
    (boundedAcyclicTruncLEExactFunctor P n) (boundedAcyclicTruncLEExactFunctor P (n + 1))
    (oneStepCycleDiskExactFunctor P n) rfl rfl rfl

/-- The same actual adjacent sequence with genuine quasi-isomorphisms. -/
theorem adjacentTruncation_isCofibrationSequence_quasiIso (n : ℤ) :
    Additivity.IsCofibrationSequence (complexSubcategory (boundedAcyclic P))
      (complexSubcategory (boundedAcyclic P))
      (adjacentTruncationInclusion P n) (adjacentTruncationProjection P n) where
  exactF := boundedAcyclicExactFunctor_waldhausenExact P (boundedAcyclicTruncLEExactFunctor P n)
  exactG := boundedAcyclicExactFunctor_waldhausenExact P (boundedAcyclicTruncLEExactFunctor P (n
    + 1))
  exactH := boundedAcyclicExactFunctor_waldhausenExact P (oneStepCycleDiskExactFunctor P n)
  cofibration := {
    app_cof := (adjacentTruncation_isCofibrationSequence P n).cofibration.app_cof
    relative_cof f hf := (adjacentTruncation_isCofibrationSequence P n).cofibration.relative_cof
      f hf }
  cofiber := (adjacentTruncation_isCofibrationSequence P n).cofiber

end Quillen.Waldhausen.GilletWaldhausen
