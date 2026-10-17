/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.StableHomotopy

/-!
# Original K-groups of the actual small Waldhausen model

The original K-group of a small model is the nonnegative stable group of its
unchanged iterated-S prespectrum. Its structure map and stage-zero inclusion
supply the comparison. Naturality retains the exact original K-map of every
zero-preserving model arrow; no additional small-model replacement is made.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum

/-- The actual original K-group at the first stable stage of the same model. -/
def modelKStableStageEquiv (W : Model.{u}) (n : ℕ) :
    Additive (W.waldhausen.K n) ≃+ (stableSystem (prespectrum W) (n : ℤ)).obj 0 :=
  (structurePiEquiv (prespectrum W) (prespectrum_isOmega W) 1 n).toAdditive.trans
    (nonnegativeStableStageEquiv (prespectrum W) n)

/-- Original K-groups of the given model compute its actual nonnegative stable groups. -/
def modelKStableEquiv (W : Model.{u}) (n : ℕ) :
    Additive (W.waldhausen.K n) ≃+ stableHomotopyGroup (prespectrum W) (n : ℤ) :=
  (modelKStableStageEquiv W n).trans
    (stableHomotopyStageZeroIso (prespectrum W) (prespectrum_isOmega W)
      (n : ℤ)).symm.addCommGroupIsoToAddEquiv

/-- The comparison is precisely the actual first-stage inclusion. -/
theorem modelKStableEquiv_apply (W : Model.{u}) (n : ℕ) (a : Additive (W.waldhausen.K n)) :
    modelKStableEquiv W n a = stableHomotopyι (prespectrum W) (n : ℤ) 0
      (modelKStableStageEquiv W n a) := by
  change (stableHomotopyStageZeroIso (prespectrum W) (prespectrum_isOmega W) (n : ℤ)).inv
    (modelKStableStageEquiv W n a) = _
  rw [stableHomotopyStageZeroIso_inv]

/-- Original model K-maps commute with the displayed first-stage map. -/
theorem modelKStableStageEquiv_naturality {V W : Model.{u}} (F : V ⟶ W)
    (n : ℕ) (a : V.waldhausen.K n) :
    modelKStableStageEquiv W n (Additive.ofMul (KMap F.exact n a)) =
      (stableSystemMap (prespectrumMap F) (n : ℤ)).app 0
        (modelKStableStageEquiv V n (Additive.ofMul a)) := by
  change nonnegativeStableStageEquiv (prespectrum W) n
      (Additive.ofMul (structurePiMap (prespectrum W) 1 n (KMap F.exact n a))) =
    (stableSystemMap (prespectrumMap F) (n : ℤ)).app 0
      (nonnegativeStableStageEquiv (prespectrum V) n
        (Additive.ofMul (structurePiMap (prespectrum V) 1 n a)))
  rw [← nonnegativeStableStageEquiv_naturality]
  apply congrArg (nonnegativeStableStageEquiv (prespectrum W) n)
  apply congrArg Additive.ofMul
  rw [KMap_eq_piMap_of_zeroEq F.exact F.zero]
  exact congrArg (fun h ↦ h a) (structurePiMap_naturality (prespectrumMap F) 1 n)

/-- The comparison preserves every actual zero-preserving exact model arrow. -/
theorem modelKStableEquiv_naturality {V W : Model.{u}} (F : V ⟶ W)
    (n : ℕ) (a : V.waldhausen.K n) :
    modelKStableEquiv W n (Additive.ofMul (KMap F.exact n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap F)
        (modelKStableEquiv V n (Additive.ofMul a)) := by
  rw [modelKStableEquiv_apply, modelKStableEquiv_apply,
    modelKStableStageEquiv_naturality F]
  exact (ConcreteCategory.congr_hom
    (stableHomotopyι_naturality (prespectrumMap F) (n : ℤ) 0)
    (modelKStableStageEquiv V n (Additive.ofMul a))).symm

end Quillen.Waldhausen.IteratedS
