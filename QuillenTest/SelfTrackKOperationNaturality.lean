/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationNaturality

/-! # Original exact-functor maps on K-zero and every higher self-track operation -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.Waldhausen
open Quillen.Waldhausen.IteratedS
universe u v
namespace QuillenTest.SelfTrackKOperationNaturality
variable {C D T : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} T]
  (W : Structure C) (V : Structure D) (U : Structure T)
  {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- Original K-zero target naturality retains the exact original K-one target map. -/
theorem original_kzero_target (H : Homotopy f f)
    {J : D ⥤ T} (hJ : IsExact V.cof V.weq U.cof U.weq J) :
    originalKSelfTrackOperation W U (H.postcomp (exactOriginalPrespectrumMap V U hJ)) 0 =
      (KMap hJ 1).comp (originalKSelfTrackOperation W V H 0) :=
  originalKSelfTrackOperation_postcomp W V U H hJ 0

/-- Original K-zero source naturality retains the exact original K-zero source map. -/
theorem original_kzero_source (H : Homotopy f f)
    {J : T ⥤ C} (hJ : IsExact U.cof U.weq W.cof W.weq J) :
    originalKSelfTrackOperation U V (H.precomp (exactOriginalPrespectrumMap U W hJ)) 0 =
      (originalKSelfTrackOperation W V H 0).comp (KMap hJ 0) :=
  originalKSelfTrackOperation_precomp W V U H hJ 0

/-- Every original higher target K-class follows the same unchanged exact functor. -/
theorem original_target_all_degrees (H : Homotopy f f)
    {J : D ⥤ T} (hJ : IsExact V.cof V.weq U.cof U.weq J) (n : ℕ) (a : W.K n) :
    originalKSelfTrackOperation W U (H.postcomp (exactOriginalPrespectrumMap V U hJ)) n a =
      KMap hJ (n + 1) (originalKSelfTrackOperation W V H n a) :=
  originalKSelfTrackOperation_postcomp_apply W V U H hJ n a

end QuillenTest.SelfTrackKOperationNaturality
