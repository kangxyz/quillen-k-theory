/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Pushforward.Affine

/-! Actual resolution augmentations and the original degree-zero derived unit. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace QuillenTest.AffineDerivedPushforward

/-- The standard ambient derived category used by the actual derived unit. -/
local instance standardDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- The actual integer-indexed resolution augmentation is preserved. -/
theorem original_integer_augmentation {Z X : Scheme.{u}} (f : Z ⟶ X) [IsAffineHom f]
    (M : Z.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M) :
    QuasiIso (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).map I.ι') :=
  AlgebraicGeometry.Scheme.Modules.quasiIso_pushforward_injectiveResolution_int f M I

/-- The original bounded-below derived unit on every quasicoherent module is invertible. -/
theorem original_single_unit {Z X : Scheme.{u}} (f : Z ⟶ X) [IsAffineHom f]
    (M : Z.Modules) [M.IsQuasicoherent] :
    IsIso ((AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlusUnit f).app
      (AlgebraicGeometry.Scheme.Modules.singleZeroPlus Z M)) :=
  AlgebraicGeometry.Scheme.Modules.isIso_derivedPushforwardPlusUnit_single f M

/-- Naturality retains the original map of degree-zero sheaves. -/
theorem original_single_square {Z X : Scheme.{u}} (f : Z ⟶ X)
    (M N : Z.Modules) (s : M ⟶ N) :
    DerivedCategory.Plus.Q.map ((Scheme.Modules.pushforward f).mapCochainComplexPlus.map
        (ObjectProperty.homMk ((CochainComplex.singleFunctor Z.Modules 0).map s) :
          AlgebraicGeometry.Scheme.Modules.singleZeroPlus Z M ⟶
            AlgebraicGeometry.Scheme.Modules.singleZeroPlus Z N)) ≫
        (AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlusUnit f).app
          (AlgebraicGeometry.Scheme.Modules.singleZeroPlus Z N) =
      (AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlusUnit f).app
        (AlgebraicGeometry.Scheme.Modules.singleZeroPlus Z M) ≫
        (DerivedCategory.Plus.Q ⋙ AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlus f).map
          (ObjectProperty.homMk ((CochainComplex.singleFunctor Z.Modules 0).map s) :
            AlgebraicGeometry.Scheme.Modules.singleZeroPlus Z M ⟶
              AlgebraicGeometry.Scheme.Modules.singleZeroPlus Z N) :=
  (AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlusUnit f).naturality _

end QuillenTest.AffineDerivedPushforward
