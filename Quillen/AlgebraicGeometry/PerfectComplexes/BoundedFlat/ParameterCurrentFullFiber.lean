/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterIteratedTwistedFiber
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterIteratedFullFiber
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterIdentityModels

/-! # The original current-stage full-open fiber lift at the integer Spec row

The existing fine localization theorem is transported through the actual original
seed-iterate, twisted, and current-stage comparisons, preserving the selected full null.
The support category and the current-stage scalar seed are unchanged.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes.ParameterFullCurrentNull

/-- The actual current-stage same-null full-open lift is stable on the integral Spec row. -/
theorem currentLift_spec_isStableEquivalence
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (currentLift f.left (specUnder.obj a)) :=
  (current_twisted_lift_stable_iff f.left (specUnder.obj a)).mpr
    ((iterated_twisted_lift_stable_iff f.left (specUnder.obj a)).mp
      (iteratedLift_spec_isStableEquivalence f a))

/-- At the actual integer basepoint the same current-stage lift is stable for the original pair. -/
theorem currentLift_integer_isStableEquivalence {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q] :
    IsStableEquivalence (currentLift f (op integerBase)) := by
  let g : Over.mk (toIntegerBase P) ⟶ Over.mk (toIntegerBase Q) :=
    Over.homMk f (toIntegerBase_naturality f)
  let : IsOpenImmersion g.left := by change IsOpenImmersion f; infer_instance
  let : CompactSpace (Over.mk (toIntegerBase P)).left := by
    change CompactSpace P
    infer_instance
  let : CompactSpace (Over.mk (toIntegerBase Q)).left := by
    change CompactSpace Q
    infer_instance
  let : QuasiSeparatedSpace (Over.mk (toIntegerBase Q)).left := by
    change QuasiSeparatedSpace Q
    infer_instance
  exact currentLift_spec_isStableEquivalence g (Under.mk (𝟙 _))

/-- Every signed stable homotopy degree sees the same current-stage lift as an iso. -/
theorem currentLift_integer_signed_isIso {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (currentLift f (op integerBase))) :=
  currentLift_integer_isStableEquivalence f d

end Quillen.PerfectComplexes.ParameterFullCurrentNull
