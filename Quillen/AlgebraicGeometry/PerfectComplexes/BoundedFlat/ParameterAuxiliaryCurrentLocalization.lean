/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterTelescopeNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryCurrentFiber
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterTelescopeSquares

/-!
# The original auxiliary-supported localization lift on the current-stage model

The original G7 same-null theorem supplies the iterated-seed lift. The three
actual stable Spec-row comparisons and the proved four-model same-null iff
transport precisely that lift. The compactness of the auxiliary open is retained.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.ParameterAuxiliaryCurrentFiber
open GlobalSectionChangeIndex ParameterAuxiliarySupport GlobalAuxiliaryParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)
    [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] [CompactSpace T]

/-- The original G7 same-null lift is stable after the actual integral Spec-row comparison. -/
theorem iteratedLift_spec_isStableEquivalence
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (iteratedLift f.left T (specUnder.obj a)) := by
  have hf := congrArg (fun k => k.app a) (telescope_enlargement_square f T)
  have hr := congrArg (fun k => k.app a) (telescope_restriction_square f T)
  have hiff := homotopyFiberLift_isStableEquivalence_iff
    ((iteratedEnlargement f.left T).app (specUnder.obj a))
    ((iteratedRestriction f.left T).app (specUnder.obj a))
    ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
    ((boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
    ((iteratedNull f.left T).homotopy (specUnder.obj a))
    ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a)
    ((fiberTelescopeComparison f T).app a)
    ((ambientTelescopeComparison Q T).app a) ((openTelescopeComparison f T).app a)
    hf hr.symm (telescope_fullNull_square f T a)
    (fiberTelescopeComparison_stable f T a)
    (ambientTelescopeComparison_stable Q T a) (openTelescopeComparison_stable f T a)
  exact hiff.mpr
    (boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence f T a)

/-- The actual current-stage auxiliary lift is stable with the original G7 hypotheses. -/
theorem currentLift_spec_isStableEquivalence
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (currentLift f.left T (specUnder.obj a)) :=
  (current_iterated_lift_stable_iff f.left T (specUnder.obj a)).mpr
    (iteratedLift_spec_isStableEquivalence f T a)

/-- At the actual integer basepoint the same auxiliary current-stage lift is stable. -/
theorem currentLift_integer_isStableEquivalence {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    (T : Q.Opens) [CompactSpace T] :
    IsStableEquivalence (currentLift f T (op integerBase)) := by
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
  exact currentLift_spec_isStableEquivalence g T (Under.mk (𝟙 _))

/-- Every signed stable degree retains the same actual current-stage auxiliary lift. -/
theorem currentLift_integer_signed_isIso {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    (T : Q.Opens) [CompactSpace T] (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (currentLift f T (op integerBase))) :=
  currentLift_integer_isStableEquivalence f T d

/-- Projection of the same original-null current lift is the actual auxiliary enlargement. -/
theorem currentLift_projection {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    currentLift f T X ≫ homotopyFiberProjection ((currentRestriction f T).app X) =
      (currentEnlargement f T).app X :=
  homotopyFiberLift_projection _ _ _

end Quillen.PerfectComplexes.ParameterAuxiliaryCurrentFiber
