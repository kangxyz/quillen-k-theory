/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Plus
public import Quillen.KTheory.Plus.ProjectiveCompletionBaseChange
public import Quillen.KTheory.Plus.ProjectiveCompletionGradeNaturality
public import Quillen.KTheory.Map.RightBaseChange
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Independent right-module plus comparison naturality client

The common ring universe is arbitrary. Virtual K-zero classes retain the original
numerator and denominator; these statements do not classify path components.
-/
public section
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
open Quillen.FiniteProjectiveModule.StableCompletion
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
universe u
namespace Consumer.RingPlusNaturality

/-- The original virtual object class is numerator divided by denominator. -/
theorem virtualClassFormula {R : Type u} [Ring R] (U : Completion R) :
    completionKZeroClass Rᵐᵒᵖ U =
      (exactStructure Rᵐᵒᵖ).kZeroObjectClass U.obj.2.of /
        (exactStructure Rᵐᵒᵖ).kZeroObjectClass U.obj.1.of :=
  completionKZeroClass_eq_objectClasses Rᵐᵒᵖ U

/-- Actual ring change preserves these original virtual K-zero object classes. -/
theorem virtualClassNaturality {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (U : Completion R) :
    (rightBaseChangeExact f).KMap 0 (completionKZeroClass Rᵐᵒᵖ U) =
      completionKZeroClass Sᵐᵒᵖ ((completionBaseChange f).obj U) :=
  completionKZeroClass_baseChange f U

/-- Identity ring change acts identically on the preexisting original K-groups. -/
theorem originalKMapIdentity {R : Type u} [Ring R] (n : ℕ)
    (a : (exactStructure Rᵐᵒᵖ).K n) :
    (rightBaseChangeExact (RingHom.id R)).KMap n a = a := by
  rw [rightBaseChangeExact_KMap_id]
  rfl

/-- Composed ring change uses the preexisting original K-map composition law. -/
theorem originalKMapComposition {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) (n : ℕ) (a : (exactStructure Rᵐᵒᵖ).K n) :
    (rightBaseChangeExact (g.comp f)).KMap n a =
      (rightBaseChangeExact g).KMap n ((rightBaseChangeExact f).KMap n a) := by
  rw [rightBaseChangeExact_KMap_comp]
  rfl

/-- A concrete noncommutative ring retains the original positive comparison. -/
example (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (ZeroComponent (Matrix (Fin 2) (Fin 2) ℤ))
      (zeroBase (Matrix (Fin 2) (Fin 2) ℤ)) ≃*
        (exactStructure (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ).K (n + 1) :=
  zeroCompletionPositiveKEquiv _ n

/-- The actual map from the integers to the zero ring preserves virtual object classes. -/
example (U : Completion ℤ) :
    (rightBaseChangeExact (Int.castRingHom (ZMod 1))).KMap 0
        (completionKZeroClass ℤᵐᵒᵖ U) =
      completionKZeroClass (ZMod 1)ᵐᵒᵖ
        ((completionBaseChange (Int.castRingHom (ZMod 1))).obj U) :=
  virtualClassNaturality _ U

/-- The actual positive comparison square for arbitrary common-universe noncommutative rings. -/
theorem positiveComparisonSquare {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ZeroComponent R) (zeroBase R)) :
    zeroCompletionPositiveKEquiv S n
      (pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) n
        (homotopyGroupMapHom (N := Fin (n + 1)) (zeroCompletionBaseChangeMap f) rfl a)) =
    (rightBaseChangeExact f).KMap (n + 1) (zeroCompletionPositiveKEquiv R n a) :=
  zeroCompletionPositiveKEquiv_baseChange f n a

/-- Identity acts identically after the original basepoint-path correction. -/
theorem correctedMapIdentity {R : Type u} [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ZeroComponent R) (zeroBase R)) :
    pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath (RingHom.id R)) n
      (homotopyGroupMapHom (N := Fin (n + 1))
        (zeroCompletionBaseChangeMap (RingHom.id R)) rfl a) = a := by
  apply (zeroCompletionPositiveKEquiv R n).injective
  rw [positiveComparisonSquare, rightBaseChangeExact_KMap_id]
  rfl

/-- Composition retains the actual map and each actual correction path before comparison. -/
theorem correctedMapComposition {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ZeroComponent R) (zeroBase R)) :
    pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath (g.comp f)) n
      (homotopyGroupMapHom (N := Fin (n + 1))
        (zeroCompletionBaseChangeMap (g.comp f)) rfl a) =
    pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath g) n
      (homotopyGroupMapHom (N := Fin (n + 1)) (zeroCompletionBaseChangeMap g) rfl
        (pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) n
          (homotopyGroupMapHom (N := Fin (n + 1))
            (zeroCompletionBaseChangeMap f) rfl a))) := by
  apply (zeroCompletionPositiveKEquiv T n).injective
  rw [positiveComparisonSquare, positiveComparisonSquare, positiveComparisonSquare,
    rightBaseChangeExact_KMap_comp]
  rfl

/-- The literal positive square specializes to a genuinely noncommutative matrix ring. -/
example (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ZeroComponent (Matrix (Fin 2) (Fin 2) ℤ))
      (zeroBase (Matrix (Fin 2) (Fin 2) ℤ))) :
    zeroCompletionPositiveKEquiv (Matrix (Fin 2) (Fin 2) ℤ) n
      (pathTransportMulEquiv
        (zeroCompletionBaseChangeBasepointPath (RingHom.id (Matrix (Fin 2) (Fin 2) ℤ))) n
        (homotopyGroupMapHom (N := Fin (n + 1))
          (zeroCompletionBaseChangeMap (RingHom.id (Matrix (Fin 2) (Fin 2) ℤ))) rfl a)) =
    (rightBaseChangeExact (RingHom.id (Matrix (Fin 2) (Fin 2) ℤ))).KMap (n + 1)
      (zeroCompletionPositiveKEquiv (Matrix (Fin 2) (Fin 2) ℤ) n a) :=
  positiveComparisonSquare _ n a

/-- The positive square also retains the actual map from the integers to the zero ring. -/
example (n : ℕ) (a : HomotopyGroup.Pi (n + 1) (ZeroComponent ℤ) (zeroBase ℤ)) :
    zeroCompletionPositiveKEquiv (ZMod 1) n
      (pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath (Int.castRingHom (ZMod 1))) n
        (homotopyGroupMapHom (N := Fin (n + 1))
          (zeroCompletionBaseChangeMap (Int.castRingHom (ZMod 1))) rfl a)) =
    (rightBaseChangeExact (Int.castRingHom (ZMod 1))).KMap (n + 1)
      (zeroCompletionPositiveKEquiv ℤ n a) :=
  positiveComparisonSquare _ n a

end Consumer.RingPlusNaturality
