/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenConnectiveInvertibility
public import Quillen.Topology.Prespectrum.ConeDescNaturality

/-!
# Connective invertibility of the original supported Bass seed

The original finite support-to-ambient cone descent preserves every time of the prescribed
localization null under the unchanged seed transitions. Its genuine signed cone sequences
therefore form the actual five-term diagram. Ambient connective invertibility and coarse-open
positive invertibility with honest zero-degree injectivity prove the original supported seed
invertible in every nonnegative degree. No ambient forget injectivity, full-open K-zero
surjectivity, geometric unit-boundary identification, or replacement seed is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The actual original supported and ambient seed transitions form their unchanged arrow square.
-/
def boundedFlatCoefficientSupportedBassTransitionSquare (i : ℕ) (a : Under R) :
    Arrow.mk ((boundedFlatCoefficientSupportedBassForget f i).app a) ⟶
      Arrow.mk ((boundedFlatCoefficientSupportedBassForget f (i + 1)).app a) :=
  Arrow.homMk ((boundedFlatCoefficientSupportedBassTransition f i).app a)
    ((boundedFlatCoefficientAmbientBassTransition Q i).app a)
    (NatTrans.congr_app (boundedFlatCoefficientSupportedBassForget_transition f i) a).symm

/-- Every prescribed localization-null time gives literal transition naturality of cone descent.
-/
theorem boundedFlatCoefficientSupportedBassOpenConeMap_transition (i : ℕ) (a : Under R) :
    mappingConeMap (boundedFlatCoefficientSupportedBassTransitionSquare f i a) ≫
        (boundedFlatCoefficientSupportedBassOpenConeMap f (i + 1)).app a =
      (boundedFlatCoefficientSupportedBassOpenConeMap f i).app a ≫
        (boundedFlatCoefficientOpenBassTransition f i).app a := by
  apply mappingConeDesc_naturality (boundedFlatCoefficientSupportedBassTransitionSquare f i a)
    ((boundedFlatCoefficientAmbientBassOpen f i).app a)
    ((boundedFlatCoefficientAmbientBassOpen f (i + 1)).app a)
    ((boundedFlatCoefficientOpenBassTransition f i).app a)
    ((boundedFlatCoefficientSupportedBassOpenNull f i).homotopy a)
    ((boundedFlatCoefficientSupportedBassOpenNull f (i + 1)).homotopy a)
  · exact (NatTrans.congr_app (boundedFlatCoefficientAmbientBassOpen_transition f i) a).symm
  · exact boundedFlatCoefficientSupportedBassOpenNull_transition f i a

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The original cone transition is invertible in positive degrees through its actual descents.
-/
theorem boundedFlatCoefficientSupportedBassConeTransition_zero_positive_isIso
    (a : Under R) (d : ℤ) (hd : 0 < d) :
    IsIso ((stableHomotopyFunctor d).map
      (mappingConeMap (boundedFlatCoefficientSupportedBassTransitionSquare f 0 a))) := by
  let e₀ := (boundedFlatCoefficientSupportedBassOpenConeMap f 0).app a
  let e₁ := (boundedFlatCoefficientSupportedBassOpenConeMap f 1).app a
  let c := mappingConeMap (boundedFlatCoefficientSupportedBassTransitionSquare f 0 a)
  let τC := (boundedFlatCoefficientOpenBassTransition f 0).app a
  let : IsIso ((stableHomotopyFunctor d).map e₀) :=
    boundedFlatCoefficientSupportedBassOpenConeMap_isStableEquivalence f 0 a d
  let : IsIso ((stableHomotopyFunctor d).map e₁) :=
    boundedFlatCoefficientSupportedBassOpenConeMap_isStableEquivalence f 1 a d
  let : IsIso ((stableHomotopyFunctor d).map τC) :=
    boundedFlatCoefficientOpenBassTransition_zero_positive_isIso f a d hd
  have he := congrArg ((stableHomotopyFunctor d).map)
    (boundedFlatCoefficientSupportedBassOpenConeMap_transition f 0 a)
  change (stableHomotopyFunctor d).map (c ≫ e₁) =
    (stableHomotopyFunctor d).map (e₀ ≫ τC) at he
  simp only [Functor.map_comp] at he
  let : IsIso ((stableHomotopyFunctor d).map c ≫ (stableHomotopyFunctor d).map e₁) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((stableHomotopyFunctor d).map e₁)

/-- At degree zero only the honest coarse injectivity is needed for the original cone transition.
-/
theorem boundedFlatCoefficientSupportedBassConeTransition_zero_stable_zero_injective
    (a : Under R) :
    Function.Injective ((stableHomotopyFunctor 0).map
      (mappingConeMap (boundedFlatCoefficientSupportedBassTransitionSquare f 0 a))) := by
  let e₀ := (boundedFlatCoefficientSupportedBassOpenConeMap f 0).app a
  let e₁ := (boundedFlatCoefficientSupportedBassOpenConeMap f 1).app a
  let c := mappingConeMap (boundedFlatCoefficientSupportedBassTransitionSquare f 0 a)
  let τC := (boundedFlatCoefficientOpenBassTransition f 0).app a
  let : IsIso ((stableHomotopyFunctor 0).map e₀) :=
    boundedFlatCoefficientSupportedBassOpenConeMap_isStableEquivalence f 0 a 0
  have he := congrArg ((stableHomotopyFunctor 0).map)
    (boundedFlatCoefficientSupportedBassOpenConeMap_transition f 0 a)
  change (stableHomotopyFunctor 0).map (c ≫ e₁) =
    (stableHomotopyFunctor 0).map (e₀ ≫ τC) at he
  simp only [Functor.map_comp] at he
  intro x y h
  apply (ConcreteCategory.bijective_of_isIso ((stableHomotopyFunctor 0).map e₀)).injective
  apply boundedFlatCoefficientOpenBassTransition_zero_stable_zero_injective f a
  exact (ConcreteCategory.congr_hom he x).symm.trans
    ((congrArg ((stableHomotopyFunctor 0).map e₁) h).trans
      (ConcreteCategory.congr_hom he y))

/-- The actual original supported stage-zero transition is invertible in every connective degree.
-/
instance boundedFlatCoefficientSupportedBassTransition_zero_connective_isIso
    (a : Under R) (n : ℕ) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedFlatCoefficientSupportedBassTransition f 0).app a)) := by
  apply left_stableMap_isIso_of_coneMap
    (boundedFlatCoefficientSupportedBassTransitionSquare f 0 a)
    (boundedFlatCoefficientSupportedBassForget_coneFiber_isStableEquivalence f 0 a)
    (boundedFlatCoefficientSupportedBassForget_coneFiber_isStableEquivalence f 1 a) (n : ℤ)
  · have he : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
    rw [he]
    exact (ConcreteCategory.bijective_of_isIso
      ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
        ((boundedFlatCoefficientAmbientBassTransition Q 0).app a))).surjective
  · exact (ConcreteCategory.isIso_iff_bijective _).mp
      (boundedFlatCoefficientSupportedBassConeTransition_zero_positive_isIso f a
        ((n : ℤ) + 1) (by omega))
  · exact ConcreteCategory.bijective_of_isIso
      ((stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientAmbientBassTransition Q 0).app a))
  · cases n with
    | zero => exact boundedFlatCoefficientSupportedBassConeTransition_zero_stable_zero_injective f a
    | succ n => exact ((ConcreteCategory.isIso_iff_bijective _).mp
        (boundedFlatCoefficientSupportedBassConeTransition_zero_positive_isIso f a
          ((n + 1 : ℕ) : ℤ) (by omega))).injective

end Quillen.PerfectComplexes
