/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Field.SteinbergFiberSurjectivity
public import Quillen.KTheory.Plus.StableFiberPerfectness
public import Quillen.KTheory.Field.SteinbergFiberTransgression
public import Quillen.Topology.HomotopyFiber.CommutingSquareCapping

/-!
# Injectivity of the original Steinberg maps over every field

The original chains, signs, maps, basepoints and stated hypotheses are retained.
-/
@[expose] public section

section

open groupHomology.IntegralBar
open Quillen.StableSteinberg.Schur
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
namespace Quillen.FiniteProjectiveModule.StableCompletion
variable (F : Type u) [Field F]

/-- Accepted actual fiber perfectness discharges the existing surjectivity premise. -/
theorem actual_steinberg_surjective : Function.Surjective (steinbergToStableFiber F) := by
  let := stableFiberPiOne_isPerfect F
  exact steinbergToStableFiber_surjective F

/-- The original positive comparison and basepoint path retain exactly the same kernel
injectivity problem as the original lift between the two central extensions. -/
theorem steinberg_injective_iff_originalKTwo_injective :
    Function.Injective (steinbergToStableFiber F) ↔
      Function.Injective (steinbergKernelToRightProjectiveKTwo F) := by
  constructor
  · intro hu a b hab
    apply Subtype.ext
    apply hu
    have h₁ := (zeroCompletionPositiveKEquiv F 1).injective hab
    have h₂ := (pathTransportMulEquiv (basepointPath F) 1).injective h₁
    have h₃ := (imagePiTwoFiberKernelEquiv F).symm.injective h₂
    exact congrArg Subtype.val h₃
  · intro hk
    apply (steinbergToStableFiber F).ker_eq_bot_iff.mp
    apply le_antisymm _ bot_le
    intro a ha
    have hu : steinbergToStableFiber F a = 1 := ha
    have he : StableSteinberg.toElementary F a = 1 := by
      rw [← steinbergToStableFiber_over]
      change stableFiberToElementary F (steinbergToStableFiber F a) = 1
      rw [hu, map_one]
    let b : (StableSteinberg.toElementary F).ker := ⟨a, he⟩
    have hb : steinbergKernelToFiberKernel F b = 1 := Subtype.ext hu
    have hb' : steinbergKernelToRightProjectiveKTwo F b = 1 := by
      change zeroCompletionPositiveKEquiv F 1
        (pathTransportMulEquiv (basepointPath F) 1
          ((imagePiTwoFiberKernelEquiv F).symm (steinbergKernelToFiberKernel F b))) = 1
      rw [hb, map_one, map_one, map_one]
    have hbone : b = 1 := hk (hb'.trans (map_one (steinbergKernelToRightProjectiveKTwo F)).symm)
    exact congrArg Subtype.val hbone

end Quillen.FiniteProjectiveModule.StableCompletion

end

section

open groupHomology.IntegralBar
open Quillen.StableSteinberg.Schur
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
open scoped commutatorElement
namespace Quillen.FiniteProjectiveModule.StableCompletion
open LocalCoefficients groupHomology.IntegralBar Quillen.StableSteinberg.Schur
open HomotopyFiber.PeriodicConnecting HomotopyFiber.CommutingSquareCapping
variable (F : Type u) [Field F] {T : Type (u + 1)} [TopologicalSpace T]
  (q : C(T, ZeroComponent F)) (e : T) (he : q e = stableZeroMap F (stableBase F))
  (hq : IsCoveringMap q) [SimplyConnectedSpace T]

/-- Constructed capping data prove agreement of the original detector and Schur map on every
original ordered torus defect. No geometric existence or transgression law is a hypothesis. -/
theorem originalKTwoToIntegerBar_torus (a b : Fˣ) :
    originalKTwoToIntegerBar F q e he hq
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b)) =
        stablePullbackIntegerSchurEquiv F q e he hq (StableSteinberg.torusDefectKernel a b) := by
  let z := stableZeroCoverPoint F q e he
  let k := Covering.Pullback.lift (stableZeroMap F) q
  let E := coverElementaryEquiv F q e he hq
  let g := E.symm (StableSteinberg.toElementary F (StableSteinberg.h a))
  let h := E.symm (StableSteinberg.toElementary F (StableSteinberg.h02 b))
  have hgh : Commute g h :=
    (elementary_torus_commute F a b).map E.symm.toMonoidHom
  obtain ⟨A, B, hArep, hBrep, hAB⟩ := exists_commuting_loop_representatives g h hgh
  let σ := sourceSquare A B hAB
  let β := targetCube A B hAB k
  let H₀ := wholeHomotopy A B hAB k
  have hsquare : basedSquare β = cubeSquare e β := by
    ext w
    apply congrArg β
    funext i
    fin_cases i <;> rfl
  let H : (k.comp σ).Homotopy (cubeSquare e β) := {
    toContinuousMap := H₀.toContinuousMap
    map_zero_left := H₀.apply_zero
    map_one_left := fun w => (H₀.apply_one w).trans
      (congrArg (fun f : C(unitInterval × unitInterval, T) => f w) hsquare) }
  have hx : σ (0, 0) = z := sourceSquare_vertex A B hAB
  have hσ₁ : ∀ t, σ (0, t) = σ (1, t) := (sourceSquare_periodic A B hAB).1
  have hσ₂ : ∀ t, σ (t, 0) = σ (t, 1) := (sourceSquare_periodic A B hAB).2
  have hH₁ : ∀ s t, H (s, (0, t)) = H (s, (1, t)) :=
    (wholeHomotopy_periodic A B hAB k).1
  have hH₂ : ∀ s t, H (s, (t, 0)) = H (s, (t, 1)) :=
    (wholeHomotopy_periodic A B hAB k).2
  have hA : E (piMap 0 (ContinuousMap.id _) hx (SingularBar.firstAxisClass σ hσ₁)) =
      StableSteinberg.toElementary F (StableSteinberg.h a) := by
    exact (congrArg E (firstAxisClass_at_of_edge σ hσ₁ hx A
      (sourceSquare_zero_second A B hAB))).trans
        ((congrArg E hArep).trans (E.apply_symm_apply _))
  have hB : E (piMap 0 (ContinuousMap.id _) hx (SingularBar.secondAxisClass σ hσ₂)) =
      StableSteinberg.toElementary F (StableSteinberg.h02 b) := by
    exact (congrArg E (secondAxisClass_at_of_edge σ hσ₂ hx B
      (sourceSquare_zero_first A B hAB))).trans
        ((congrArg E hBrep).trans (E.apply_symm_apply _))
  exact originalKTwoToIntegerBar_periodic F q e he hq a b σ β H hx
    hσ₁ hσ₂ hH₁ hH₂ hA hB

/-- The constructed detector is a left inverse to the ORIGINAL kernel-to-Quillen-K-two map. -/
theorem originalKTwoSchurDetector_left_inverse :
    (originalKTwoSchurDetector F q e he hq).comp (steinbergKernelToRightProjectiveKTwo F) =
      MonoidHom.id (StableSteinberg.toElementary F).ker := by
  apply kernelHom_ext_torusDefect F
  intro a b
  change (stablePullbackIntegerSchurEquiv F q e he hq).symm
    (originalKTwoToIntegerBar F q e he hq
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b))) =
        StableSteinberg.torusDefectKernel a b
  rw [originalKTwoToIntegerBar_torus, MulEquiv.symm_apply_apply]

include q e he hq in
/-- Any supplied actual simply connected cover gives injectivity of the original comparison. -/
theorem originalKTwoComparison_injective_with_cover :
    Function.Injective (steinbergKernelToRightProjectiveKTwo F) := by
  have hl : Function.LeftInverse (originalKTwoSchurDetector F q e he hq)
      (steinbergKernelToRightProjectiveKTwo F) := by
    intro a
    exact congrArg (fun k => k a) (originalKTwoSchurDetector_left_inverse F q e he hq)
  exact hl.injective

end Quillen.FiniteProjectiveModule.StableCompletion

namespace Quillen.FiniteProjectiveModule.StableCompletion
variable (F : Type u) [Field F]

/-- The ORIGINAL Steinberg-kernel-to-right-projective K-two map is injective over every field.
The actual simply connected cover and all chain/geometric comparison data are constructed. -/
theorem originalKTwoComparison_injective :
    Function.Injective (steinbergKernelToRightProjectiveKTwo F) := by
  obtain ⟨T, t, hcover⟩ := exists_stableZeroCover_homologicalSetup F
  let := t
  obtain ⟨q, e, he, hq, _, hSC, _⟩ := hcover
  let := hSC
  exact originalKTwoComparison_injective_with_cover F q e he hq

/-- The existing ORIGINAL stable Steinberg-to-completion-fiber map is injective. -/
theorem actual_steinberg_injective : Function.Injective (steinbergToStableFiber F) :=
  (steinberg_injective_iff_originalKTwo_injective F).mpr (originalKTwoComparison_injective F)

/-- The existing ORIGINAL stable Steinberg-to-completion-fiber map is bijective. -/
theorem actual_steinberg_bijective : Function.Bijective (steinbergToStableFiber F) :=
  ⟨actual_steinberg_injective F, actual_steinberg_surjective F⟩

end Quillen.FiniteProjectiveModule.StableCompletion

end

namespace Quillen.FiniteProjectiveModule.StableCompletion
universe u
variable (F : Type u) [Field F]

/-- The original kernel-to-right-projective K2 map is injective over every field. -/
theorem steinbergKernelToRightProjectiveKTwo_injective :
    Function.Injective (steinbergKernelToRightProjectiveKTwo F) :=
  originalKTwoComparison_injective F

/-- The original Steinberg-to-stable-fiber map is injective over every field. -/
theorem steinbergToStableFiber_injective : Function.Injective (steinbergToStableFiber F) :=
  actual_steinberg_injective F

/-- The original Steinberg-to-stable-fiber map is bijective over every field. -/
theorem steinbergToStableFiber_bijective : Function.Bijective (steinbergToStableFiber F) :=
  actual_steinberg_bijective F

end Quillen.FiniteProjectiveModule.StableCompletion
