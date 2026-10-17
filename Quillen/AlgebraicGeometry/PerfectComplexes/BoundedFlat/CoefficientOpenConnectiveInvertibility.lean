/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientGradedOpenBassPositiveVanishing
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassFineConnectiveInvertibility
public import Quillen.Topology.Prespectrum.ConeStableRangeDetection

/-!
# The original coarse open seed in its connective comparison range

The actual first graded Bass stage vanishes only in positive degrees. The original restriction
cone sequence therefore compares first-stage coarse and full-open groups in positive degrees.
The unchanged restriction/seed square gives positive invertibility of the coarse seed and only
injectivity in degree zero. No full-open zero-degree surjectivity is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The unchanged first coarse restriction is invertible in positive degrees. -/
theorem boundedFlatCoefficientOpenBassRestriction_one_positive_isIso
    (a : Under R) (d : ℤ) (hd : 0 < d) :
    IsIso ((stableHomotopyFunctor d).map
      ((boundedFlatCoefficientOpenBassRestriction f 1).app a)) := by
  have hz (k : ℤ) (hk : 0 < k) : Subsingleton (stableHomotopyGroup
      (mappingCone ((boundedFlatCoefficientOpenBassRestriction f 1).app a)) k) := by
    let : Subsingleton ((stableHomotopyFunctor k).obj
        ((boundedFlatCoefficientGradedOpenBassDiagram f 1).obj a)) :=
      boundedFlatCoefficientGradedOpenBass_one_positive_subsingleton f a k hk
    let : IsIso ((stableHomotopyFunctor k).map
        ((boundedFlatCoefficientOpenBassConeComparison f 1).app a)) :=
      boundedFlatCoefficientOpenBassConeComparison_isStableEquivalence f 1 a k
    exact (ConcreteCategory.bijective_of_isIso
      ((stableHomotopyFunctor k).map
        ((boundedFlatCoefficientOpenBassConeComparison f 1).app a))).injective.subsingleton
  exact stableMap_isIso_of_cone_subsingleton _
    (boundedFlatCoefficientOpenBassRestriction_coneFiber_isStableEquivalence f 1 a)
    d (hz d hd) (hz (d + 1) (by omega))

/-- The full-open row retains precisely the proved fine seed of its original open scheme. -/
instance boundedFlatCoefficientFullOpenBassTransition_zero_connective_isIso
    (a : Under R) (n : ℕ) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedFlatCoefficientFullOpenBassTransition f 0).app a)) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  exact boundedFlatCoefficientFullOpenBassSeedMap_connective_isIso P a n

/-- The actual coarse-open stage-zero seed is invertible in each positive degree. -/
theorem boundedFlatCoefficientOpenBassTransition_zero_positive_isIso
    (a : Under R) (d : ℤ) (hd : 0 < d) :
    IsIso ((stableHomotopyFunctor d).map
      ((boundedFlatCoefficientOpenBassTransition f 0).app a)) := by
  let r₀ := (boundedFlatCoefficientOpenBassRestriction f 0).app a
  let r₁ := (boundedFlatCoefficientOpenBassRestriction f 1).app a
  let τC := (boundedFlatCoefficientOpenBassTransition f 0).app a
  let τF := (boundedFlatCoefficientFullOpenBassTransition f 0).app a
  let : IsIso ((stableHomotopyFunctor d).map r₀) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨boundedFlatCoefficientOpenRestriction_stable_injective f a d,
        boundedFlatCoefficientOpenRestriction_stable_surjective_of_ne_zero f a d (ne_of_gt hd)⟩
  let : IsIso ((stableHomotopyFunctor d).map r₁) :=
    boundedFlatCoefficientOpenBassRestriction_one_positive_isIso f a d hd
  let : IsIso ((stableHomotopyFunctor d).map τF) := by
    have he : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (le_of_lt hd)
    rw [← he]
    exact boundedFlatCoefficientFullOpenBassTransition_zero_connective_isIso f a d.toNat
  have hs : r₀ ≫ τF = τC ≫ r₁ :=
    NatTrans.congr_app (boundedFlatCoefficientOpenBassRestriction_transition f 0) a
  have he := congrArg ((stableHomotopyFunctor d).map) hs
  simp only [Functor.map_comp] at he
  let : IsIso ((stableHomotopyFunctor d).map τC ≫ (stableHomotopyFunctor d).map r₁) := by
    rw [← he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((stableHomotopyFunctor d).map r₁)

/-- Zero-degree coarse seed injectivity uses the honest original restriction image only. -/
theorem boundedFlatCoefficientOpenBassTransition_zero_stable_zero_injective (a : Under R) :
    Function.Injective ((stableHomotopyFunctor 0).map
      ((boundedFlatCoefficientOpenBassTransition f 0).app a)) := by
  let r₀ := (boundedFlatCoefficientOpenBassRestriction f 0).app a
  let r₁ := (boundedFlatCoefficientOpenBassRestriction f 1).app a
  let τC := (boundedFlatCoefficientOpenBassTransition f 0).app a
  let τF := (boundedFlatCoefficientFullOpenBassTransition f 0).app a
  let : IsIso ((stableHomotopyFunctor 0).map τF) :=
    boundedFlatCoefficientFullOpenBassTransition_zero_connective_isIso f a 0
  have hs : r₀ ≫ τF = τC ≫ r₁ :=
    NatTrans.congr_app (boundedFlatCoefficientOpenBassRestriction_transition f 0) a
  have he := congrArg ((stableHomotopyFunctor 0).map) hs
  simp only [Functor.map_comp] at he
  intro x y h
  apply boundedFlatCoefficientOpenRestriction_stable_injective f a 0
  apply (ConcreteCategory.bijective_of_isIso ((stableHomotopyFunctor 0).map τF)).injective
  exact (ConcreteCategory.congr_hom he x).trans
    ((congrArg ((stableHomotopyFunctor 0).map r₁) h).trans
      (ConcreteCategory.congr_hom he y).symm)

end Quillen.PerfectComplexes
