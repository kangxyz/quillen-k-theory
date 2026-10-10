/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HELP.CompactRealizationLifting

/-! Every actual simplicial monomorphism realizes to a map with the homotopy
extension property, by the proved relative cell lifting theorem. -/
@[expose] public section

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial Topology unitInterval
namespace Quillen.TheoremA

/-- Evaluation at the initial endpoint of the compact-open path space. -/
def pathEvaluationZero (Z : TopCat.{u}) : TopCat.of C(unitInterval,Z) ⟶ Z :=
  TopCat.ofHom ⟨fun γ ↦ γ 0, by fun_prop⟩

/-- HEP is exactly enough to lift a square against path evaluation. -/
theorem pathEvaluationZero_hasLiftingProperty {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : homotopyExtensionProperty i) (Z : TopCat.{u}) :
    HasLiftingProperty i (pathEvaluationZero Z) where
  sq_hasLift {a b} sq := by
    let H : C(unitInterval × A,Z) := ⟨fun z ↦ a z.2 z.1, by fun_prop⟩
    obtain ⟨K,hK₀,hKA⟩ := homotopyExtensionProperty_continuous hi Z b.hom H
      (fun x ↦ ConcreteCategory.congr_hom sq.w x)
    let l : B ⟶ TopCat.of C(unitInterval,Z) := TopCat.ofHom {
      toFun x := ⟨fun t ↦ K (t,x), by fun_prop⟩
      continuous_toFun := by
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact K.continuous.comp continuous_swap }
    refine ⟨l,?_,?_⟩
    · apply ConcreteCategory.hom_ext
      intro x
      apply ContinuousMap.ext
      intro t
      exact hKA t x
    · apply ConcreteCategory.hom_ext
      intro x
      exact hK₀ x

/-- Actual realization takes every simplicial mono to a genuine HEP map.
No extra compactness of the whole source or target realization is needed. -/
theorem homotopyExtensionProperty_realization_mono {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] : homotopyExtensionProperty (SSet.toTop.map i) := by
  intro Z f H hzero
  let a : |A| ⟶ TopCat.of C(unitInterval,Z) := TopCat.ofHom {
    toFun x := ⟨fun t ↦ H (x, ULift.up t),
      H.hom.continuous.comp (continuous_const.prodMk continuous_uliftUp)⟩
    continuous_toFun := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : |A| × unitInterval ↦ H (z.1,ULift.up z.2))
      exact H.hom.continuous.comp
        (continuous_fst.prodMk (continuous_uliftUp.comp continuous_snd)) }
  let : HasLiftingProperty (SSet.toTop.map i) (pathEvaluationZero Z) :=
    Quillen.hasLiftingProperty_realization_mono (pathEvaluationZero Z)
      (fun n ↦ pathEvaluationZero_hasLiftingProperty _
        (homotopyExtensionProperty_realizationBoundary n) Z) i
  have sq : CommSq a (SSet.toTop.map i) (pathEvaluationZero Z) f := by
    constructor
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom hzero x
  let l := sq.lift
  let K : |B| ⊗ TopCat.I ⟶ Z := TopCat.ofHom ⟨fun z ↦ l z.1 z.2.down, by fun_prop⟩
  refine ⟨K,?_,?_⟩
  · apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom sq.fac_right x
  · apply ConcreteCategory.hom_ext
    rintro ⟨x,t⟩
    exact ContinuousMap.congr_fun (ConcreteCategory.congr_hom sq.fac_left x) t.down

end Quillen.TheoremA
