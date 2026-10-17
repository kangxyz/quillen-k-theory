/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeEvaluation
public import Quillen.Topology.Realization.DoubleCylinderSimplexCoverage
public import Quillen.Topology.Realization.CompactFamilyContinuity

/-! Compact joint continuity on the exact four-edge reference tree. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
open CutOpenCarrier Quillen.NativePathCells

namespace SetDescent

/-- A displayed cylinder retains joint compact continuity after its set-level descent. -/
theorem value_compact_continuous {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) {A B : Type u}
    [TopologicalSpace A] [TopologicalSpace B]
    (l : |Y| → A → B) (r : |Z| → A → B)
    (c : |X| × TopCat.I.{u} → A → B)
    (h0 : ∀ x, c (x, ULift.up 0) = l (SSet.toTop.map f x))
    (h1 : ∀ x, c (x, ULift.up 1) = r (SSet.toTop.map g x))
    (hl : ∀ {S : Type u} [TopologicalSpace S] [CompactSpace S] (p : C(S, |Y|)),
      Continuous (fun z : S × A ↦ l (p z.1) z.2))
    (hr : ∀ {S : Type u} [TopologicalSpace S] [CompactSpace S] (p : C(S, |Z|)),
      Continuous (fun z : S × A ↦ r (p z.1) z.2))
    (hc : ∀ {S : Type u} [TopologicalSpace S] [CompactSpace S]
      (p : C(S, |X| × TopCat.I.{u})),
      Continuous (fun z : S × A ↦ c (p z.1) z.2))
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |DoubleCylinder.simplicial f g|)) :
    Continuous (fun z : S × A ↦ value f g l r c h0 h1 (p z.1) z.2) := by
  apply Quillen.realization_compactFamily_continuous
    (DoubleCylinder.simplicial f g)
    (fun z ↦ value f g l r c h0 h1 z.1 z.2) _ p
  intro k simplexMap
  rcases DoubleCylinder.characteristicSimplex_factors f g ⦋k⦌ simplexMap with
    ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
  · rw [← hq, Functor.map_comp]
    let q' : C(|(Δ[k] : SSet.{u})|, |X| × TopCat.I.{u}) :=
      (realizationCylinderIso X).hom.hom.comp (SSet.toTop.map q).hom
    apply (hc q').congr
    intro z
    have hh : (realizationCylinderIso X).hom ≫ DoubleCylinder.realizedCylinder f g =
        SSet.toTop.map (DoubleCylinder.simplicialCylinder f g) := by
      simp [DoubleCylinder.realizedCylinder]
    have hv := congrFun (value_cylinder f g l r c h0 h1 (q' z.1)) z.2
    rw [show DoubleCylinder.realizedCylinder f g (q' z.1) =
      SSet.toTop.map (DoubleCylinder.simplicialCylinder f g)
        (SSet.toTop.map q z.1) from
          ConcreteCategory.congr_hom hh (SSet.toTop.map q z.1)] at hv
    exact hv.symm
  · have hq' : q ≫ left f g = simplexMap := hq
    rw [← hq', Functor.map_comp]
    apply (hl (SSet.toTop.map q).hom).congr
    intro z
    exact (congrFun (value_left f g l r c h0 h1 (SSet.toTop.map q z.1)) z.2).symm
  · have hq' : q ≫ right f g = simplexMap := hq
    rw [← hq', Functor.map_comp]
    apply (hr (SSet.toTop.map q).hom).congr
    intro z
    exact (congrFun (value_right f g l r c h0 h1 (SSet.toTop.map q z.1)) z.2).symm

end SetDescent

variable {V W T : Model.{u}} (E : V ⟶ W) (J : W ⟶ T)

/-- Arbitrary compact coefficient parameters retain the whole original native input. -/
theorem nativeCylinder_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |parameterSSet E|)) (c : C(S, I)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      nativeCylinder E J n (p z.1) (c z.1) z.2) :=
  (LoopPrespectrum.HomotopyPushout.cylinder (prespectrumMap J) (prespectrumMap J) n).continuous.comp
    ((c.continuous.comp continuous_fst).prodMk
      (pointwisePrespectrumFamily_compact_continuous E p n))

theorem nativePlus_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |parameterSSet (E ≫ J)|)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦ nativePlus E J n (p z.1) z.2) :=
  (LoopPrespectrum.HomotopyPushout.left (prespectrumMap J) (prespectrumMap J) n).continuous.comp
    (pointwisePrespectrumFamily_compact_continuous (E ≫ J) p n)

theorem nativeMinus_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |parameterSSet (E ≫ J)|)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦ nativeMinus E J n (p z.1) z.2) :=
  (LoopPrespectrum.HomotopyPushout.right (prespectrumMap J) (prespectrumMap J) n).continuous.comp
    (pointwisePrespectrumFamily_compact_continuous (E ≫ J) p n)

private theorem nativeCell_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |parameterSSet E| × TopCat.I.{u})) (c : C(I, I)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      nativeCylinder E J n (p z.1).1 (c (p z.1).2.down) z.2) :=
  nativeCylinder_compact_continuous E J
    ⟨fun s ↦ (p s).1, continuous_fst.comp p.continuous⟩
    ⟨fun s ↦ c (p s).2.down,
      c.continuous.comp (continuous_uliftDown.comp (continuous_snd.comp p.continuous))⟩ n

/-- Compact joint continuity is preserved by the first displayed reference cylinder. -/
theorem firstNativeEval_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |first E J|)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦ firstNativeEval E J n (p z.1) z.2) := by
  unfold firstNativeEval
  apply SetDescent.value_compact_continuous
  · intro S _ _ p
    exact nativeCylinder_compact_continuous E J p (ContinuousMap.const S (time12 0)) n
  · intro S _ _ p
    exact nativePlus_compact_continuous E J p n
  · intro S _ _ p
    exact nativeCell_compact_continuous E J p ⟨time12, by unfold time12; fun_prop⟩ n

/-- The second cylinder keeps the already descended positive branch unchanged. -/
theorem secondNativeEval_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |second E J|)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦ secondNativeEval E J n (p z.1) z.2) := by
  unfold secondNativeEval
  apply SetDescent.value_compact_continuous
  · intro S _ _ p
    exact nativeCylinder_compact_continuous E J p (ContinuousMap.const S (time01 0)) n
  · intro S _ _ p
    exact firstNativeEval_compact_continuous E J p n
  · intro S _ _ p
    exact nativeCell_compact_continuous E J p ⟨time01, by unfold time01; fun_prop⟩ n

/-- The third cylinder retains the distinct inverse-chart branch. -/
theorem thirdNativeEval_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |third E J|)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦ thirdNativeEval E J n (p z.1) z.2) := by
  unfold thirdNativeEval
  apply SetDescent.value_compact_continuous
  · intro S _ _ p
    exact secondNativeEval_compact_continuous E J p n
  · intro S _ _ p
    exact nativeCylinder_compact_continuous E J p (ContinuousMap.const S (time03 1)) n
  · intro S _ _ p
    exact nativeCell_compact_continuous E J p ⟨time03, by unfold time03; fun_prop⟩ n

/-- The exact whole tree evaluator is jointly continuous after any compact parameter. -/
theorem nativeEval_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, space E J)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦ nativeEval E J n (p z.1) z.2) := by
  unfold nativeEval
  apply SetDescent.value_compact_continuous
  · intro S _ _ p
    exact thirdNativeEval_compact_continuous E J p n
  · intro S _ _ p
    exact nativeMinus_compact_continuous E J p n
  · intro S _ _ p
    exact nativeCell_compact_continuous E J p ⟨time34, by unfold time34; fun_prop⟩ n

/-- One scalar compact parameter gives the original native family at every level. -/
def compactNativeFamily
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, space E J)) (n : ℕ) :
    C(S × (prespectrum V).space n, (nativeSpan J).space n) :=
  ⟨fun z ↦ nativeEval E J n (p z.1) z.2, nativeEval_compact_continuous E J p n⟩

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
