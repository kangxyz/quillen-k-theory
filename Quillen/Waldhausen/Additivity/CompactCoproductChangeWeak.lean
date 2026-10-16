/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.CompactCoproductCube
public import Quillen.Waldhausen.Fibration.CanonicalFiberMap

/-! # Literal compact coproducts under the original change of weak equivalences

The product comparison and normalized coproduct commute with the original change-weak map.
This owner retains exact original cubes before the separate whole unit/separation comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open scoped Topology Simplicial unitInterval
universe u v
namespace Quillen.Waldhausen.Additivity
open ExtensionCategory Fibration
variable {C : Type u} [Category.{v} C] (W : Structure C) (N : NestedWeakEquivalences W)

/-- The actual componentwise enlargement retains the original product cofibrations and zero. -/
def coproductProductNested : NestedWeakEquivalences (productStructure W W) where
  coarse := productStructure N.coarse N.coarse
  cof_eq := congrArg₂ MorphismProperty.prod N.cof_eq N.cof_eq
  zero_eq := congrArg₂ Prod.mk N.zero_eq N.zero_eq
  le_weq _ _ _ h := ⟨N.le_weq _ h.1, N.le_weq _ h.2⟩

/-- Both original product projections commute with the unchanged identity exact functor. -/
theorem coproductProductComparison_changeWeak (x : (productStructure W W).Delooping) :
    Product.deloopingComparison N.coarse N.coarse
      (changeWeakMap (coproductProductNested W N) x) =
        (changeWeakMap N (Product.deloopingComparison W W x).1,
          changeWeakMap N (Product.deloopingComparison W W x).2) := by
  have hf : deloopingMap (changeWeak_exact (coproductProductNested W N)) ≫
      deloopingMap (fst_exact N.coarse N.coarse) =
        deloopingMap (fst_exact W W) ≫ deloopingMap (changeWeak_exact N) := by
    rw [deloopingMap_comp_deloopingMap, deloopingMap_comp_deloopingMap]
  have hg : deloopingMap (changeWeak_exact (coproductProductNested W N)) ≫
      deloopingMap (snd_exact N.coarse N.coarse) =
        deloopingMap (snd_exact W W) ≫ deloopingMap (changeWeak_exact N) := by
    rw [deloopingMap_comp_deloopingMap, deloopingMap_comp_deloopingMap]
  exact Prod.ext (ConcreteCategory.congr_hom hf x) (ConcreteCategory.congr_hom hg x)

variable (n : ℕ)

/-- The original change-weak map on the unchanged positive-dimensional cubes. -/
def coproductChangeWeakCubeMap :
    C(GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint,
      GenLoop (Fin (n + 1)) N.coarse.Delooping N.coarse.kBasepoint) :=
  genLoopPostcompContinuousMap (changeWeakMap N) (changeWeakMap_basepoint N)

/-- Coarse projection injectivity recovers the whole original product lift. -/
theorem productCubeLift_changeWeak
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    genLoopPostcomp (changeWeakMap (coproductProductNested W N))
      (changeWeakMap_basepoint (coproductProductNested W N)) (productCubeLift W n p q) =
        productCubeLift N.coarse n (coproductChangeWeakCubeMap W N n p)
          (coproductChangeWeakCubeMap W N n q) := by
  apply productCubeLift_unique
  intro z
  change Product.deloopingComparison N.coarse N.coarse
    (changeWeakMap (coproductProductNested W N) (productCubeLift W n p q z)) = _
  rw [coproductProductComparison_changeWeak, productCubeLift_projection]
  rfl

variable [HasBinaryCoproducts C]

/-- The actual canonical coproduct rebasing is unchanged under the same chosen-zero transport. -/
theorem coproductBasedMap_changeWeak (x : (productStructure W W).Delooping) :
    changeWeakMap N (coproductBasedMap W x) =
      coproductBasedMap N.coarse (changeWeakMap (coproductProductNested W N) x) := by
  have h : deloopingMap (coproductFunctor_isExact W).rebase ≫
      deloopingMap (changeWeak_exact N) =
        deloopingMap (changeWeak_exact (coproductProductNested W N)) ≫
          deloopingMap (coproductFunctor_isExact N.coarse).rebase := by
    rw [deloopingMap_comp_deloopingMap, deloopingMap_comp_deloopingMap]
    cases W
    rcases N with ⟨coarse, hcof, hzero, hw⟩
    cases coarse
    cases hzero
    rfl
  exact ConcreteCategory.congr_hom h x

/-- The complete compact coproduct cube commutes with the original change-weak map. -/
theorem coproductCube_changeWeak
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    coproductChangeWeakCubeMap W N n (coproductCube W n p q) =
      coproductCube N.coarse n (coproductChangeWeakCubeMap W N n p)
        (coproductChangeWeakCubeMap W N n q) := by
  apply GenLoop.ext
  intro z
  change changeWeakMap N (coproductBasedMap W (productCubeLift W n p q z)) = _
  rw [coproductBasedMap_changeWeak]
  exact congrArg (fun a ↦ coproductBasedMap N.coarse (a z))
    (productCubeLift_changeWeak W N n p q)

end Quillen.Waldhausen.Additivity
