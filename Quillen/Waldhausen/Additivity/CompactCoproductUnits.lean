/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.CompactCoproductCube

/-! # Actual based unit cylinders for the compact coproduct cubes

The two original coproduct-unit isomorphisms are conjugated only by the original canonical
coproduct normalization. Their based realization cylinders give paths of the actual cubes.
The zero-left path uses the second embedding, retaining the quotient-first summand order.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped Topology
universe u v
namespace Quillen.Waldhausen.Additivity
open ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C]

/-- The same canonically rebased coproduct functor used in the original based map. -/
def coproductRebasedFunctor : C × C ⥤ C :=
  Quillen.rebaseFunctor coproductFunctor (productStructure W W).zero W.zero
    (((coproductFunctor_isExact W).zero (productStructure W W).isZero).iso W.isZero)

/-- Exactness uses the original coproduct witness and its actual canonical rebasing. -/
theorem coproductRebasedFunctor_exact :
    IsExact (productStructure W W).cof (productStructure W W).weq W.cof W.weq
      (coproductRebasedFunctor W) := (coproductFunctor_isExact W).rebase

/-- The original coproduct rebasing isomorphism, with its actual chosen-zero component. -/
def coproductRebaseIso : coproductFunctor ≅ coproductRebasedFunctor W :=
  Quillen.rebaseFunctorIso coproductFunctor (productStructure W W).zero W.zero
    (((coproductFunctor_isExact W).zero (productStructure W W).isZero).iso W.isZero)

/-- The normalized coproduct sends the original pair of zeros exactly to the original zero. -/
theorem coproductRebasedFunctor_zero :
    (coproductRebasedFunctor W).obj (W.zero, W.zero) = W.zero :=
  Quillen.rebaseFunctor_obj_base _ _ _ _

/-- Zero on the left uses the actual second coproduct embedding and its original unitor. -/
def coproductLeftUnitIso : secondEmbedding W ⋙ coproductRebasedFunctor W ≅ 𝟭 C :=
  isoWhiskerLeft (secondEmbedding W) (coproductRebaseIso W).symm ≪≫
    secondEmbeddingCoproductIso W

/-- Zero on the right uses the actual first coproduct embedding and its original unitor. -/
def coproductRightUnitIso : firstEmbedding W ⋙ coproductRebasedFunctor W ≅ 𝟭 C :=
  isoWhiskerLeft (firstEmbedding W) (coproductRebaseIso W).symm ≪≫
    firstEmbeddingCoproductIso W

omit [HasBinaryCoproducts C] in
/-- Both original projection maps of the second embedding retain their exact values. -/
theorem deloopingComparison_secondEmbedding (x : W.Delooping) :
    Product.deloopingComparison W W (deloopingMap (secondEmbedding_isExact W) x) =
      (W.kBasepoint, x) := by
  have hf : deloopingMap (secondEmbedding_isExact W) ≫ deloopingMap (fst_exact W W) =
      deloopingMap (zeroFunctor_isExact W W) := by
    rw [deloopingMap_comp_deloopingMap]
  have hg : deloopingMap (secondEmbedding_isExact W) ≫ deloopingMap (snd_exact W W) =
      deloopingMap (IsExact.id W.cof W.weq) := by
    rw [deloopingMap_comp_deloopingMap]
  apply _root_.Prod.ext
  · exact (ConcreteCategory.congr_hom hf x).trans
      (ContinuousMap.congr_fun (deloopingMap_zeroFunctor W W) x)
  · exact (ConcreteCategory.congr_hom hg x).trans
      (ConcreteCategory.congr_hom (deloopingMap_id W) x)

omit [HasBinaryCoproducts C] in
/-- Both original projection maps of the first embedding retain their exact values. -/
theorem deloopingComparison_firstEmbedding (x : W.Delooping) :
    Product.deloopingComparison W W (deloopingMap (firstEmbedding_isExact W) x) =
      (x, W.kBasepoint) := by
  have hf : deloopingMap (firstEmbedding_isExact W) ≫ deloopingMap (fst_exact W W) =
      deloopingMap (IsExact.id W.cof W.weq) := by
    rw [deloopingMap_comp_deloopingMap]
  have hg : deloopingMap (firstEmbedding_isExact W) ≫ deloopingMap (snd_exact W W) =
      deloopingMap (zeroFunctor_isExact W W) := by
    rw [deloopingMap_comp_deloopingMap]
  apply _root_.Prod.ext
  · exact (ConcreteCategory.congr_hom hf x).trans
      (ConcreteCategory.congr_hom (deloopingMap_id W) x)
  · exact (ConcreteCategory.congr_hom hg x).trans
      (ContinuousMap.congr_fun (deloopingMap_zeroFunctor W W) x)

variable (n : ℕ)

omit [HasBinaryCoproducts C] in
/-- Uniqueness recovers the entire original zero-left embedding cube. -/
theorem productCubeLift_zero_left
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    productCubeLift W n GenLoop.const q =
      genLoopPostcomp (deloopingMap (secondEmbedding_isExact W)).hom
        (deloopingMap_basepoint_of_zeroEq (secondEmbedding_isExact W) rfl) q := by
  symm
  exact productCubeLift_unique W n _ _ _ (fun z ↦ deloopingComparison_secondEmbedding W (q z))

omit [HasBinaryCoproducts C] in
/-- Uniqueness recovers the entire original zero-right embedding cube. -/
theorem productCubeLift_zero_right
    (p : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    productCubeLift W n p GenLoop.const =
      genLoopPostcomp (deloopingMap (firstEmbedding_isExact W)).hom
        (deloopingMap_basepoint_of_zeroEq (firstEmbedding_isExact W) rfl) p := by
  symm
  exact productCubeLift_unique W n _ _ _ (fun z ↦ deloopingComparison_firstEmbedding W (p z))

/-- The zero-left compact coproduct is exactly the original composite realization map. -/
theorem coproductCube_zero_left_apply
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (z : Fin (n + 1) → unitInterval) :
    coproductCube W n GenLoop.const q z =
      deloopingMap ((secondEmbedding_isExact W).comp (coproductRebasedFunctor_exact W)) (q z) := by
  rw [coproductCube_apply, productCubeLift_zero_left]
  exact ConcreteCategory.congr_hom
    (deloopingMap_comp_deloopingMap (secondEmbedding_isExact W) (coproductRebasedFunctor_exact W))
    (q z)

/-- The zero-right compact coproduct is exactly the original composite realization map. -/
theorem coproductCube_zero_right_apply
    (p : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (z : Fin (n + 1) → unitInterval) :
    coproductCube W n p GenLoop.const z =
      deloopingMap ((firstEmbedding_isExact W).comp (coproductRebasedFunctor_exact W)) (p z) := by
  rw [coproductCube_apply, productCubeLift_zero_right]
  exact ConcreteCategory.congr_hom
    (deloopingMap_comp_deloopingMap (firstEmbedding_isExact W) (coproductRebasedFunctor_exact W))
    (p z)

/-- The actual normalized zero-left unitor realization cylinder. -/
def coproductLeftUnitHomotopy :
    (deloopingMap ((secondEmbedding_isExact W).comp (coproductRebasedFunctor_exact W))).hom.Homotopy
      (deloopingMap (IsExact.id W.cof W.weq)).hom :=
  weakNaturalTransformationRealizationHomotopy W W
    ((secondEmbedding_isExact W).comp (coproductRebasedFunctor_exact W))
    (IsExact.id W.cof W.weq) (coproductLeftUnitIso W).hom (fun _ ↦ W.weq_iso _ inferInstance)

/-- The actual normalized zero-right unitor realization cylinder. -/
def coproductRightUnitHomotopy :
    (deloopingMap ((firstEmbedding_isExact W).comp (coproductRebasedFunctor_exact W))).hom.Homotopy
      (deloopingMap (IsExact.id W.cof W.weq)).hom :=
  weakNaturalTransformationRealizationHomotopy W W
    ((firstEmbedding_isExact W).comp (coproductRebasedFunctor_exact W))
    (IsExact.id W.cof W.weq) (coproductRightUnitIso W).hom (fun _ ↦ W.weq_iso _ inferInstance)

/-- The entire zero-left unit cylinder is fixed at the actual chosen zero. -/
theorem coproductLeftUnitHomotopy_zero (t : unitInterval) :
    coproductLeftUnitHomotopy W (t, W.kBasepoint) = W.kBasepoint :=
  weakNaturalTransformationRealizationHomotopy_fixed_zero W W
    ((secondEmbedding_isExact W).comp (coproductRebasedFunctor_exact W))
    (IsExact.id W.cof W.weq) (coproductLeftUnitIso W).hom (fun _ ↦ W.weq_iso _ inferInstance)
    (coproductRebasedFunctor_zero W) rfl t

/-- The entire zero-right unit cylinder is fixed at the actual chosen zero. -/
theorem coproductRightUnitHomotopy_zero (t : unitInterval) :
    coproductRightUnitHomotopy W (t, W.kBasepoint) = W.kBasepoint :=
  weakNaturalTransformationRealizationHomotopy_fixed_zero W W
    ((firstEmbedding_isExact W).comp (coproductRebasedFunctor_exact W))
    (IsExact.id W.cof W.weq) (coproductRightUnitIso W).hom (fun _ ↦ W.weq_iso _ inferInstance)
    (coproductRebasedFunctor_zero W) rfl t

/-- The whole zero-left unit cylinder on original cubes, jointly in time and input. -/
def coproductLeftUnitCubeMap :
    C(unitInterval × GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint,
      GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) where
  toFun tp := ⟨⟨fun z ↦ coproductLeftUnitHomotopy W (tp.1, tp.2 z), by fun_prop⟩, by
    intro z hz
    change coproductLeftUnitHomotopy W (tp.1, tp.2 z) = W.kBasepoint
    exact (congrArg (fun x ↦ coproductLeftUnitHomotopy W (tp.1, x))
      (tp.2.property z hz)).trans (coproductLeftUnitHomotopy_zero W tp.1)⟩
  continuous_toFun := by
    have hc : Continuous (fun tp :
        unitInterval × GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint ↦
      (⟨fun z ↦ coproductLeftUnitHomotopy W (tp.1, tp.2 z), by fun_prop⟩ :
        C((Fin (n + 1) → unitInterval), W.Delooping))) := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z :
        (unitInterval × GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) ×
          (Fin (n + 1) → unitInterval) ↦ coproductLeftUnitHomotopy W (z.1.1, z.1.2 z.2))
      fun_prop
    exact hc.subtype_mk _

/-- The whole zero-right unit cylinder on original cubes, jointly in time and input. -/
def coproductRightUnitCubeMap :
    C(unitInterval × GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint,
      GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) where
  toFun tp := ⟨⟨fun z ↦ coproductRightUnitHomotopy W (tp.1, tp.2 z), by fun_prop⟩, by
    intro z hz
    change coproductRightUnitHomotopy W (tp.1, tp.2 z) = W.kBasepoint
    exact (congrArg (fun x ↦ coproductRightUnitHomotopy W (tp.1, x))
      (tp.2.property z hz)).trans (coproductRightUnitHomotopy_zero W tp.1)⟩
  continuous_toFun := by
    have hc : Continuous (fun tp :
        unitInterval × GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint ↦
      (⟨fun z ↦ coproductRightUnitHomotopy W (tp.1, tp.2 z), by fun_prop⟩ :
        C((Fin (n + 1) → unitInterval), W.Delooping))) := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z :
        (unitInterval × GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) ×
          (Fin (n + 1) → unitInterval) ↦ coproductRightUnitHomotopy W (z.1.1, z.1.2 z.2))
      fun_prop
    exact hc.subtype_mk _

/-- The zero-left unit is the actual path from the compact coproduct cube to the second input. -/
def coproductLeftUnitPath (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    Path (coproductCube W n GenLoop.const q) q where
  toFun t := coproductLeftUnitCubeMap W n (t, q)
  continuous_toFun := (coproductLeftUnitCubeMap W n).continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := by
    ext z
    exact ((coproductLeftUnitHomotopy W).apply_zero (q z)).trans
      (coproductCube_zero_left_apply W n q z).symm
  target' := by
    ext z
    exact ((coproductLeftUnitHomotopy W).apply_one (q z)).trans
      (ConcreteCategory.congr_hom (deloopingMap_id W) (q z))

/-- The zero-right unit is the actual path from the compact coproduct cube to the first input. -/
def coproductRightUnitPath (p : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    Path (coproductCube W n p GenLoop.const) p where
  toFun t := coproductRightUnitCubeMap W n (t, p)
  continuous_toFun := (coproductRightUnitCubeMap W n).continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := by
    ext z
    exact ((coproductRightUnitHomotopy W).apply_zero (p z)).trans
      (coproductCube_zero_right_apply W n p z).symm
  target' := by
    ext z
    exact ((coproductRightUnitHomotopy W).apply_one (p z)).trans
      (ConcreteCategory.congr_hom (deloopingMap_id W) (p z))

/-- Both original coordinates of the zero-left unit cylinder remain literal. -/
theorem coproductLeftUnitPath_apply
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    coproductLeftUnitPath W n q t z = coproductLeftUnitHomotopy W (t, q z) := rfl

/-- Both original coordinates of the zero-right unit cylinder remain literal. -/
theorem coproductRightUnitPath_apply
    (p : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    coproductRightUnitPath W n p t z = coproductRightUnitHomotopy W (t, p z) := rfl

/-- Every time of the zero-left unit at the constant cube is constant. -/
theorem coproductLeftUnitPath_const (t : unitInterval) :
    coproductLeftUnitPath W n GenLoop.const t = GenLoop.const := by
  ext z
  exact coproductLeftUnitHomotopy_zero W t

/-- Every time of the zero-right unit at the constant cube is constant. -/
theorem coproductRightUnitPath_const (t : unitInterval) :
    coproductRightUnitPath W n GenLoop.const t = GenLoop.const := by
  ext z
  exact coproductRightUnitHomotopy_zero W t

end Quillen.Waldhausen.Additivity
