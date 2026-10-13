/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.EmbeddingRelativeChains
public import Quillen.Topology.LocalCoefficients.ConstantChainMaps
public import Quillen.Topology.MappingCylinder.SourceCollar

/-! # Genuine mapping-cylinder relative acyclicity from the original chain map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u

namespace Quillen.MappingCylinder
variable {X Y M : TopCat.{u}} {f : X ⟶ Y}
  {l : X ⊗ TopCat.I ⟶ M} {c : Y ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I) f l c)

include sq

/-- The actual source inclusion is an embedding, witnessed by its product collar. -/
theorem mappingCylinderStart_isEmbedding : Topology.IsEmbedding (TopCat.ι₀ ≫ l) := by
  let e := SourceCollar.collarHomeomorph sq 1
  have h : Topology.IsEmbedding (fun x : X ↦
      (e (x, (⟨0, zero_lt_one⟩ : SourceCollar.Interval 1))).val) :=
    Topology.IsEmbedding.subtypeVal.comp
      (e.isEmbedding.comp (isEmbedding_prodMkLeft _))
  exact h

/-- The genuine projection is exactly the inverse map of the established deformation retract. -/
def mappingCylinderProjectionHomotopyEquiv : ContinuousMap.HomotopyEquiv M Y :=
  (mappingCylinderTargetStrongDeformationRetract sq).toHomotopyEquiv.symm

@[simp]
theorem mappingCylinderProjectionHomotopyEquiv_toFun :
    (mappingCylinderProjectionHomotopyEquiv sq).toFun =
      (mappingCylinderProjection sq).hom := rfl

end Quillen.MappingCylinder

namespace Quillen.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual image pair is acyclic when its original embedding chain map
is a quasi-isomorphism. -/
theorem embeddingRelative_acyclic_of_quasiIso (j : C(X, Y))
    (hj : Topology.IsEmbedding j) (A : System.{u, u} Y)
    (hq : QuasiIso (pushforwardChainMap j A)) :
    (relativeSingularChainComplex (Set.range j) A).Acyclic := by
  have he : QuasiIso ((embeddingRangeChainIso j hj A).hom ≫
      pushforwardChainMap (subspaceInclusion (Set.range j)) A) := by
    rwa [embeddingRangeChainIso_inclusion]
  have hq' : QuasiIso (pushforwardChainMap (subspaceInclusion (Set.range j)) A) :=
    (quasiIso_iff_comp_left _ _).mp he
  let S : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
    ShortComplex.mk (pushforwardChainMap (subspaceInclusion (Set.range j)) A)
      (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  exact hS.acyclic_X₃ hq'

variable {B C M : TopCat.{u}} {f : B ⟶ C}
  {l : B ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : B ⟶ B ⊗ TopCat.I) f l c)

include sq

/-- The original chain quasi-isomorphism transfers to the literal cylinder-source embedding. -/
theorem mappingCylinderStart_quasiIso_of_quasiIso (A : System.{u, u} C)
    (hq : QuasiIso (pushforwardChainMap f.hom A)) :
    QuasiIso (pushforwardChainMap (TopCat.ι₀ ≫ l).hom
      (pullback (MappingCylinder.mappingCylinderProjection sq).hom A)) := by
  let p := (MappingCylinder.mappingCylinderProjection sq).hom
  let j := (TopCat.ι₀ ≫ l).hom
  have hp : QuasiIso (pushforwardChainMap p A) :=
    pushforwardChainMap_quasiIso_of_homotopyEquiv
      (MappingCylinder.mappingCylinderProjectionHomotopyEquiv sq) A
  have hjp : p.comp j = f.hom :=
    congrArg TopCat.Hom.hom (MappingCylinder.mappingCylinderProjection_start sq)
  have hcomp : QuasiIso (pushforwardChainMap (p.comp j) A) := by rwa [hjp]
  rw [pushforwardChainMap_comp] at hcomp
  have : IsIso (coefficientChainMap (pullbackCompositionIso j p A).hom) := by
    change IsIso ((coefficientChainFunctor B).map (pullbackCompositionIso j p A).hom)
    infer_instance
  have hmiddle : QuasiIso (pushforwardChainMap j (pullback p A) ≫
      pushforwardChainMap p A) :=
    (quasiIso_iff_comp_left _ _).mp hcomp
  exact (quasiIso_iff_comp_right _ _).mp hmiddle

/-- Relative acyclicity concerns the actual embedded source in the mapping cylinder,
not the cokernel of the possibly noninjective original map. -/
theorem mappingCylinderRelative_acyclic_of_quasiIso (A : System.{u, u} C)
    (hq : QuasiIso (pushforwardChainMap f.hom A)) :
    (relativeSingularChainComplex (Set.range (TopCat.ι₀ ≫ l).hom)
      (pullback (MappingCylinder.mappingCylinderProjection sq).hom A)).Acyclic :=
  embeddingRelative_acyclic_of_quasiIso _
    (MappingCylinder.mappingCylinderStart_isEmbedding sq) _
    (mappingCylinderStart_quasiIso_of_quasiIso sq A hq)

/-- For every integral coefficient module, the output is the original constant-coefficient pair. -/
theorem mappingCylinderRelative_constant_acyclic_of_quasiIso (V : ModuleCat.{u} ℤ)
    (hq : QuasiIso (pushforwardChainMap f.hom (constant C V))) :
    (relativeSingularChainComplex (Set.range (TopCat.ι₀ ≫ l).hom)
      (constant M V)).Acyclic :=
  mappingCylinderRelative_acyclic_of_quasiIso sq (constant C V) hq

end Quillen.LocalCoefficients
