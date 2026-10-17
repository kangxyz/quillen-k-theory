/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeTree
public import Quillen.Topology.Path.ScalarPathCells

/-! The original four-quarter route in the full-reference scalar tree. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
open CutOpenCarrier Quillen.NativePathCells

/-- Realize an original simplicial edge with its original increasing interval coordinate. -/
def realizedEdge {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y) : C(|X| × unitInterval, |Y|) :=
  ⟨fun z ↦ (SSet.toTop.map H).hom ((realizationCylinderIso X).inv.hom (z.1, ULift.up z.2)),
    (SSet.toTop.map H).hom.continuous.comp
      ((realizationCylinderIso X).inv.hom.continuous.comp
        (continuous_fst.prodMk (continuous_uliftUp.comp continuous_snd)))⟩

theorem realizedEdge_zero {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y) (x : |X|) :
    realizedEdge H (x, 0) = SSet.toTop.map (SSet.ι₀ ≫ H) x := by
  have h : SSet.toTop.map (SSet.ι₀ (X := X)) ≫ (realizationCylinderIso X).hom =
      TopCat.ι₀ := realizationCylinderComparison_zero X
  have h' := congrArg (fun k ↦ k ≫ (realizationCylinderIso X).inv ≫ SSet.toTop.map H) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp] at h'
  exact (ConcreteCategory.congr_hom h' x).symm

theorem realizedEdge_one {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y) (x : |X|) :
    realizedEdge H (x, 1) = SSet.toTop.map (SSet.ι₁ ≫ H) x := by
  have h : SSet.toTop.map (SSet.ι₁ (X := X)) ≫ (realizationCylinderIso X).hom =
      TopCat.ι₁ := realizationCylinderComparison_one X
  have h' := congrArg (fun k ↦ k ≫ (realizationCylinderIso X).inv ≫ SSet.toTop.map H) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp] at h'
  exact (ConcreteCategory.congr_hom h' x).symm

variable {V W T : Model.{u}} (E : V ⟶ W) (J : W ⟶ T)

/-- The whole oriented edge 12, for an arbitrary full-nerve point. -/
def path12 (e : |parameterSSet E|) :
    Path (SSet.toTop.map (oneVertex E J) e)
      (SSet.toTop.map (plusVertex E J) (SSet.toTop.map (attachment E J) e)) where
  toFun t := realizedEdge (edge12 E J) (e, t)
  continuous_toFun := by fun_prop
  source' := by rw [realizedEdge_zero, edge12_zero]
  target' := by
    rw [realizedEdge_one, edge12_one]
    rw [Functor.map_comp]
    rfl

/-- The whole oriented edge 01, for an arbitrary full-nerve point. -/
def path01 (e : |parameterSSet E|) :
    Path (SSet.toTop.map (zeroVertex E J) e)
      (SSet.toTop.map (oneVertex E J) e) where
  toFun t := realizedEdge (edge01 E J) (e, t)
  continuous_toFun := by fun_prop
  source' := by rw [realizedEdge_zero, edge01_zero]
  target' := by
    rw [realizedEdge_one, edge01_one]

/-- The whole oriented edge 03, for an arbitrary full-nerve point. -/
def path03 (e : |parameterSSet E|) :
    Path (SSet.toTop.map (zeroVertex E J) e)
      (SSet.toTop.map (threeVertex E J) e) where
  toFun t := realizedEdge (edge03 E J) (e, t)
  continuous_toFun := by fun_prop
  source' := by rw [realizedEdge_zero, edge03_zero]
  target' := by
    rw [realizedEdge_one, edge03_one]

/-- The whole oriented edge 34, for an arbitrary full-nerve point. -/
def path34 (e : |parameterSSet E|) :
    Path (SSet.toTop.map (threeVertex E J) e)
      (SSet.toTop.map (minusVertex E J) (SSet.toTop.map (attachment E J) e)) where
  toFun t := realizedEdge (edge34 E J) (e, t)
  continuous_toFun := by fun_prop
  source' := by rw [realizedEdge_zero, edge34_zero]
  target' := by
    rw [realizedEdge_one, edge34_one]
    rw [Functor.map_comp]
    rfl

/-- The original edge as a jointly continuous family on the whole reference nerve. -/
def homotopy12 : (SSet.toTop.map (oneVertex E J)).hom.Homotopy
    ((SSet.toTop.map (plusVertex E J)).hom.comp (SSet.toTop.map (attachment E J)).hom) where
  toFun z := realizedEdge (edge12 E J) (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left e := (path12 E J e).source
  map_one_left e := (path12 E J e).target

/-- The original edge as a jointly continuous family on the whole reference nerve. -/
def homotopy01 : (SSet.toTop.map (zeroVertex E J)).hom.Homotopy
    ((SSet.toTop.map (oneVertex E J)).hom) where
  toFun z := realizedEdge (edge01 E J) (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left e := (path01 E J e).source
  map_one_left e := (path01 E J e).target

/-- The original edge as a jointly continuous family on the whole reference nerve. -/
def homotopy03 : (SSet.toTop.map (zeroVertex E J)).hom.Homotopy
    ((SSet.toTop.map (threeVertex E J)).hom) where
  toFun z := realizedEdge (edge03 E J) (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left e := (path03 E J e).source
  map_one_left e := (path03 E J e).target

/-- The original edge as a jointly continuous family on the whole reference nerve. -/
def homotopy34 : (SSet.toTop.map (threeVertex E J)).hom.Homotopy
    ((SSet.toTop.map (minusVertex E J)).hom.comp (SSet.toTop.map (attachment E J)).hom) where
  toFun z := realizedEdge (edge34 E J) (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left e := (path34 E J e).source
  map_one_left e := (path34 E J e).target

/-- The two literal half-concatenations produce the original four quarters. -/
def overlapHomotopy := ((homotopy01 E J).trans (homotopy12 E J)).symm.trans
  ((homotopy03 E J).trans (homotopy34 E J))

/-- The literal four-quarter traversal: reverse 1→2, reverse 0→1, then 0→3 and 3→4. -/
def overlapPath (e : |parameterSSet E|) :
    Path (SSet.toTop.map (plusVertex E J) (SSet.toTop.map (attachment E J) e))
      (SSet.toTop.map (minusVertex E J) (SSet.toTop.map (attachment E J) e)) :=
  ((path01 E J e).trans (path12 E J e)).symm.trans
    ((path03 E J e).trans (path34 E J e))

/-- The full route retains both independent reference and path coordinates continuously. -/
def overlap : C(|parameterSSet E| × unitInterval, space E J) :=
  ⟨fun z ↦ overlapPath E J z.1 z.2, by
    change Continuous (fun z : |parameterSSet E| × unitInterval ↦
      overlapHomotopy E J (z.2, z.1))
    fun_prop⟩

theorem overlap_zero (e : |parameterSSet E|) : overlap E J (e, 0) =
    SSet.toTop.map (plusVertex E J) (SSet.toTop.map (attachment E J) e) :=
  (overlapPath E J e).source

theorem overlap_one (e : |parameterSSet E|) : overlap E J (e, 1) =
    SSet.toTop.map (minusVertex E J) (SSet.toTop.map (attachment E J) e) :=
  (overlapPath E J e).target

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
