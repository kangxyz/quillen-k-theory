/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.OmegaSpectrum

/-! # Original-map consumers of the genuine all-stage Waldhausen Omega-spectrum -/
@[expose] public section

open Quillen.TheoremA
open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
open Quillen Quillen.Waldhausen.IteratedS
universe u v
namespace QuillenTest.IteratedSOmegaSpectrum

open Quillen
open Quillen.Waldhausen.Fibration.RelativeRows TheoremA

/-- The whole original interval object and both inverse row transpositions are retained. -/
theorem original_row_coordinates (W : Model.{u}) (m n : SimplexCategory)
    (A : (rows m).obj ((rows n).obj W)) (p : Interval n) (q : Interval m) :
    (((rowSwap W m n).hom.functor.obj A).obj.obj p).obj.obj q = (A.obj.obj q).obj.obj p ∧
    (rowSwap W m n).hom ≫ (rowSwap W m n).inv = 𝟙 _ := ⟨rfl, (rowSwap W m n).hom_inv_id⟩

/-- The original higher one-row cylinder commutes with the genuine coordinate swap. -/
theorem original_insertion_interchange (W : Model.{u}) (m n : SimplexCategory) (τ : n ⟶ ⦋1⦌) :
    (rows m).map ((insertion τ).app W) ≫ (rowSwap W m n).hom =
      (insertion τ).app ((rows m).obj W) := insertion_rowSwap W m τ

/-- Every higher added-initial path object contracts with no all-weak premise on W. -/
theorem genuine_path_contraction (r : ℕ) (W : Model.{u}) :
    ContractibleSpace |diagonalSSet (pathDiagram W ⋙ stages r)| ∧
    (pathRealizationEquiv (stages r) W).toFun = (SSet.toTop.map (pathAugmentationMap (stages r)
      W)).hom :=
  ⟨pathStage_contractible r W, rfl⟩

/-- Higher additivity retains the displayed first/tail map and the original strict fiber section. -/
theorem original_first_tail (r : ℕ) (W : Model.{u}) (n : SimplexCategory) :
    (stageFirstTailRealizationEquiv r W n).toFun = (SSet.toTop.map (stageFirstTail r W n)).hom ∧
    (stagePathFiber r W).app (op n) ≫ stageFirstTail r W n =
      ProductRealization.vertexSection ((stages r).obj W) ((stages r).obj ((rows n).obj W))
        (stageVertex r ((rows n).obj W)) :=
  ⟨stageFirstTailRealizationEquiv_toFun r W n, stagePathFiber_firstTail r W n⟩

/-- The total comparison retains both the exact source and every point of its whole constant path.
  -/
theorem original_total_fiber (r : ℕ) (W : Model.{u}) (x : stageSpace r W) (t : unitInterval) :
    (stageTotalFiberComparison r W x).1.1 = SSet.toTop.map (stageTotalFiberInclusion r W) x ∧
    (stageTotalFiberComparison r W x).1.2 t = stagePoint (r+1) W := ⟨rfl, rfl⟩

/-- The all-stage comparison uses the existing cylinder at every original time parameter. -/
theorem original_all_stage_loop (r : ℕ) (W : Model.{u}) (x : stageSpace r W) (t : unitInterval) :
    HomotopyFiber.cylinderLoop (stageTotalTailMap r W) (stagePoint (r+1) W)
      (stagePathPoint r W) (stageTotalTailMap_point r W)
      (SSet.toTop.map (stageTotalFiberInclusion r W)).hom
      (stageTotalTailMap_fiberInclusion r W) (stageRelativeTopHomotopy r W) x t = stageLoopMap r W x
        t :=
  congrArg (fun f ↦ f x t) (stageCylinderLoop_eq r W)

/-- Components and all finite homotopy degrees are controlled for every actual structure map. -/
theorem original_structure_weak (W : Model.{u}) (n k : ℕ)
    (x : (prespectrum W).space n)
    (γ : Path ((prespectrum W).point (n+1)) ((prespectrum W).point (n+1))) :
    (∃ y, Joined ((prespectrum W).structureMap n y) γ) ∧
    Function.Bijective (homotopyGroupMap (N := Fin k) ((prespectrum W).structureMap n) (x := x) rfl)
      :=
  ⟨(prespectrum_isOmega W n).component_surjective γ, (prespectrum_isOmega W n).homotopy_bijective x
    k⟩

/-- Every class at every higher stage has a unique preimage under the actual structure map. -/
theorem unique_original_structure_preimage (W : Model.{u}) (n k : ℕ)
    (x : (prespectrum W).space n)
    (b : HomotopyGroup.Pi k (Path ((prespectrum W).point (n+1)) ((prespectrum W).point (n+1)))
      ((prespectrum W).structureMap n x)) :
    ∃! a, homotopyGroupMap (N := Fin k) ((prespectrum W).structureMap n) (x := x) rfl a = b := by
  obtain ⟨hi, hs⟩ := (prespectrum_isOmega W n).homotopy_bijective x k
  obtain ⟨a, ha⟩ := hs b
  exact ⟨a, ha, fun a' ha' ↦ hi (ha'.trans ha.symm)⟩

/-- The enhanced functor has actual categorical identity and composition laws. -/
theorem omega_functor_laws {U V W : Model.{u}} (F : U ⟶ V) (G : V ⟶ W) :
    omegaSpectrumFunctor.map (F ≫ G) = omegaSpectrumFunctor.map F ≫ omegaSpectrumFunctor.map G ∧
    omegaSpectrumFunctor.map (𝟙 U) = 𝟙 (omegaSpectrumFunctor.obj U) :=
  ⟨omegaSpectrumFunctor.map_comp F G, omegaSpectrumFunctor.map_id U⟩

variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The constructed original spectrum keeps independent object and morphism universes. -/
theorem original_universe_omega : (originalOmegaSpectrum W).obj.IsOmega :=
  (originalOmegaSpectrum W).property

/-- The zero-space inverse recovers the unchanged original K-zero class. -/
theorem original_K_zero (a : W.K 0) :
    (originalOmegaSpectrum W).obj = originalPrespectrum W ∧
    (originalZeroSpaceEquiv W 0).symm (originalZeroSpaceEquiv W 0 a) = a :=
  ⟨rfl, (originalZeroSpaceEquiv W 0).symm_apply_apply a⟩

/-- The full Omega-spectrum enhancement keeps the literal old K-map, with chosen-zero equality
  explicit. -/
theorem original_K_map {D : Type u} [Category.{v} D] (V : Structure D) {F : C ⥤ D}
    (hF : IsExact W.cof W.weq V.cof V.weq F) (h0 : F.obj W.zero = V.zero) (n : ℕ) (a : W.K n) :
    originalZeroSpaceEquiv V n (KMap hF n a) =
      homotopyGroupMap ((originalOmegaSpectrumMap W V hF h0).hom.map 0)
        ((originalOmegaSpectrumMap W V hF h0).hom.map_point 0) (originalZeroSpaceEquiv W n a) :=
  originalZeroSpaceEquiv_naturality W V hF h0 n a

end QuillenTest.IteratedSOmegaSpectrum
