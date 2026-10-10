/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.Prespectrum

/-! # Consumers of the actual sequential S-prespectrum and original K-map -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
open Quillen Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.Tests.IteratedSPrespectrum

/-- Every successor space and every higher structure map retain the original finite stage. -/
theorem actual_levels (W : Model.{u}) (r : ℕ) :
    (prespectrum W).space (r+1) = SSet.toTop.obj ((stages r).obj W) ∧
    (prespectrum W).structureMap (r+1) = stageLoopMap r W := ⟨rfl, rfl⟩

/-- The zero space is literally the based loops on the first realization, and its
first adjoint structure map is the identity, including on every original path. -/
theorem actual_zero_space (W : Model.{u}) :
    (prespectrum W).space 0 = TopCat.of (Path W.waldhausen.kBasepoint W.waldhausen.kBasepoint) ∧
    ∀ γ : (prespectrum W).space 0, (prespectrum W).structureMap 0 γ = γ :=
  ⟨rfl, fun _ ↦ rfl⟩

/-- In every stage the whole continuous loop is the realization of the specified cylinder. -/
theorem actual_cylinder_formula (W : Model.{u}) (r : ℕ)
    (x : stageSpace r W) (t : unitInterval) :
    stageLoopMap r W x t = SSet.toTop.map (stageCylinder r W)
      ((realizationCylinderIso ((stages r).obj W)).inv (x, ULift.up t)) := rfl

/-- Both original faces and the entire zero track hold in every higher simplicial degree. -/
theorem all_stage_faces (W : Model.{u}) (r : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj W).obj n) :
    (∀ c : Fin 2, (stageCylinder r W).app n (A, ⟨SimplexCategory.const n.unop ⦋1⦌ c⟩) =
      (SSet.const (X := (stages r).obj W) (stageVertex (r+1) W)).app n A) ∧
    stageLoopMap r W (stagePoint r W) = Path.refl (stagePoint (r+1) W) :=
  ⟨stageCylinder_endpoint r W n A, stageLoopMap_point r W⟩

/-- The exact-functor compatibility retains every point of every resulting loop. -/
theorem whole_structure_square {V W : Model.{u}} (F : V ⟶ W) (n : ℕ)
    (x : (prespectrum V).space n) (t : unitInterval) :
    (prespectrumMap F).map (n+1) ((prespectrum V).structureMap n x t) =
      (prespectrum W).structureMap n ((prespectrumMap F).map n x) t :=
  congrArg (fun γ ↦ γ t) ((prespectrumMap F).comm n x)

/-- Composition and identity hold for the actual entire prespectrum maps. -/
theorem actual_functor_laws {U V W : Model.{u}} (F : U ⟶ V) (G : V ⟶ W) :
    prespectrumFunctor.map (F ≫ G) = prespectrumFunctor.map F ≫ prespectrumFunctor.map G ∧
    prespectrumFunctor.map (𝟙 U) = 𝟙 (prespectrum U) :=
  ⟨prespectrumFunctor.map_comp F G, prespectrumFunctor.map_id U⟩

variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Independent original category universes are retained, including degree-zero inverse laws. -/
theorem original_K_zero_inverse (a : W.K 0) :
    (originalZeroSpaceEquiv W 0).symm (originalZeroSpaceEquiv W 0 a) = a :=
  (originalZeroSpaceEquiv W 0).symm_apply_apply a

/-- In positive zero-space degree the comparison preserves the original multiplication. -/
theorem original_K_product (n : ℕ) (a b : W.K (n+1)) :
    originalZeroSpaceMulEquiv W n (a*b) =
      originalZeroSpaceMulEquiv W n a * originalZeroSpaceMulEquiv W n b :=
  (originalZeroSpaceMulEquiv W n).map_mul a b

/-- The unchanged original K-map is the homotopy map of the constructed zero-space map. -/
theorem original_K_map {D : Type u} [Category.{v} D] (V : Structure D) {F : C ⥤ D}
    (hF : IsExact W.cof W.weq V.cof V.weq F) (h0 : F.obj W.zero = V.zero)
    (n : ℕ) (a : W.K n) :
    originalZeroSpaceEquiv V n (KMap hF n a) =
      homotopyGroupMap ((originalPrespectrumMap W V hF h0).map 0)
        ((originalPrespectrumMap W V hF h0).map_point 0) (originalZeroSpaceEquiv W n a) :=
  originalZeroSpaceEquiv_naturality W V hF h0 n a

end Quillen.Tests.IteratedSPrespectrum
