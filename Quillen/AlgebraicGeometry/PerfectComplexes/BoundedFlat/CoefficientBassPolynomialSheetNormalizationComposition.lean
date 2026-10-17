/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialDirectPathCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTipFaces

/-!
# Composition of actual polynomial first-sheet normalizations

Two successive full-reference normalizations equal normalization by the composite
reference isomorphism. The proof retains every Laurent node, polynomial cylinder
parameter and height, and the unreduced terminal tip. The actual left and right
radial cap endpoint maps consume this identity.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPolynomialSheetNormalization
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier

private theorem reanchor_node_comp {V W : Model.{u}} {F F' F'' : V ⟶ W}
    (δ : F'.functor ≅ F.functor) (γ : F''.functor ≅ F'.functor) (N : Node F) :
    CommonReferenceProduct.reanchor γ (CommonReferenceProduct.reanchor δ N) =
      CommonReferenceProduct.reanchor (γ ≪≫ δ) N := by
  rcases N with ⟨K, ρ⟩
  simp only [CommonReferenceProduct.reanchor, Iso.trans_assoc]

private theorem reanchor_parameter_comp {V W : Model.{u}} {F F' F'' : V ⟶ W}
    (δ : F'.functor ≅ F.functor) (γ : F''.functor ≅ F'.functor)
    (y : |parameterSSet F|) :
    mapParameter (CommonReferenceProduct.reanchor γ)
      (mapParameter (CommonReferenceProduct.reanchor δ) y) =
    mapParameter (CommonReferenceProduct.reanchor (γ ≪≫ δ)) y := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F y
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns ↦ parameter F'' ns z)
    (funext (fun i ↦ reanchor_node_comp δ γ (N i)))

/-- The Laurent reference retains the original anchor through both normalizations. -/
theorem laurentIso_comp {V W T : Model.{u}} (F F' F'' : V ⟶ W) (J : W ⟶ T)
    (G : V ⟶ T) (ε : G.functor ≅ (F ≫ J).functor)
    (δ : F'.functor ≅ F.functor) (γ : F''.functor ≅ F'.functor) :
    laurentIso F' F'' J (F' ≫ J) (Iso.refl _) γ ≪≫ laurentIso F F' J G ε δ =
      laurentIso F F'' J G ε (γ ≪≫ δ) := by
  apply Iso.ext
  ext X
  have h : J.functor.map (γ.hom.app X) ≫ 𝟙 ((F' ≫ J).functor.obj X) ≫
      J.functor.map (δ.hom.app X) ≫ ε.inv.app X =
      J.functor.map (γ.hom.app X) ≫ J.functor.map (δ.hom.app X) ≫ ε.inv.app X :=
    congrArg (fun k ↦ J.functor.map (γ.hom.app X) ≫ k)
      (Category.id_comp (J.functor.map (δ.hom.app X) ≫ ε.inv.app X))
  simpa [laurentIso] using h

/-- Successive normalizations agree on every point of the actual first sheet. -/
theorem map_comp {V W T : Model.{u}} (F F' F'' : V ⟶ W) (J : W ⟶ T)
    (G : V ⟶ T) (ε : G.functor ≅ (F ≫ J).functor)
    (δ : F'.functor ≅ F.functor) (γ : F''.functor ≅ F'.functor)
    (z : |firstSimplicial F J G ε|) :
    map F' F'' J (F' ≫ J) (Iso.refl _) γ (map F F' J G ε δ z) =
      map F F'' J G ε (γ ≪≫ δ) z := by
  have h : (fun z ↦ map F' F'' J (F' ≫ J) (Iso.refl _) γ (map F F' J G ε δ z)) =
      (fun z ↦ map F F'' J G ε (γ ≪≫ δ) z) := by
    apply FourEdgeTree.SetDescent.funext (attaching F J G ε) (erase F)
    · rintro ⟨y, ⟨t⟩⟩
      dsimp only
      rw [map_cylinder, map_cylinder, map_cylinder, reanchor_parameter_comp]
    · intro y
      change map F' F'' J (F' ≫ J) (Iso.refl _) γ
        (map F F' J G ε δ (SSet.toTop.map (left₀ F J G ε) y)) =
          map F F'' J G ε (γ ≪≫ δ) (SSet.toTop.map (left₀ F J G ε) y)
      rw [map_laurent, map_laurent, map_laurent, reanchor_parameter_comp,
        laurentIso_comp]
    · intro y
      change map F' F'' J (F' ≫ J) (Iso.refl _) γ
        (map F F' J G ε δ (SSet.toTop.map (right₀ F J G ε) y)) =
          map F F'' J G ε (γ ≪≫ δ) (SSet.toTop.map (right₀ F J G ε) y)
      rw [map_tip, map_tip, map_tip]
  exact congrFun h z

end Quillen.PerfectComplexes.CoefficientBassPolynomialSheetNormalization
