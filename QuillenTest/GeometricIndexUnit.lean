/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IndexSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProductSwapOuterUnit
public import Quillen.KTheory.Bass.StrictDiagram

/-!
# The actual geometric index interchange and original unit-track consumer

The arbitrary-scheme square iso gives the expected Bass/reindex natural iso for
any strict spectrum diagram. The other regression retains the original geometric
prespectrum pullback at every time in the correctly directed unit square.
This does not identify the induced current-stage cone action or a tower map.
-/

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.FunctorIdentityAutomorphism Quillen.PerfectComplexes
open Quillen.PerfectComplexes.ProductSwapUnit
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w

namespace QuillenTest.GeometricIndexUnit

variable {T : Scheme.{u}} (q : T ⟶ integerBase) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})

/-- The actual four-corner index iso supplies the correctly oriented Bass interchange. -/
def eta : (baseProductFunctor q).op ⋙ (strictDiagramFunctor squareFunctor).obj F ≅
    (strictDiagramFunctor squareFunctor).obj ((baseProductFunctor q).op ⋙ F) :=
  Functor.isoWhiskerRight (interchange q) (F.mapArrow.mapArrow ⋙ strictSquareLoopedConeFunctor)

/-- The forward map is literally the cone/loop image of the original four index maps. -/
theorem eta_hom_app (X : Scheme.{u}ᵒᵖ) :
    (eta q F).hom.app X = strictSquareLoopedConeFunctor.map
      (F.mapArrow.mapArrow.map (squareIso q X).hom) := rfl

/-- The inverse retains naturality for all original scheme arrows. -/
theorem eta_inverse_naturality {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    ((strictDiagramFunctor squareFunctor).obj ((baseProductFunctor q).op ⋙ F)).map f ≫
        (eta q F).inv.app Y =
      (eta q F).inv.app X ≫
        ((strictDiagramFunctor squareFunctor).obj F).map ((baseProductFunctor q).op.map f) :=
  (eta q F).inv.naturality f

/-- Both directions of the concrete swap are inverse at the original geometric map level. -/
theorem original_swap_inverse {S : Scheme.{u}} (p : S ⟶ integerBase) (X : Scheme.{u}) :
    baseProductSwapMap p q X ≫ (baseProductSwapIso q p).hom.app X = 𝟙 _ :=
  baseProductSwapMap_comp p q X

/-- Every time slice retains the literal geometric prespectrum pullback along σ(S,T). -/
theorem actual_unitTrack {S : Scheme.{u}} (p : S ⟶ integerBase) (X : Scheme.{u})
    {V : Model.{u + 1}}
    (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
      ((baseProductFunctor p).obj ((baseProductFunctor q).obj X))))
    (r : Γ(T, ⊤)ˣ) (t : unitInterval) :
    (prespectrumIsoHomotopy G (onFunctor G.functor
      (smallUnit _ (innerUnit q p X r)))).at t ≫
        boundedFlatPerfectPrespectrumMap (baseProductSwapMap p q X) =
    (prespectrumIsoHomotopy (G ≫ swapModelMap p q X)
      (onFunctor (G ≫ swapModelMap p q X).functor
        (smallUnit _ (outerUnit q p X r)))).at t := by
  rw [← swapModelMap_prespectrum]
  exact ProductSwapOuterUnit.unitTrack_square p q X G r t

#print axioms AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.interchange
#print axioms eta
#print axioms eta_inverse_naturality
#print axioms Quillen.PerfectComplexes.ProductSwapOuterUnit.swap_outer_unit
#print axioms Quillen.PerfectComplexes.ProductSwapOuterUnit.polynomial_laurent_swap_unit
#print axioms actual_unitTrack

end QuillenTest.GeometricIndexUnit
