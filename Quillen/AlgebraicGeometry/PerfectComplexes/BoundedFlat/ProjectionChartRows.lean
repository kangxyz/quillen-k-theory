/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PreReferenceFamily
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionPolynomialColumns

/-! Original precomposed chart rows inside a projection rectangle and a five-node square. -/
@[expose] public section

open Quillen.PerfectComplexes.BassH0Merge

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassH0Merge
section Square
variable {X Y Z T : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
  (h : p ≫ v = q ≫ w) {U : Model.{u + 1}}
  (F : U ⟶ modelOf (boundedFlatPerfectWaldhausen X))
  (P : U ⟶ modelOf (boundedFlatPerfectWaldhausen Z))
  (ρ : F.functor ≅ (P ≫ NativeSquareFiveSimplex.source p v).functor)

/-- The first original square row after the actual fixed precomposition. -/
theorem pre_square_first_nodes (i : Fin 3) :
    preReferenceNode F P ρ (NativeSquareFiveSimplex.nodes p v q w h
      (NativeSquareFiveSimplex.firstFace.toOrderHom i)) =
      preReferenceNode F P ρ (binaryNodes p v i) :=
  congrArg (preReferenceNode F P ρ) (square_first_nodes p v q w h i)

/-- The second row retains its original geometric square equality under precomposition. -/
theorem pre_square_second_nodes (i : Fin 3) :
    preReferenceNode F P ρ (NativeSquareFiveSimplex.nodes p v q w h
      (NativeSquareFiveSimplex.secondFace.toOrderHom i)) =
      preReferenceNode F P
        (ρ ≪≫ isoWhiskerLeft P.functor (NativeSquareFiveSimplex.sourceIso p v q w h))
        (binaryNodes q w i) :=
  (congrArg (preReferenceNode F P ρ) (square_second_nodes p v q w h i)).trans
    (pre_anchor_node F P ρ (NativeSquareFiveSimplex.sourceIso p v q w h) (binaryNodes q w i))
end Square

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)

/--
The reference from the projection source to the first triple `c, q, p`, induced by the
projection equation `hr`.
-/
def nativeFirstReference : (ProjectionReference.reference c r).functor ≅
    (NormalizedTripleSimplex.sourceMap c q p).functor :=
  eqToIso (ProjectionReference.anchor p q c r hr)

/-- The first original chart binary row has its exact native projection reference. -/
theorem native_first_right_row (i : Fin 3) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (rightRowReference (ProjectionReference.reference c r) c q p
          (nativeFirstReference p q c r hr)) (binaryNodes c q i) := by
  have hn := projection_first_right_row p q p' q' a b c hp hq r hr
    (ProjectionReference.reference c r) rfl i
  have he : projectionNativeNode p q p' q' a b c hp hq r hr
      (ProjectionReference.reference c r) rfl
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      ProjectionReference.nodes p q p' q' a b c hp hq r hr
        (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) := anchorNode_refl _
  exact he.symm.trans (by
    simpa only [projectionFirstReference, eqToIso_refl, Iso.refl_trans, nativeFirstReference,
      preBinaryNodes, preReferenceNode]
      using hn)

/-- The second original chart binary row includes the unchanged middle-square source transport. -/
theorem native_middle_right_row (i : Fin 3) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (rightRowReference (ProjectionReference.reference c r) q' b p
          (nativeMiddleReference p q q' b c hq r hr)) (binaryNodes q' b i) :=
  (native_middle_nodes p q p' q' a b c hp hq r hr (rightIndex i)).trans
    (triple_right_row (ProjectionReference.reference c r) q' b p
      (nativeMiddleReference p q q' b c hq r hr) i)

end Quillen.PerfectComplexes.BassH1Join
