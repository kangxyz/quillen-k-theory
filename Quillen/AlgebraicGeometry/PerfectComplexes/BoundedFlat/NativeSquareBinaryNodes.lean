/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PostReferenceFamily

/-! Both original binary rows inside the actual five-node square, with full references. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassH0Merge NativeSquareFiveSimplex
variable {X Y Z T : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
  (h : p ≫ v = q ≫ w)

/-- The first full binary row uses the unchanged original square source. -/
theorem square_first_nodes (i : Fin 3) :
    nodes p v q w h (firstFace.toOrderHom i) = binaryNodes p v i := by
  fin_cases i <;> rfl

/-- The second full row includes the actual original square source equality. -/
theorem square_second_nodes (i : Fin 3) :
    nodes p v q w h (secondFace.toOrderHom i) =
      anchorNode (sourceIso p v q w h) (binaryNodes q w i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (source_eq p v q w h)
    simp [sourceIso, binaryNodes]
  · rfl
  · rfl

variable {U : Model.{u + 1}}
  (F : modelOf (boundedFlatPerfectWaldhausen Z) ⟶ U)
  (J : modelOf (boundedFlatPerfectWaldhausen X) ⟶ U)
  (ρ : F.functor ≅ (source p v ≫ J).functor)

/-- The first original postcomposed square row, without replacing its reference. -/
theorem post_square_first_nodes (i : Fin 3) :
    postReferenceNode F J ρ (nodes p v q w h (firstFace.toOrderHom i)) =
      postReferenceNode F J ρ (binaryNodes p v i) :=
  congrArg (postReferenceNode F J ρ) (square_first_nodes p v q w h i)

/-- The other postcomposed square row retains its genuine geometric equality transport. -/
theorem post_square_second_nodes (i : Fin 3) :
    postReferenceNode F J ρ (nodes p v q w h (secondFace.toOrderHom i)) =
      postReferenceNode F J (ρ ≪≫ isoWhiskerRight (sourceIso p v q w h) J.functor)
        (binaryNodes q w i) :=
  (congrArg (postReferenceNode F J ρ) (square_second_nodes p v q w h i)).trans
    (post_anchor_node F J ρ (sourceIso p v q w h) (binaryNodes q w i))

end Quillen.PerfectComplexes.BassH1Join
