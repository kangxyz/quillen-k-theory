/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SquareConeStrength
public import Quillen.Topology.Prespectrum.ParameterLoopingHomotopy

/-!
# Independent-loop regression for actual square cone strength

The original null time and the new parameter-loop coordinate remain independent,
including level zero. The resulting map is the actual natural cone comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.KTheory.Bass.SquareConeStrength
universe u v w
namespace QuillenTest.SquareConeStrength
variable {C : Type u} [Category.{v} C]
  (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w})))
  (Q : C ⥤ Arrow (Arrow C))

/-- Applying independent parameter looping preserves the original whole source null. -/
theorem looped_sourceNull (X : C) (n : ℕ) (r : unitInterval)
    (γ : (parameterLooping (((strictDiagramFunctor Q).obj S.left.left).obj X)).space n) :
    (parameterLoopingMap ((chi S Q).app X)).map n
        ((sourceNull (bassSquare S Q) X).parameterLooping.level n (r, γ)) =
      (strictDiagramMapHomotopy (sourceNull S)
        (sourceNull_naturality S) Q X).parameterLooping.level n (r, γ) := by
  change Path _ _ at γ
  apply Path.ext
  funext s
  exact chi_sourceNull S Q X n r (γ s)

/-- The exact source-null comparison still uses the original coefficient maps on both cones. -/
theorem coefficient_square {X Y : C} (k : X ⟶ Y) :
    (mappingConeDiagram (comparison (bassSquare S Q))).map k ≫ (chi S Q).app Y =
      (chi S Q).app X ≫
        ((strictDiagramFunctor Q).obj (mappingConeDiagram (comparison S))).map k :=
  (chi S Q).naturality k

#print axioms Quillen.KTheory.Bass.SquareConeStrength.rho_comparison
#print axioms Quillen.KTheory.Bass.SquareConeStrength.chi
#print axioms Quillen.KTheory.Bass.SquareConeStrength.chi_sourceNull
#print axioms looped_sourceNull

end QuillenTest.SquareConeStrength
