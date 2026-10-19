/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeInputTelescope

/-! # Original input composition on current Bass telescopes -/
@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace Quillen.KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan
variable {F G K : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}
    (A : Track laurent.op coefficient F) (B : Track laurent.op coefficient G)
    (D : Track laurent.op coefficient K)
    (a : F ⟶ G) (ha : Equivariant A B a)
    (b : G ⟶ K) (hb : Equivariant B D b)
    (hab : Equivariant A D (a ≫ b))

/-- Every original cylinder map preserves literal input composition. -/
theorem currentInputMap_comp :
    currentInputMap A B a ha ≫ currentInputMap B D b hb =
      currentInputMap A D (a ≫ b) hab := by
  apply NatTrans.ext
  funext X
  apply Telescope.hom_ext
  intro n i s x
  exact congrArg (fun y => Telescope.cylinder
    (fun j => ((strictDiagramIterate squareFunctor j).obj K).obj X)
    (fun j => (currentTransition D j).app X) n i (s, y))
    (congrArg (fun k => (k.app X).map n x)
      ((strictDiagramIterate squareFunctor i).map_comp a b)).symm

/-- Equality of the original input gives equality of the actual current maps. -/
theorem currentInputMap_congr (a' : F ⟶ G) (ha' : Equivariant A B a') (h : a = a') :
    currentInputMap A B a ha = currentInputMap A B a' ha' := by
  subst a'
  rfl

include hab in
/-- A proved original composite equality yields the corresponding original telescope square. -/
theorem currentInputMap_comp_eq (c : F ⟶ K) (hc : Equivariant A D c) (h : a ≫ b = c) :
    currentInputMap A B a ha ≫ currentInputMap B D b hb = currentInputMap A D c hc :=
  (currentInputMap_comp A B D a ha b hb hab).trans
    (currentInputMap_congr A D (a ≫ b) hab c hc h)

end Quillen.KTheory.Bass.SchemeNaturalSeed
