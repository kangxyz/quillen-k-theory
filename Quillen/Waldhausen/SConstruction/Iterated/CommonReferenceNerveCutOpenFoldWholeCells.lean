/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenFold
/-!
The second displayed cylinder retains its full parameter and height.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Convexity
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenFold
open CutOpenCarrier
variable {V W T : Model.{u}} (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
  (ε : G.functor ≅ (F ≫ J).functor) (Q : TopCat.{u})
  (l : C(|parameterSSet G|, Q)) (c : C(|parameterSSet F| × unitInterval, Q)) (q : Q)
  (h0 : ∀ z, c (z, 0) = l (mapParameter (attachPostcompNode F J G ε) z))
  (h1 : ∀ z, c (z, 1) = q)

/-- The second displayed cylinder retains its full parameter and height. -/
theorem map_cylinderPlus (z : |parameterSSet F|) (s : unitInterval) :
    map F J G ε Q l c q h0 h1 (cylinderPlus F J G ε ε (z, s)) = c (z, s) :=
  ConcreteCategory.congr_hom ((second_isPushout F J G ε ε).inl_desc _ _ _) (z, ULift.up s)

/-- The negative tip is the actual terminal value of the same fold. -/
theorem map_tipMinus : map F J G ε Q l c q h0 h1 (tipMinus F J G ε ε) = q := by
  let z : |parameterSSet F| := parameter F (fun _ : Fin 1 ↦ ⟨F, Iso.refl _⟩)
    (StdSimplex.single 0)
  have h := map_cylinder F J G ε Q l c q h0 h1 z 1
  rw [cylinderMinus_one] at h
  exact h.trans (h1 z)

/-- The positive tip is retained separately before the actual fold identifies its value. -/
theorem map_tipPlus : map F J G ε Q l c q h0 h1 (tipPlus F J G ε ε) = q := by
  let z : |parameterSSet F| := parameter F (fun _ : Fin 1 ↦ ⟨F, Iso.refl _⟩)
    (StdSimplex.single 0)
  have h := map_cylinderPlus F J G ε Q l c q h0 h1 z 1
  rw [cylinderPlus_one] at h
  exact h.trans (h1 z)
end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenFold
