/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Duality.ComplexSubcategory

/-!
# Actual pullback gluing of cochain quasi-isomorphisms

The genuine degree-reversing opposite-complex equivalence transports the
established pushout gluing theorem to arbitrary pullback squares with epic
legs. All four original vertical maps and their exact commuting equations
are retained. No abstract pullback-gluing axiom is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace Quillen.CochainComplex

/-- Genuine gluing of quasi-isomorphisms across actual pullback squares with epic legs. -/
lemma quasiIso_pullback_gluing {C : Type u} [Category.{v} C] [Abelian C]
    {P X Y Z P' X' Y' Z' : CochainComplex C ℤ}
    {i : P ⟶ X} {j : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {i' : P' ⟶ X'} {j' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    [Epi f] [Epi f'] (h : IsPullback i j f g) (h' : IsPullback i' j' f' g')
    (a : P ⟶ P') (b : X ⟶ X') (c : Y ⟶ Y') (d : Z ⟶ Z')
    (hi : i ≫ b = a ≫ i') (hj : j ≫ c = a ≫ j')
    (hf : f ≫ d = b ≫ f') (hg : g ≫ d = c ≫ g')
    [QuasiIso b] [QuasiIso c] [QuasiIso d] : QuasiIso a := by
  let E := (_root_.CochainComplex.opEquivalence C).functor
  let : E.IsEquivalence := (_root_.CochainComplex.opEquivalence C).isEquivalence_functor
  have : QuasiIso (E.map b.op) := Waldhausen.quasiIso_cochain_opEquivalence_functor_map _
  have : QuasiIso (E.map c.op) := Waldhausen.quasiIso_cochain_opEquivalence_functor_map _
  have : QuasiIso (E.map d.op) := Waldhausen.quasiIso_cochain_opEquivalence_functor_map _
  have ha := Waldhausen.quasiIso_gluing (h'.op.flip.map E) (h.op.flip.map E)
    (E.map d.op) (E.map b.op) (E.map c.op) (E.map a.op)
    (by simpa only [← E.map_comp, ← op_comp] using congrArg (fun k => E.map k.op) hf.symm)
    (by simpa only [← E.map_comp, ← op_comp] using congrArg (fun k => E.map k.op) hg.symm)
    (by simpa only [← E.map_comp, ← op_comp] using congrArg (fun k => E.map k.op) hi.symm)
    (by simpa only [← E.map_comp, ← op_comp] using congrArg (fun k => E.map k.op) hj.symm)
  exact (Waldhausen.quasiIso_cochain_opEquivalence_functor_map_iff a).mp ha

end Quillen.CochainComplex
