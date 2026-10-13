/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.StableLocalization
public import Quillen.Topology.Prespectrum.HomotopyLoop

/-!
# Equality in the coherent homotopy category

Full coherent based homotopy is already an equivalence relation compatible with both compositions.
Consequently the existing categorical quotient identifies two original maps exactly when there is
an actual whole coherent homotopy. This concerns the homotopy quotient before stable localization.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace Quillen.LoopPrespectrum

instance : Congruence coherentHomotopyRelation.{u} where
  comp_left f := fun ⟨H⟩ ↦ ⟨H.precomp f⟩
  comp_right f := fun ⟨H⟩ ↦ ⟨H.postcomp f⟩
  equivalence :=
    { refl := fun f ↦ ⟨Homotopy.refl f⟩
      symm := fun ⟨H⟩ ↦ ⟨H.symm⟩
      trans := fun ⟨H⟩ ⟨K⟩ ↦ ⟨H.trans K⟩ }

instance : coherentHomotopyQuotient.{u}.Full :=
  CategoryTheory.Quotient.full_functor coherentHomotopyRelation

/-- Equality of original arrows in the homotopy quotient is witnessed by a whole coherent
homotopy, rather than only equality on homotopy groups. -/
theorem coherentHomotopyQuotient_map_eq_iff {E F : LoopPrespectrum.{u}} (f g : E ⟶ F) :
    coherentHomotopyQuotient.map f = coherentHomotopyQuotient.map g ↔ Nonempty (Homotopy f g) :=
  CategoryTheory.Quotient.functor_map_eq_iff coherentHomotopyRelation f g

end Quillen.LoopPrespectrum
