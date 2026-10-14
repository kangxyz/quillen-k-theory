/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Topology.Prespectrum.NativeHomotopyCells

/-! Exact cell formulas for the original pasted comparison and homotopy-pushout cylinder map. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum
variable {E F E' F' E'' F'' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (h : E'' ⟶ F'')
  (a : E ⟶ E') (b : F ⟶ F') (c : E' ⟶ E'') (d : F' ⟶ F'')
  (H : Homotopy (f ≫ b) (a ≫ g)) (K : Homotopy (g ≫ d) (c ≫ h))

/-- The actual first pasted half retains H followed by d, including all endpoint casts. -/
theorem coneSquarePasted_lower_cell (n : ℕ) (s : unitInterval) (x : E.space n) :
    (coneSquarePastedHomotopy f g h a b c d H K).level n (lower s, x) =
      d.map n (H.level n (s, x)) :=
  Homotopy.trans_lower_cell (H.postcomp d)
    ((Homotopy.precomp a K).cast (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)
    n s x

/-- The actual second pasted half retains a followed by K, including its shared initial point. -/
theorem coneSquarePasted_upper_cell (n : ℕ) (s : unitInterval) (x : E.space n) :
    (coneSquarePastedHomotopy f g h a b c d H K).level n (upper s, x) =
      K.level n (s, a.map n x) :=
  Homotopy.trans_upper_cell (H.postcomp d)
    ((Homotopy.precomp a K).cast (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)
    n s x

namespace HomotopyPushout
variable {A B C A' B' C' : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (Hf : Homotopy (f ≫ b) (a ≫ f')) (Hg : Homotopy (g ≫ c) (a ≫ g'))

/-- The whole first cylinder cell is the supplied original first square. -/
theorem mapOfHomotopies_lower_cell (n : ℕ) (t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n (cylinder f g n (lower t, x)) =
      (inl f' g').map n (Hf.level n (t, x)) :=
  Homotopy.trans_lower_cell (Hf.postcomp (inl f' g'))
    ((Homotopy.precomp a (glue f' g')).trans (Hg.symm.postcomp (inr f' g'))) n t x

/-- The middle quarter is precisely the original target cylinder after the overlap map. -/
theorem mapOfHomotopies_middle_cell (n : ℕ) (t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n
      (cylinder f g n (upper (lower t), x)) = cylinder f' g' n (t, a.map n x) :=
  (Homotopy.trans_upper_cell (Hf.postcomp (inl f' g'))
    ((Homotopy.precomp a (glue f' g')).trans (Hg.symm.postcomp (inr f' g'))) n (lower t) x).trans
    (Homotopy.trans_lower_cell (Homotopy.precomp a (glue f' g'))
      (Hg.symm.postcomp (inr f' g')) n t x)

/-- The final quarter is exactly the original reversed second square, in the other chart. -/
theorem mapOfHomotopies_upper_cell (n : ℕ) (t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n
      (cylinder f g n (upper (upper t), x)) =
      (inr f' g').map n (Hg.level n (unitInterval.symm t, x)) :=
  (Homotopy.trans_upper_cell (Hf.postcomp (inl f' g'))
    ((Homotopy.precomp a (glue f' g')).trans (Hg.symm.postcomp (inr f' g'))) n (upper t) x).trans
    (Homotopy.trans_upper_cell (Homotopy.precomp a (glue f' g'))
      (Hg.symm.postcomp (inr f' g')) n t x)

end HomotopyPushout
end Quillen.LoopPrespectrum
