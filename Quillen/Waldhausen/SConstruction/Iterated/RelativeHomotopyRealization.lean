/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.HomotopyTransport

/-!
# Whole first-level relative homotopies on original realization spaces

The actual original small-model homeomorphisms transport a supplied first-level relative
homotopy back to the original realization spaces. Both homotopy coordinates and the entire
endpoint-and-basepoint union are retained. The endpoint equations are literal map equations;
no equality of induced homotopy-group maps supplies a comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology
universe u v u' v'
namespace Quillen.Waldhausen.IteratedS
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (W : Structure C) (V : Structure D)
  {f g : C(unitInterval × (originalPrespectrum W).space 1, (originalPrespectrum V).space 1)}
  {f' g' : C(unitInterval × W.Delooping, V.Delooping)}
  (J : f.HomotopyRel g {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = (originalPrespectrum W).point 1})
  (hf : ∀ z : unitInterval × W.Delooping,
    V.smallModelDeloopingHomeomorph.symm (f (z.1, W.smallModelDeloopingHomeomorph z.2)) = f' z)
  (hg : ∀ z : unitInterval × W.Delooping,
    V.smallModelDeloopingHomeomorph.symm (g (z.1, W.smallModelDeloopingHomeomorph z.2)) = g' z)

/-- Transport the same whole first-level comparison through the original homeomorphisms. -/
def originalPrespectrumLevelOneRelHomotopy :
    f'.HomotopyRel g' {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = W.kBasepoint} where
  toFun z := V.smallModelDeloopingHomeomorph.symm
    (J (z.1, (z.2.1, W.smallModelDeloopingHomeomorph z.2.2)))
  continuous_toFun := V.smallModelDeloopingHomeomorph.symm.continuous.comp
    (J.continuous.comp (continuous_fst.prodMk (continuous_snd.fst.prodMk
      (W.smallModelDeloopingHomeomorph.continuous.comp continuous_snd.snd))))
  map_zero_left z := (congrArg V.smallModelDeloopingHomeomorph.symm
    (J.apply_zero (z.1, W.smallModelDeloopingHomeomorph z.2))).trans (hf z)
  map_one_left z := (congrArg V.smallModelDeloopingHomeomorph.symm
    (J.apply_one (z.1, W.smallModelDeloopingHomeomorph z.2))).trans (hg z)
  prop' a z hz := by
    have hz' : z.1 = 0 ∨ z.1 = 1 ∨
        W.smallModelDeloopingHomeomorph z.2 = (originalPrespectrum W).point 1 := by
      rcases hz with hz | hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr ((congrArg W.smallModelDeloopingHomeomorph hz).trans
          W.smallModelDeloopingHomeomorph_basepoint))
    exact (congrArg V.smallModelDeloopingHomeomorph.symm (J.eq_fst a hz')).trans (hf z)

/-- Every input and both independent times retain the same literal original first-level map. -/
theorem originalPrespectrumLevelOneRelHomotopy_apply
    (a t : unitInterval) (x : W.Delooping) :
    originalPrespectrumLevelOneRelHomotopy W V J hf hg (a, (t, x)) =
      V.smallModelDeloopingHomeomorph.symm
        (J (a, (t, W.smallModelDeloopingHomeomorph x))) := rfl

end Quillen.Waldhausen.IteratedS
