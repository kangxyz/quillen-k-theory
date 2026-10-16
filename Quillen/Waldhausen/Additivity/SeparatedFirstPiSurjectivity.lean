/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.SeparatedPairMap

/-!
# Original subdivision representatives cover every original K-class

The actual first separated map is the original forward horizontal endpoint followed by the
original diagonal isomorphism. Its positive homotopy-group map is therefore surjective. Passing
from a homotopy class to a representative uses only quotient induction. No inverse subdivision
map or based inverse homotopy is chosen.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Simplicial Topology
universe u v w
namespace Quillen.Waldhausen.Additivity
variable {C : Type u} [Category.{v} C] (V : Structure C) (n : ℕ)

/-- The actual separated first map is the composite of the two original forward group maps. -/
theorem separatedFirstPiMap_eq_comp :
    piMap n (separatedFirstDeloopingMap V) (separatedFirstDeloopingMap_basepoint V) =
      (diagonalPiEquiv V n).toMonoidHom.comp (subdivisionPiEquiv V n).toMonoidHom := by
  ext a
  refine Quotient.inductionOn a (fun p => ?_)
  rfl

/-- Every original K-class is in the image of the actual based forward separated map. -/
theorem separatedFirstPiMap_surjective :
    Function.Surjective
      (piMap n (separatedFirstDeloopingMap V) (separatedFirstDeloopingMap_basepoint V)) := by
  rw [separatedFirstPiMap_eq_comp]
  exact (diagonalPiEquiv V n).surjective.comp (subdivisionPiMap_surjective V n)

/-- Quotient induction supplies an original subdivision cube, without choosing an inverse map. -/
theorem separatedFirstCube_class_surjective (a : V.K n) :
    ∃ p : GenLoop (Fin (n + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      (subdivisionBasepoint V),
      (⟦genLoopPostcomp (separatedFirstDeloopingMap V)
        (separatedFirstDeloopingMap_basepoint V) p⟧ : V.K n) = a := by
  obtain ⟨a', ha'⟩ := separatedFirstPiMap_surjective V n a
  revert ha'
  refine Quotient.inductionOn a' (fun p hp => ?_)
  exact ⟨p, hp⟩

/-- Equality on the actual forward subdivision representatives determines an original function. -/
theorem separatedFirstCube_funext {Y : Sort w} (f g : V.K n → Y)
    (h : ∀ p : GenLoop (Fin (n + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      (subdivisionBasepoint V),
      f ⟦genLoopPostcomp (separatedFirstDeloopingMap V)
        (separatedFirstDeloopingMap_basepoint V) p⟧ =
      g ⟦genLoopPostcomp (separatedFirstDeloopingMap V)
        (separatedFirstDeloopingMap_basepoint V) p⟧) : f = g := by
  funext a
  obtain ⟨p, hp⟩ := separatedFirstCube_class_surjective V n a
  rw [← hp]
  exact h p

end Quillen.Waldhausen.Additivity
