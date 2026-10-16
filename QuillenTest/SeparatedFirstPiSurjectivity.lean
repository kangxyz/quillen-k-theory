/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.SeparatedFirstPiSurjectivity

/-! # The literal forward separated map and original quotient representatives -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.Waldhausen Quillen.Waldhausen.Additivity
open scoped Simplicial Topology
universe u v w
namespace QuillenTest.SeparatedFirstPiSurjectivity
variable {C : Type u} [Category.{v} C] (V : Structure C)

/-- The complete original forward homomorphism, with its actual basepoint transport. -/
theorem original_forward_map (n : ℕ) :
    piMap n (separatedFirstDeloopingMap V) (separatedFirstDeloopingMap_basepoint V) =
      (diagonalPiEquiv V n).toMonoidHom.comp (subdivisionPiEquiv V n).toMonoidHom :=
  separatedFirstPiMap_eq_comp V n

/-- The prescribed forward map, rather than a selected inverse, is surjective in every degree. -/
theorem original_forward_surjective (n : ℕ) :
    Function.Surjective
      (piMap n (separatedFirstDeloopingMap V) (separatedFirstDeloopingMap_basepoint V)) :=
  separatedFirstPiMap_surjective V n

/-- One-coordinate representatives cover original K-zero through that same actual map. -/
theorem original_degree_zero (a : V.K 0) :
    ∃ p : GenLoop (Fin 1)
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      (subdivisionBasepoint V),
      (⟦genLoopPostcomp (separatedFirstDeloopingMap V)
        (separatedFirstDeloopingMap_basepoint V) p⟧ : V.K 0) = a :=
  separatedFirstCube_class_surjective V 0 a

/-- Equality is concluded only from the displayed hypothesis on every original forward cube. -/
theorem original_descent (n : ℕ) {Y : Sort w} (f g : V.K n → Y)
    (h : ∀ p : GenLoop (Fin (n + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      (subdivisionBasepoint V),
      f ⟦genLoopPostcomp (separatedFirstDeloopingMap V)
        (separatedFirstDeloopingMap_basepoint V) p⟧ =
      g ⟦genLoopPostcomp (separatedFirstDeloopingMap V)
        (separatedFirstDeloopingMap_basepoint V) p⟧) : f = g :=
  separatedFirstCube_funext V n f g h

end QuillenTest.SeparatedFirstPiSurjectivity
