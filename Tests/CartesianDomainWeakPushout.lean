/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

import Quillen.CategoryTheory.TheoremB.CartesianDomainWeakPushout

/-!
# General weak fixed-target domain descent consumer

Both source and base pushout diagrams may vary. The corner hypotheses are
weakness of their original canonical comparisons, and the conclusion retains
the original point and entire constant path of the prescribed total map.
-/
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open Quillen Quillen.CartesianDomainPushout
universe u
variable {A B C P A' B' C' P' E T : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ P} {j : C ⟶ P}
  {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ P'} {j' : C' ⟶ P'}
  (sq : IsPushout f g i j) (sq' : IsPushout f' g' i' j')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (p : P ⟶ P')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
  (wi : i ≫ p = b ≫ i') (wj : j ≫ p = c ≫ j')
  (q : E ⟶ T) (s : P' ⟶ T) (t : P ⟶ E) (w : t ≫ q = p ≫ s)

example (hf : TheoremA.homotopyExtensionProperty f)
    (hf' : TheoremA.homotopyExtensionProperty f')
    (hA : IsWeakHomotopyEquivalence (comparisonA a b p wf wi q s t w).hom)
    (hB : IsWeakHomotopyEquivalence (comparisonB b p wi q s t w).hom)
    (hC : IsWeakHomotopyEquivalence (comparisonC c p wj q s t w).hom) :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison q.hom s.hom p.hom t.hom (congrArg TopCat.Hom.hom w)) :=
  comparison_isWeakHomotopyEquivalence sq sq' a b c p wf wg wi wj q s t w hf hf' hA hB hC

example (x : P) :
    ((totalComparison p q s t w) x).val =
      (p x,t x,ContinuousMap.const unitInterval (s (p x))) := rfl
