/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.KTheory.Bass.Iteration
public import Quillen.KTheory.Bass.RightExactness

/-!
# Right exactness through every Bass iteration

The existing ring-indexed Bass recursion preserves pointwise right exact sequences in every
nonnegative iteration index. All maps are the original `iteratedContraction` maps; the original
Laurent quotient square is `iteratedContraction_map_π`. These are group-level results, not a
construction of negative localization boundaries or a comparison with spectral Bass iteration.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Quillen.Bass

variable {F G H : CommRingCat.{u} ⥤ AddCommGrpCat.{v}}

/-- Pointwise surjectivity is retained by the original map in every Bass iteration. -/
lemma iteratedContraction_map_surjective (α : F ⟶ G)
    (hα : ∀ R, Function.Surjective (α.app R)) (n : ℕ) (R : CommRingCat.{u}) :
    Function.Surjective (((iteratedContraction n).map α).app R) := by
  induction n generalizing R with
  | zero => exact hα R
  | succ n ih =>
    exact TwoChart.contractionMap_surjective plus minus ((iteratedContraction n).map α)
      R (ih (laurentFunctor.obj R))

/-- Iterated original maps retain a zero composite of the initial natural transformations. -/
lemma iteratedContraction_map_comp_eq_zero (α : F ⟶ G) (β : G ⟶ H)
    (h : α ≫ β = 0) (n : ℕ) :
    (iteratedContraction n).map α ≫ (iteratedContraction n).map β = 0 := by
  induction n with
  | zero => exact h
  | succ n ih =>
    apply NatTrans.ext
    funext R
    exact TwoChart.contractionMap_comp_eq_zero plus minus ((iteratedContraction n).map α)
      ((iteratedContraction n).map β) R (congrArg (fun γ ↦ γ.app (laurentFunctor.obj R)) ih)

/-- The actual pointwise short complex at any stage of the existing Bass recursion. -/
def iteratedContractionShortComplex (α : F ⟶ G) (β : G ⟶ H)
    (h : α ≫ β = 0) (n : ℕ) (R : CommRingCat.{u}) : ShortComplex AddCommGrpCat.{v} :=
  ShortComplex.mk (((iteratedContraction n).map α).app R)
    (((iteratedContraction n).map β).app R)
    (congrArg (fun γ ↦ γ.app R) (iteratedContraction_map_comp_eq_zero α β h n))

/-- Pointwise exactness and surjectivity give exactness at every original Bass stage. -/
lemma iteratedContractionShortComplex_exact (α : F ⟶ G) (β : G ⟶ H)
    (h : α ≫ β = 0)
    (he : ∀ R, (ShortComplex.mk (α.app R) (β.app R)
      (show α.app R ≫ β.app R = 0 from congrArg (fun γ ↦ γ.app R) h)).Exact)
    (hβ : ∀ R, Function.Surjective (β.app R)) (n : ℕ) (R : CommRingCat.{u}) :
    (iteratedContractionShortComplex α β h n R).Exact := by
  induction n generalizing R with
  | zero => exact he R
  | succ n ih =>
    exact TwoChart.contractionShortComplex_exact plus minus ((iteratedContraction n).map α)
      ((iteratedContraction n).map β) R
      (congrArg (fun γ ↦ γ.app (laurentFunctor.obj R))
        (iteratedContraction_map_comp_eq_zero α β h n))
      (ih (laurentFunctor.obj R))
      (iteratedContraction_map_surjective β hβ n (polynomialFunctor.obj R))

/-- The original endpoint is a cokernel of the original first map in every Bass iteration. -/
def iteratedContractionCokernel (α : F ⟶ G) (β : G ⟶ H)
    (h : α ≫ β = 0)
    (he : ∀ R, (ShortComplex.mk (α.app R) (β.app R)
      (show α.app R ≫ β.app R = 0 from congrArg (fun γ ↦ γ.app R) h)).Exact)
    (hβ : ∀ R, Function.Surjective (β.app R)) (n : ℕ) (R : CommRingCat.{u}) :
    IsColimit (CokernelCofork.ofπ (((iteratedContraction n).map β).app R)
      (congrArg (fun γ ↦ γ.app R) (iteratedContraction_map_comp_eq_zero α β h n))) := by
  have : Epi (iteratedContractionShortComplex α β h n R).g :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (iteratedContraction_map_surjective β hβ n R)
  exact (iteratedContractionShortComplex_exact α β h he hβ n R).gIsCokernel

end Quillen.Bass
