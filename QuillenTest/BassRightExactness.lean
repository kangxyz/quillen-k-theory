/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.KTheory.Bass.IterationExactness

/-!
Semantic consumers for right-exact Bass recursion: successive contractions preserve the
original exact maps, and maps out of every iterated endpoint descend uniquely while retaining
the original Laurent-representative equation.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Quillen.Bass.TwoChart

universe u v w

namespace BassRightExactnessConsumers

variable {D : Type u} [Category.{w} D] {P L : D ⥤ D} (p m : P ⟶ L)
  {F G H : D ⥤ AddCommGrpCat.{v}} (α : F ⟶ G) (β : G ⟶ H)
  (h : α ≫ β = 0)
  (he : ∀ R, (ShortComplex.mk (α.app R) (β.app R)
    (show α.app R ≫ β.app R = 0 from congrArg (fun γ ↦ γ.app R) h)).Exact)
  (hβ : ∀ R, Function.Surjective (β.app R))

include h he hβ in
/-- Two genuine quotient steps preserve exactness without a splitting or projectivity premise. -/
theorem two_successive_contractions (R : D) :
    Function.Exact
      ((contractionMap p m (contractionMap p m α)).app R)
      ((contractionMap p m (contractionMap p m β)).app R) := by
  have h' : contractionMap p m α ≫ contractionMap p m β = 0 := by
    apply NatTrans.ext
    funext S
    exact contractionMap_comp_eq_zero p m α β S (congrArg (fun γ ↦ γ.app (L.obj S)) h)
  have he' (S : D) := contractionShortComplex_exact p m α β S
    (congrArg (fun γ ↦ γ.app (L.obj S)) h) (he (L.obj S)) (hβ (P.obj S))
  have hβ' (S : D) := contractionMap_surjective p m β S (hβ (L.obj S))
  have hh := contractionShortComplex_exact p m (contractionMap p m α)
    (contractionMap p m β) R (congrArg (fun γ ↦ γ.app (L.obj R)) h')
    (he' (L.obj R)) (hβ' (P.obj R))
  exact (ShortComplex.ab_exact_iff_function_exact _).mp hh

include hβ in
/-- The twice-contracted endpoint has representatives lifted through the original map. -/
theorem two_successive_surjections (R : D) :
    Function.Surjective ((contractionMap p m (contractionMap p m β)).app R) :=
  contractionMap_surjective p m (contractionMap p m β) R
    (contractionMap_surjective p m β (L.obj R) (hβ (L.obj (L.obj R))))

include h he hβ in
/-- Killing the induced first map gives one unique descent, with the literal Laurent square. -/
theorem actual_unique_descent (R : D) (A : AddCommGrpCat.{v})
    (k : (contraction p m G).obj R ⟶ A)
    (hk : (contractionMap p m α).app R ≫ k = 0) :
    ∃! d : (contraction p m H).obj R ⟶ A,
      (contractionMap p m β).app R ≫ d = k ∧
      β.app (L.obj R) ≫ (contractionπ p m H).app R ≫ d =
        (contractionπ p m G).app R ≫ k := by
  let hc := contractionCokernel p m α β R (congrArg (fun γ ↦ γ.app (L.obj R)) h)
    (he (L.obj R)) (hβ (P.obj R)) (hβ (L.obj R))
  obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hc k hk
  change (contraction p m H).obj R ⟶ A at d
  change (contractionMap p m β).app R ≫ d = k at hd
  refine ⟨d, ⟨hd, ?_⟩, ?_⟩
  · rw [← Category.assoc, ← contractionMap_π, Category.assoc, hd]
  · intro e he
    apply Cofork.IsColimit.hom_ext hc
    exact he.1.trans hd.symm

end BassRightExactnessConsumers

namespace BassIterationExactnessConsumers

open Quillen.Bass

variable {F G H : CommRingCat.{u} ⥤ AddCommGrpCat.{v}}
  (α : F ⟶ G) (β : G ⟶ H) (h : α ≫ β = 0)
  (he : ∀ R, (ShortComplex.mk (α.app R) (β.app R)
    (show α.app R ≫ β.app R = 0 from congrArg (fun γ ↦ γ.app R) h)).Exact)
  (hβ : ∀ R, Function.Surjective (β.app R))

/-- Degree zero of the iterated sequence retains both literal original maps. -/
theorem zero_stage_original (R : CommRingCat.{u}) :
    (iteratedContractionShortComplex α β h 0 R).f = α.app R ∧
      (iteratedContractionShortComplex α β h 0 R).g = β.app R := ⟨rfl, rfl⟩

include h he hβ in
/-- Every successor stage has unique descent compatible with the original Laurent square. -/
theorem all_stage_laurent_descent (n : ℕ) (R : CommRingCat.{u}) (A : AddCommGrpCat.{v})
    (k : ((iteratedContraction (n + 1)).obj G).obj R ⟶ A)
    (hk : ((iteratedContraction (n + 1)).map α).app R ≫ k = 0) :
    ∃! d : ((iteratedContraction (n + 1)).obj H).obj R ⟶ A,
      ((iteratedContraction (n + 1)).map β).app R ≫ d = k ∧
      ((iteratedContraction n).map β).app (laurentFunctor.obj R) ≫
        (contractionπ ((iteratedContraction n).obj H)).app R ≫ d =
          (contractionπ ((iteratedContraction n).obj G)).app R ≫ k := by
  let hc := iteratedContractionCokernel α β h he hβ (n + 1) R
  obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hc k hk
  change ((iteratedContraction (n + 1)).obj H).obj R ⟶ A at d
  change ((iteratedContraction (n + 1)).map β).app R ≫ d = k at hd
  refine ⟨d, ⟨hd, ?_⟩, ?_⟩
  · rw [← Category.assoc, ← iteratedContraction_map_π, Category.assoc, hd]
  · intro e he
    apply Cofork.IsColimit.hom_ext hc
    exact he.1.trans hd.symm

end BassIterationExactnessConsumers
