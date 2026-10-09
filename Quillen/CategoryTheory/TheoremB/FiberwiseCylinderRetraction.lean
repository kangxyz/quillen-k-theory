import Quillen.CategoryTheory.TheoremB.FiberwiseCylinderEquivalence

/-!
# Strict mapping-cylinder retractions over the base

Parameter-preserving homotopy extension turns the chosen fiberwise inverse
of the source inclusion into a strict retraction, without changing the
base map. Its explicit inverse homotopy remains over that base.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.TheoremB

/-- A fiberwise homotopy inverse of the attaching map gives a strict
source retraction over the base, together with an actual inverse homotopy
over the base. -/
theorem mappingCylinder_exists_source_retraction_over
    {A C M T : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
    (base : C ⟶ T) (g : C ⟶ A)
    (H : TopCat.Homotopy (f ≫ g) (𝟙 A)) (K : TopCat.Homotopy (g ≫ f) (𝟙 C))
    (hg : g ≫ f ≫ base = base)
    (hH : ∀ t a, base (f (H (t, a))) = base (f a))
    (hK : ∀ t x, base (K (t, x)) = base x) :
    ∃ r : M ⟶ A, (TopCat.ι₀ ≫ l) ≫ r = 𝟙 A ∧
      r ≫ f ≫ base = TheoremA.mappingCylinderProjection sq ≫ base ∧
        ∃ F : TopCat.Homotopy (r ≫ (TopCat.ι₀ ≫ l)) (𝟙 M),
          ∀ t m, (TheoremA.mappingCylinderProjection sq ≫ base) (F (t, m)) =
            (TheoremA.mappingCylinderProjection sq ≫ base) m := by
  let j := TopCat.ι₀ ≫ l
  let r₀ := mappingCylinderSourceInverse sq g
  let η := mappingCylinderSourceLeftHomotopy sq g H
  have hη : η.h ≫ (f ≫ base) = fst A TopCat.I ≫ f ≫ base := by
    ext ⟨a, t⟩
    exact hH t.down a
  obtain ⟨Q, hQ₀, hQj, hQbase⟩ := mappingCylinderStart_extension_over sq base (f ≫ base)
    r₀ η.h η.ι₀_h (mappingCylinderSourceInverse_over sq base g hg) hη
  let r := TopCat.ι₁ ≫ Q
  have hjr : j ≫ r = 𝟙 A := by
    dsimp [r, j]
    rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hQj, η.ι₁_h]
  have hrbase : r ≫ f ≫ base = TheoremA.mappingCylinderProjection sq ≫ base := by
    dsimp [r]
    simp only [Category.assoc]
    rw [hQbase, ← Category.assoc, TopCat.ι₁_fst, Category.id_comp]
  let R : TopCat.Homotopy r₀ r := TheoremA.homotopyOfCylinder Q hQ₀ rfl
  have hRbase : ∀ t m, base (f (R (t, m))) = (TheoremA.mappingCylinderProjection sq ≫ base) m := by
    intro t m
    exact ConcreteCategory.congr_hom hQbase (m, ULift.up t)
  let F₀ := mappingCylinderSourceRightHomotopy sq g K
  let F : TopCat.Homotopy (r ≫ j) (𝟙 M) := ((TopCat.Homotopy.refl j).comp R.symm).trans F₀
  refine ⟨r, hjr, hrbase, ⟨F, ?_⟩⟩
  intro t m
  simp only [F, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · change (TheoremA.mappingCylinderProjection sq ≫ base) (j (R (σ _, m))) = _
    exact (ConcreteCategory.congr_hom
      (TheoremA.mappingCylinderProjection_start_assoc sq base) _).trans (hRbase _ m)
  · exact mappingCylinderSourceRightHomotopy_over sq base g K hg hK _ m

end Quillen.TheoremB
