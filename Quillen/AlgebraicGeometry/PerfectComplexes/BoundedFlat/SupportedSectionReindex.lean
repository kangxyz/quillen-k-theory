/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSections

/-!
# Literal identity and composition for original supported coefficient maps

The support proofs restrict existing section reindexing without changing its objects or arrows.
Consequently the actual supported coefficient maps satisfy strict identity and composition laws,
including the specified original open-side maps of their squares.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Quillen.CategoryTheory.StrictSections
variable {R S T : CommRingCat.{u}} {U V W : Scheme.{u}}

private theorem supported_lift_congr {C : Type*} [Category* C] {D : Type*} [Category* D]
    (P : ObjectProperty D) {F G : C ⥤ D} (h : F = G)
    (hF : ∀ x, P (F.obj x)) (hG : ∀ x, P (G.obj x)) : P.lift F hF = P.lift G hG := by
  subst h
  rfl

/-- Restriction along the original identity square is literally the identity functor. -/
theorem boundedFlatAffineSupportedSectionsMap_id
    (j : U ⟶ Spec R) [IsOpenImmersion j]
    (h : 𝟙 U ≫ j = j ≫ Spec.map (𝟙 R)) :
    boundedFlatAffineSupportedSectionsMap j j (𝟙 R) (𝟙 U) h =
      𝟭 (BoundedFlatAffineSupportedSections j) := by
  change (boundedFlatAffineSectionSupported j).lift
    ((boundedFlatAffineSectionSupported j).ι ⋙ boundedFlatAffineSectionsMap (𝟙 R)) _ =
      (boundedFlatAffineSectionSupported j).lift (boundedFlatAffineSectionSupported j).ι _
  apply supported_lift_congr
  exact congrArg (fun F ↦ (boundedFlatAffineSectionSupported j).ι ⋙ F)
    (underCocartesianReindex_id boundedFlatAffineProjection R)

/-- Original supported coefficient reindexing composes strictly through the actual open maps. -/
theorem boundedFlatAffineSupportedSectionsMap_comp
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) (j'' : W ⟶ Spec T)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (f : R ⟶ S) (g : S ⟶ T) (l : V ⟶ U) (m : W ⟶ V)
    (hf : l ≫ j = j' ≫ Spec.map f) (hg : m ≫ j' = j'' ≫ Spec.map g)
    (hfg : (m ≫ l) ≫ j = j'' ≫ Spec.map (f ≫ g)) :
    boundedFlatAffineSupportedSectionsMap j j'' (f ≫ g) (m ≫ l) hfg =
      boundedFlatAffineSupportedSectionsMap j j' f l hf ⋙
        boundedFlatAffineSupportedSectionsMap j' j'' g m hg := by
  change (boundedFlatAffineSectionSupported j'').lift
    ((boundedFlatAffineSectionSupported j).ι ⋙ boundedFlatAffineSectionsMap (f ≫ g)) _ =
      (boundedFlatAffineSectionSupported j'').lift
        ((boundedFlatAffineSectionSupported j).ι ⋙ boundedFlatAffineSectionsMap f ⋙
          boundedFlatAffineSectionsMap g) _
  apply supported_lift_congr
  exact congrArg (fun F ↦ (boundedFlatAffineSectionSupported j).ι ⋙ F)
    (underCocartesianReindex_comp boundedFlatAffineProjection f g)

end Quillen.PerfectComplexes
