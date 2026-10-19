/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.Empty
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedModels

/-!
# The original support-forgetful Model isomorphism for an empty open

When the actual open source has no points, every original evaluated complex is
acyclic there. The original support inclusion is therefore an isomorphism of the
existing Waldhausen Models. Its inverse retains every original global section,
map, and chosen zero, adding only the proved support property. Exactness is
proved using the reverse inclusion of the original geometric full subcategories;
in particular their admissible quotients retain the same support condition.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Complex
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} [IsEmpty U]
    (j : U ⟶ X.unop) [IsOpenImmersion j]

/-- Every original global section is supported on the complement of the empty open. -/
theorem supported_of_isEmpty (S : globalModel.obj X) : supported j S :=
  restrict_acyclic_of_isEmpty j _

/-- The support inverse retains the original section and adds its proved support property. -/
def emptySupportedLift : globalModel.obj X ⥤ (supported j).FullSubcategory :=
  (supported j).lift (𝟭 _) (supported_of_isEmpty j)

/-- The original support inclusion has this literal section-preserving inverse. -/
def emptySupportedEquivalence : (supported j).FullSubcategory ≌ globalModel.obj X where
  functor := (supported j).ι
  inverse := emptySupportedLift j
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := by cat_disch

/-- The evaluated inverse is exact for the original supported geometric classes. -/
theorem emptySupportedLift_evaluation_exact :
    IsExact (globalModel.obj X).waldhausen.cof (globalModel.obj X).waldhausen.weq
      (boundedFlatPerfectSupportedWaldhausen j).cof
      (boundedFlatPerfectSupportedWaldhausen j).weq
      (emptySupportedLift j ⋙ supportedEvaluation j) := by
  let h : boundedFlatPerfect X.unop ≤ boundedFlatPerfectSupported j :=
    fun K hK => ⟨hK, restrict_acyclic_of_isEmpty j K⟩
  have he := (globalEvaluation_exact X).comp
    (subcategoryInclusion_exact _ _ h)
  exact he

/-- The literal inverse is exact for the unchanged global and supported Waldhausen structures. -/
theorem emptySupportedLift_exact :
    IsExact (globalModel.obj X).waldhausen.cof (globalModel.obj X).waldhausen.weq
      (supportedWaldhausen j).cof (supportedWaldhausen j).weq
      (emptySupportedLift j) where
  zero hz := IsZero.of_full_of_faithful_of_isZero (supportedEvaluation j) _
    ((emptySupportedLift_evaluation_exact j).zero hz)
  cofibration f hf := (emptySupportedLift_evaluation_exact j).cofibration f hf
  weak f hf := (emptySupportedLift_evaluation_exact j).weak f hf
  pushout hi hp := IsPushout.of_map_of_faithful (supportedEvaluation j)
    ((emptySupportedLift_evaluation_exact j).pushout hi hp)

/-- The exact inverse preserves the original chosen global zero literally. -/
def emptySupportedInverse : globalModel.obj X ⟶ supportedModel j where
  functor := emptySupportedLift j
  exact := emptySupportedLift_exact j
  zero := by apply ObjectProperty.FullSubcategory.ext; rfl

/-- Forgetting empty-open support and restoring its proved property is literally identity. -/
theorem supportedForget_emptySupportedInverse :
    supportedForget j ≫ emptySupportedInverse j = 𝟙 (supportedModel j) := by
  apply Model.Hom.ext
  rfl

/-- Adding the proved empty-open support property and forgetting it is literally identity. -/
theorem emptySupportedInverse_supportedForget :
    emptySupportedInverse j ≫ supportedForget j = 𝟙 (globalModel.obj X) := by
  apply Model.Hom.ext
  rfl

/-- The original support-forgetful arrow is an actual isomorphism of the existing Models. -/
def emptySupportedModelIso : supportedModel j ≅ globalModel.obj X where
  hom := supportedForget j
  inv := emptySupportedInverse j
  hom_inv_id := supportedForget_emptySupportedInverse j
  inv_hom_id := emptySupportedInverse_supportedForget j

/-- The forward Model isomorphism is the original support-forgetful arrow. -/
theorem emptySupportedModelIso_hom :
    (emptySupportedModelIso j).hom = supportedForget j := rfl

/-- Bottom-open support gives the same actual support-forgetful Model isomorphism. -/
def bottomSupportedModelIso (X : Scheme.{u}ᵒᵖ) :
    supportedModel (X := X) (⊥ : X.unop.Opens).ι ≅ globalModel.obj X :=
  emptySupportedModelIso (⊥ : X.unop.Opens).ι

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
