/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Abelian
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
public import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Exact localizations descend to genuine small models

Conjugating an actual exact localization by the chosen small-model equivalences
preserves its Serre-localization theorem. The kernel is still the actual inverse
image of zero under the conjugated functor. This construction is the underlying
functor used by `ExactFunctor.smallModel`, so its canonical K-map is retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace Quillen.SmallModelLocalization
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  (F : C ⥤ D)

/-- Transport an actual functor through the chosen small-model equivalences. -/
def functor : SmallModel.{w} C ⥤ SmallModel.{w} D :=
  ((equivSmallModel C).inverse ⋙ F) ⋙ (equivSmallModel D).functor

instance functor_preservesFiniteLimits [PreservesFiniteLimits F] :
    PreservesFiniteLimits (functor F) := by dsimp [functor]; infer_instance

instance functor_preservesFiniteColimits [PreservesFiniteColimits F] :
    PreservesFiniteColimits (functor F) := by dsimp [functor]; infer_instance

instance functor_additive [F.Additive] : (functor F).Additive := by
  dsimp [functor]
  infer_instance

/-- The genuine source small-model equivalence commutes with transported F. -/
def comparison : (equivSmallModel C).functor ⋙ functor F ≅ F ⋙ (equivSmallModel D).functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (equivSmallModel C).unitIso.symm _ ≪≫ Functor.leftUnitor _) _

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Actual Serre localization remains actual Serre localization after shrinking. -/
instance functor_isLocalization [F.IsLocalization F.kernel.isoModSerre] :
    (functor F).IsLocalization (functor F).kernel.isoModSerre := by
  let L := F ⋙ (equivSmallModel.{w} D).functor
  have hinv : (functor F).kernel.isoModSerre.IsInvertedBy (functor F) := by
    rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
    intro X Y f hf
    exact hf
  apply Functor.IsLocalization.of_equivalence_source L F.kernel.isoModSerre
    (functor F) (functor F).kernel.isoModSerre (equivSmallModel C)
    ?_ hinv (comparison F)
  have hi : F.kernel.isoModSerre.IsInvertedBy ((equivSmallModel C).functor ⋙ functor F) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _ (comparison F)).2
      (Localization.inverts L F.kernel.isoModSerre)
  intro X Y f hf
  apply MorphismProperty.le_isoClosure
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  exact hi f hf

omit [Abelian C] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The kernel on the small model is the original kernel evaluated on the
actual represented object; no replacement support property is introduced. -/
theorem kernel_iff (M : SmallModel.{w} C) :
    (functor F).kernel M ↔ F.kernel ((equivSmallModel C).inverse.obj M) := by
  change IsZero ((equivSmallModel D).functor.obj (F.obj ((equivSmallModel C).inverse.obj M))) ↔
    IsZero (F.obj ((equivSmallModel C).inverse.obj M))
  exact ⟨fun h ↦ IsZero.of_full_of_faithful_of_isZero _ _ h, fun h ↦ Functor.map_isZero _ h⟩

end Quillen.SmallModelLocalization

namespace Quillen.SmallModelLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
variable (C : Type u₁) [Category.{v₁} C] [Abelian C] [EssentiallySmall.{w} C]

/-- The identity exact functor between the proved-equal transported and
standard abelian exact structures on the chosen small model. -/
def standardExactFunctor : ExactFunctor (abelianExactStructure C).smallModel
    (abelianExactStructure (SmallModel.{w} C)) where
  toFunctor := 𝟭 _
  map_conflation _ h := by
    rw [abelianExactStructure_smallModel] at h
    exact h

instance standardExactFunctor_isEquivalence :
    (standardExactFunctor.{w} C).toFunctor.IsEquivalence := inferInstanceAs (𝟭 _).IsEquivalence

instance standardExactFunctor_mapQ_isEquivalence :
    (standardExactFunctor.{w} C).mapQ.IsEquivalence := by
  apply ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N f hf
    rw [abelianExactStructure_smallModel]
    exact hf
  · intro M N f hf
    rw [abelianExactStructure_smallModel]
    exact hf

/-- The canonical identity-induced comparison with standard abelian K-theory
of the chosen small model. -/
def standardKEquiv (n : ℕ) : (abelianExactStructure C).SmallK n ≃*
    (abelianExactStructure (SmallModel.{w} C)).K n :=
  (standardExactFunctor C).KEquivOfMapQIsEquivalence n

variable {C} {D : Type u₂} [Category.{v₂} D] [Abelian D] [EssentiallySmall.{w} D]

/-- The same canonical small-model functor, with the equal standard abelian
exact structures instead of the transported structures. -/
def standardFunctor (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D)) :
    ExactFunctor (abelianExactStructure (SmallModel.{w} C))
      (abelianExactStructure (SmallModel.{w} D)) where
  toFunctor := F.smallModel.toFunctor
  map_conflation S h := by
    have hs : (abelianExactStructure C).smallModel.conflation S := by
      rwa [abelianExactStructure_smallModel]
    have ht := F.smallModel.map_conflation S hs
    exact (congrArg (fun E : ExactStructure (SmallModel.{w} D) =>
      E.conflation (S.map F.smallModel.toFunctor)) (abelianExactStructure_smallModel D)).mp ht

/-- The standard comparison retains exactly the original canonical
`smallKMap`, rather than an unrelated isomorphism of groups. -/
theorem smallKMap_comparison
    (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D)) (n : ℕ) :
    (standardKEquiv D n).toMonoidHom.comp (F.smallKMap n) =
      ((standardFunctor F).KMap n).comp (standardKEquiv C n).toMonoidHom := by
  change ((standardExactFunctor D).KMap n).comp (F.smallModel.KMap n) =
    ((standardFunctor F).KMap n).comp ((standardExactFunctor C).KMap n)
  rw [← ExactFunctor.KMap_comp, ← ExactFunctor.KMap_comp]
  rfl

end Quillen.SmallModelLocalization
