/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.Algebra.Category.FGModuleCat.PrimaryDecomposition
public import Quillen.Aglib.Algebra.Category.FGModuleCat.SmallModelLocalization
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Quillen.Aglib.CategoryTheory.Pi.Equivalence

/-!
# Actual small-model transport of primary decomposition

The supported category is exactly the `smallTorsion R⁰` kernel used by finite-module
localization, with its original lower-universe `SmallModel.{u} (FGModuleCat.{u} R)`.
`smallTorsionEquivalence` restricts the original `equivSmallModel` and preserves the support
inclusion square. It does not replace the supported category by an independently selected model.

The intended upstream module is `Aglib.Algebra.Category.FGModuleCat.PrimarySmallModel`.
Current consumers are Quillen's native Dedekind residue assembly and its explicitly chosen
upper-universe coherent comparison. The compatibility supplier is the designated general
candidate `SmallModelLocalization`, whose source-preserved namespace owns the actual
`Quillen.FiniteModuleLocalization.smallTorsion`; that supplier must migrate together on upstream
admission.

`nativePrimaryEquivalence` has the original lower-universe support category and a primary
family whose objects and homs are in `u`. `chosenPrimaryEquivalence` instead takes one explicit
common model universe `t`, with the corresponding `EssentiallySmall` inputs. The choices
`t = u` and `t = u + 1` are supported; the latter is a chosen upper presentation of the same
original large categories. Identifying a distinct higher-carrier coherent client still requires
its actual categorical comparison. These results do not identify K-groups across universes.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe t u

open CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors ZeroObject

namespace ModuleCat.FiniteLocalization.PrimaryDecomposition

attribute [local instance] Abelian.hasFiniteBiproducts

variable (R : Type u) [CommRing R]

section Noetherian

variable [IsNoetherianRing R]

/-- The original native supported small-model category, with no change of its predicate. -/
abbrev NativeSmallTorsion : Type u :=
  (Quillen.FiniteModuleLocalization.smallTorsion (nonZeroDivisors R)).FullSubcategory

/-- The original support predicate is the inverse image under canonical small-model realization. -/
theorem smallTorsion_inverseImage :
    (torsion (nonZeroDivisors R)).inverseImage (equivSmallModel.{u} (FGModuleCat.{u} R)).inverse =
      Quillen.FiniteModuleLocalization.smallTorsion (nonZeroDivisors R) := by
  funext M
  exact propext (Quillen.FiniteModuleLocalization.smallTorsion_iff (nonZeroDivisors R) M).symm

/-- Restrict the original canonical small-model equivalence to the actual torsion kernels. -/
def smallTorsionEquivalence : NativeSmallTorsion R ≌ TorsionModule R :=
  (equivSmallModel.{u} (FGModuleCat.{u} R)).symm.congrFullSubcategory (smallTorsion_inverseImage R)

instance smallTorsionEquivalence_functor_additive :
    (smallTorsionEquivalence R).functor.Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    exact (equivSmallModel.{u} (FGModuleCat.{u} R)).inverse.map_add

/-- Realization of the actual supported small category is exact. -/
def smallTorsionToOriginalExactFunctor : ExactCategory.ExactFunctor
    (ObjectProperty.subcategoryExactStructure
      (Quillen.FiniteModuleLocalization.smallTorsion (nonZeroDivisors R)))
    (ObjectProperty.subcategoryExactStructure (torsion (nonZeroDivisors R))) where
  toFunctor := (smallTorsionEquivalence R).functor
  map_conflation _ hS := hS.map_of_exact _

/-- The original-to-small supported comparison is exact for the same standard structures. -/
def originalToSmallTorsionExactFunctor : ExactCategory.ExactFunctor
    (ObjectProperty.subcategoryExactStructure (torsion (nonZeroDivisors R)))
    (ObjectProperty.subcategoryExactStructure
      (Quillen.FiniteModuleLocalization.smallTorsion (nonZeroDivisors R))) where
  toFunctor := (smallTorsionEquivalence R).inverse
  additive := (smallTorsionEquivalence R).inverse_additive
  map_conflation _ hS := hS.map_of_exact _

/-- The realized support inclusion is literally the original ambient realization functor. -/
theorem smallTorsionEquivalence_comp_inclusion :
    (smallTorsionEquivalence R).functor ⋙ (torsion (nonZeroDivisors R)).ι =
      (Quillen.FiniteModuleLocalization.smallTorsion (nonZeroDivisors R)).ι ⋙
        (equivSmallModel.{u} (FGModuleCat.{u} R)).inverse := rfl

/-- The inverse comparison also retains the original inclusion and small-model functor. -/
theorem smallTorsionEquivalence_inverse_comp_inclusion :
    (smallTorsionEquivalence R).inverse ⋙
        (Quillen.FiniteModuleLocalization.smallTorsion (nonZeroDivisors R)).ι =
      (torsion (nonZeroDivisors R)).ι ⋙ (equivSmallModel.{u} (FGModuleCat.{u} R)).functor := rfl

/-- The original native support inclusion square uses the canonical ambient counit. -/
def smallTorsionInclusionIso :
    (smallTorsionEquivalence R).functor ⋙ (torsion (nonZeroDivisors R)).ι ⋙
        (equivSmallModel.{u} (FGModuleCat.{u} R)).functor ≅
      (Quillen.FiniteModuleLocalization.smallTorsion (nonZeroDivisors R)).ι :=
  NatIso.ofComponents
    (fun M => (equivSmallModel.{u} (FGModuleCat.{u} R)).counitIso.app M.obj) (by
      intro M N f
      exact (equivSmallModel.{u} (FGModuleCat.{u} R)).counitIso.hom.naturality f.hom)

/-- The original finite-module chosen-model functor with standard abelian exact structures. -/
def finiteModuleToNativeSmallExactFunctor : ExactCategory.ExactFunctor
    (finiteModuleExactStructure R)
    (ExactCategory.abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} R))) where
  toFunctor := (equivSmallModel.{u} (FGModuleCat.{u} R)).functor
  map_conflation _ hS := hS.map_of_exact _

/-- The original support inclusion square, explicitly on the same small exact endpoints. -/
def smallTorsionInclusionExactIso :
    (((smallTorsionToOriginalExactFunctor R).comp
      (ObjectProperty.exactInclusion (torsion (nonZeroDivisors R)))).comp
      (finiteModuleToNativeSmallExactFunctor R)).toFunctor ≅
      (ObjectProperty.exactInclusion
        (Quillen.FiniteModuleLocalization.smallTorsion (nonZeroDivisors R))).toFunctor :=
  smallTorsionInclusionIso R

end Noetherian

/-- The original torsion category admits lower-universe models through its original inclusion. -/
instance torsionModule_essentiallySmall : EssentiallySmall.{u} (TorsionModule R) :=
  essentiallySmall_of_fully_faithful (torsion (nonZeroDivisors R)).ι

/-- Ideal-power primary modules admit lower-universe models through their original inclusion. -/
instance primaryModule_essentiallySmall (I : Ideal R) : EssentiallySmall.{u} (PrimaryModule R I) :=
  essentiallySmall_of_fully_faithful (primaryObjectProperty R I).ι

section Dedekind

variable [IsDedekindDomain R]

section ChosenModels

variable [EssentiallySmall.{t} (TorsionModule R)]
  [∀ p : IsDedekindDomain.HeightOneSpectrum R, EssentiallySmall.{t} (PrimaryModule R p.asIdeal)]

/-- Chosen models at one explicit common universe give the same primary-family equivalence. -/
def chosenPrimaryEquivalence : SmallModel.{t} (TorsionModule R) ≌
    Pi.FiniteCategoryFamily (fun p : IsDedekindDomain.HeightOneSpectrum R =>
      SmallModel.{t} (PrimaryModule R p.asIdeal)) :=
  (equivSmallModel.{t} (TorsionModule R)).symm.trans
    ((finitePrimaryEquivalence R).trans (Pi.finiteFamilySmallModelEquivalence _))

/-- Realization from the explicitly chosen torsion model is exact. -/
def chosenTorsionRealizationExactFunctor : ExactCategory.ExactFunctor
    (ExactCategory.abelianExactStructure (SmallModel.{t} (TorsionModule R)))
    (ObjectProperty.subcategoryExactStructure (torsion (nonZeroDivisors R))) where
  toFunctor := (equivSmallModel.{t} (TorsionModule R)).inverse
  map_conflation _ hS := hS.map_of_exact _

/-- The chosen-model primary comparison uses the original exact functors throughout. -/
def chosenPrimaryExactFunctor : ExactCategory.ExactFunctor
    (ExactCategory.abelianExactStructure (SmallModel.{t} (TorsionModule R)))
    (Pi.finiteCategoryExactStructure (fun p : IsDedekindDomain.HeightOneSpectrum R =>
      SmallModel.{t} (PrimaryModule R p.asIdeal))) :=
  ((chosenTorsionRealizationExactFunctor R).comp (finitePrimaryExactFunctor R)).comp
    (Pi.finiteFamilyToSmallModelExactFunctor _)

@[simp]
theorem chosenPrimaryExactFunctor_toFunctor :
    (chosenPrimaryExactFunctor R).toFunctor = (chosenPrimaryEquivalence R).functor := rfl

instance chosenPrimaryEquivalence_functor_additive :
    (chosenPrimaryEquivalence R).functor.Additive := by
  change (chosenPrimaryExactFunctor R).toFunctor.Additive
  infer_instance

/-- The same chosen-model inverse equivalence is exact. -/
def chosenPrimaryInverseExactFunctor : ExactCategory.ExactFunctor
    (Pi.finiteCategoryExactStructure (fun p : IsDedekindDomain.HeightOneSpectrum R =>
      SmallModel.{t} (PrimaryModule R p.asIdeal)))
    (ExactCategory.abelianExactStructure (SmallModel.{t} (TorsionModule R))) where
  toFunctor := (chosenPrimaryEquivalence R).inverse
  additive := (chosenPrimaryEquivalence R).inverse_additive
  map_conflation _ hS := hS.map_of_exact _

/-- Chosen-model evaluation retains the original primary coordinate and its chosen model map. -/
theorem chosenPrimaryEquivalence_comp_evaluation (p : IsDedekindDomain.HeightOneSpectrum R) :
    (chosenPrimaryEquivalence R).functor ⋙ (Pi.finiteCategoryEvaluation
      (fun q : IsDedekindDomain.HeightOneSpectrum R => SmallModel.{t} (PrimaryModule R q.asIdeal))
      p).toFunctor =
      (equivSmallModel.{t} (TorsionModule R)).inverse ⋙ torsionPrimaryFunctor R p.asIdeal ⋙
        (equivSmallModel.{t} (PrimaryModule R p.asIdeal)).functor := rfl

/-- The original primary-to-chosen-model functor is exact at the declared model universe. -/
def chosenPrimaryModelExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactCategory.ExactFunctor
      (ObjectProperty.subcategoryExactStructure (primaryObjectProperty R p.asIdeal))
      (ExactCategory.abelianExactStructure (SmallModel.{t} (PrimaryModule R p.asIdeal))) where
  toFunctor := (equivSmallModel.{t} (PrimaryModule R p.asIdeal)).functor
  map_conflation _ hS := hS.map_of_exact _

/-- Chosen-model exact evaluation is the original coordinate chain on the same endpoints. -/
theorem chosenPrimaryExactFunctor_comp_evaluation (p : IsDedekindDomain.HeightOneSpectrum R) :
    (chosenPrimaryExactFunctor R).comp (Pi.finiteCategoryEvaluation
      (fun q : IsDedekindDomain.HeightOneSpectrum R =>
        SmallModel.{t} (PrimaryModule R q.asIdeal)) p) =
      ((chosenTorsionRealizationExactFunctor R).comp (torsionPrimaryExactFunctor R p)).comp
        (chosenPrimaryModelExactFunctor R p) := rfl

end ChosenModels

/-- The lower-universe primary family used by the original native number-ring support model. -/
abbrev NativePrimaryFamily : Type u := Pi.FiniteCategoryFamily
  (fun p : IsDedekindDomain.HeightOneSpectrum R => SmallModel.{u} (PrimaryModule R p.asIdeal))

/-- The actual native support category splits into its lower-universe actual primary models. -/
def nativePrimaryEquivalence : NativeSmallTorsion R ≌ NativePrimaryFamily R :=
  (smallTorsionEquivalence R).trans
    ((finitePrimaryEquivalence R).trans (Pi.finiteFamilySmallModelEquivalence _))

/-- The native comparison retains the original support realization and exact primary functors. -/
def nativePrimaryExactFunctor : ExactCategory.ExactFunctor
    (ObjectProperty.subcategoryExactStructure
      (Quillen.FiniteModuleLocalization.smallTorsion (nonZeroDivisors R)))
    (Pi.finiteCategoryExactStructure (fun p : IsDedekindDomain.HeightOneSpectrum R =>
      SmallModel.{u} (PrimaryModule R p.asIdeal))) :=
  ((smallTorsionToOriginalExactFunctor R).comp (finitePrimaryExactFunctor R)).comp
    (Pi.finiteFamilyToSmallModelExactFunctor _)

@[simp]
theorem nativePrimaryExactFunctor_toFunctor :
    (nativePrimaryExactFunctor R).toFunctor = (nativePrimaryEquivalence R).functor := rfl

instance nativePrimaryEquivalence_functor_additive :
    (nativePrimaryEquivalence R).functor.Additive := by
  change (nativePrimaryExactFunctor R).toFunctor.Additive
  infer_instance

/-- The native inverse primary equivalence is exact in the same lower universe. -/
def nativePrimaryInverseExactFunctor : ExactCategory.ExactFunctor
    (Pi.finiteCategoryExactStructure (fun p : IsDedekindDomain.HeightOneSpectrum R =>
      SmallModel.{u} (PrimaryModule R p.asIdeal)))
    (ObjectProperty.subcategoryExactStructure
      (Quillen.FiniteModuleLocalization.smallTorsion (nonZeroDivisors R))) where
  toFunctor := (nativePrimaryEquivalence R).inverse
  additive := (nativePrimaryEquivalence R).inverse_additive
  map_conflation _ hS := hS.map_of_exact _

/-- Native evaluation retains the actual support realization and original primary coordinate. -/
theorem nativePrimaryEquivalence_comp_evaluation (p : IsDedekindDomain.HeightOneSpectrum R) :
    (nativePrimaryEquivalence R).functor ⋙ (Pi.finiteCategoryEvaluation
      (fun q : IsDedekindDomain.HeightOneSpectrum R => SmallModel.{u} (PrimaryModule R q.asIdeal))
      p).toFunctor =
      (smallTorsionEquivalence R).functor ⋙ torsionPrimaryFunctor R p.asIdeal ⋙
        (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).functor := rfl

/-- The original primary inclusion transported to the actual native supported category. -/
def nativePrimaryInclusion (p : IsDedekindDomain.HeightOneSpectrum R) :
    SmallModel.{u} (PrimaryModule R p.asIdeal) ⥤ NativeSmallTorsion R :=
  (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).inverse ⋙ primaryToTorsion R p ⋙
    (smallTorsionEquivalence R).inverse

/-- The chosen lower-universe primary realization is exact. -/
def nativePrimaryRealizationExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactCategory.ExactFunctor
      (ExactCategory.abelianExactStructure (SmallModel.{u} (PrimaryModule R p.asIdeal)))
      (ObjectProperty.subcategoryExactStructure (primaryObjectProperty R p.asIdeal)) where
  toFunctor := (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).inverse
  map_conflation _ hS := hS.map_of_exact _

/-- The transported original primary inclusion is exact on the original native support model. -/
def nativePrimaryInclusionExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactCategory.ExactFunctor
      (ExactCategory.abelianExactStructure (SmallModel.{u} (PrimaryModule R p.asIdeal)))
      (ObjectProperty.subcategoryExactStructure
        (Quillen.FiniteModuleLocalization.smallTorsion (nonZeroDivisors R))) :=
  ((nativePrimaryRealizationExactFunctor R p).comp (primaryToTorsionExactFunctor R p)).comp
    (originalToSmallTorsionExactFunctor R)

@[simp]
theorem nativePrimaryInclusionExactFunctor_toFunctor
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    (nativePrimaryInclusionExactFunctor R p).toFunctor = nativePrimaryInclusion R p := rfl

/-- The native primary inclusion retains the original ambient finite-module inclusion square. -/
theorem nativePrimaryInclusion_comp_support_inclusion
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    nativePrimaryInclusion R p ⋙
        (Quillen.FiniteModuleLocalization.smallTorsion (nonZeroDivisors R)).ι =
      (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).inverse ⋙
        (primaryObjectProperty R p.asIdeal).ι ⋙
        (equivSmallModel.{u} (FGModuleCat.{u} R)).functor := rfl

/-- The original primary-to-lower-model functor is exact. -/
def nativePrimaryModelExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactCategory.ExactFunctor
      (ObjectProperty.subcategoryExactStructure (primaryObjectProperty R p.asIdeal))
      (ExactCategory.abelianExactStructure (SmallModel.{u} (PrimaryModule R p.asIdeal))) where
  toFunctor := (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).functor
  map_conflation _ hS := hS.map_of_exact _

/-- Native exact evaluation is the actual original coordinate chain on the same small endpoints. -/
theorem nativePrimaryExactFunctor_comp_evaluation (p : IsDedekindDomain.HeightOneSpectrum R) :
    (nativePrimaryExactFunctor R).comp (Pi.finiteCategoryEvaluation
      (fun q : IsDedekindDomain.HeightOneSpectrum R =>
        SmallModel.{u} (PrimaryModule R q.asIdeal)) p) =
      ((smallTorsionToOriginalExactFunctor R).comp (torsionPrimaryExactFunctor R p)).comp
        (nativePrimaryModelExactFunctor R p) := rfl

/-- The transported original primary inclusion has its exact original ambient inclusion square. -/
theorem nativePrimaryInclusionExactFunctor_comp_support_inclusion
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    (nativePrimaryInclusionExactFunctor R p).comp (ObjectProperty.exactInclusion
        (Quillen.FiniteModuleLocalization.smallTorsion (nonZeroDivisors R))) =
      ((nativePrimaryRealizationExactFunctor R p).comp
        (ObjectProperty.exactInclusion (primaryObjectProperty R p.asIdeal))).comp
        (finiteModuleToNativeSmallExactFunctor R) := rfl

end Dedekind

end ModuleCat.FiniteLocalization.PrimaryDecomposition
