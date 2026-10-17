/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSectionUnits
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSupportedUnits
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientFiberInclusion
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenModels

/-!
# Actual units with the original intersection support

The lifted forward Laurent unit and actual supported coefficient/inclusion maps retain their
original identity-automorphism preservation equations.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso boundedFlatCoefficientSectionLaurentUnitIso

/-- The original forward Laurent unit on the actual intersection-support native fiber. -/
def boundedFlatCoefficientSupportedFiberLaurentUnitIso (a : Under R) :=
  lift (boundedFlatCoefficientSectionSupported
    (boundedFlatCoefficientFiberSupportOpen f T ((laurentUnderFunctor R).obj a)).ι).ι
    (boundedFlatCoefficientSectionLaurentUnitIso Q a)

theorem fiberMap_preserves_lift {i k : Index R} {U V : Scheme.{u}}
    (j : U ⟶ space i) (j' : V ⟶ space k) [IsOpenImmersion j] [IsOpenImmersion j']
    (η : i ⟶ k) (l : V ⟶ U) (h : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      η)
    (α : 𝟭 (BoundedFlatCoefficientSections i) ≅ 𝟭 (BoundedFlatCoefficientSections i))
    (β : 𝟭 (BoundedFlatCoefficientSections k) ≅ 𝟭 (BoundedFlatCoefficientSections k))
    (hαβ : Preserves (boundedFlatCoefficientSectionsMap η) α β) :
    Preserves (boundedFlatCoefficientSupportedSectionsMap j j' η l h)
      (lift (boundedFlatCoefficientSectionSupported j).ι α)
      (lift (boundedFlatCoefficientSectionSupported j').ι β) := by
  intro S
  apply ObjectProperty.hom_ext
  change (boundedFlatCoefficientSectionsMap η).map
    ((lift (boundedFlatCoefficientSectionSupported j).ι α).hom.app S).hom =
    ((lift (boundedFlatCoefficientSectionSupported j').ι β).hom.app
      ((boundedFlatCoefficientSupportedSectionsMap j j' η l h).obj S)).hom
  rw [show ((lift (boundedFlatCoefficientSectionSupported j).ι α).hom.app S).hom =
    α.hom.app S.obj from map_lift_hom (boundedFlatCoefficientSectionSupported j).ι α S,
    show ((lift (boundedFlatCoefficientSectionSupported j').ι β).hom.app
      ((boundedFlatCoefficientSupportedSectionsMap j j' η l h).obj S)).hom =
      β.hom.app ((boundedFlatCoefficientSectionsMap η).obj S.obj) from
      map_lift_hom (boundedFlatCoefficientSectionSupported j').ι β _]
  exact hαβ S.obj

/-- Actual coefficient reindexing preserves every original forward fiber-unit component. -/
theorem boundedFlatCoefficientSupportedFiberLaurentUnitIso_coefficient
    {a b : Under R} (g : a ⟶ b) :
    Preserves ((boundedFlatCoefficientSupportedFiberModelFunctor f T).map
      ((laurentUnderFunctor R).map g)).functor
      (boundedFlatCoefficientSupportedFiberLaurentUnitIso f T a)
      (boundedFlatCoefficientSupportedFiberLaurentUnitIso f T b) :=
  fiberMap_preserves_lift
    (boundedFlatCoefficientFiberSupportOpen f T ((laurentUnderFunctor R).obj a)).ι
    (boundedFlatCoefficientFiberSupportOpen f T ((laurentUnderFunctor R).obj b)).ι
    (𝟙 (op Q), (laurentUnderFunctor R).map g)
    (boundedFlatCoefficientFiberSupportPairMap f T ((laurentUnderFunctor R).map g)).hom.left
    (Arrow.w (boundedFlatCoefficientFiberSupportPairMap f T ((laurentUnderFunctor R).map g)).hom)
    _ _ (boundedFlatCoefficientSectionLaurentUnitIso_coefficient Q g)

theorem supportedFiberForget_unit_preserves (a : Under R)
    (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves (boundedFlatCoefficientSupportedFiberForget f T a)
      (boundedFlatCoefficientSupportSectionUnitIso (boundedFlatCoefficientFiberSupportOpen f T a).ι
        r)
      (boundedFlatCoefficientSupportSectionUnitIso (boundedFlatCoefficientSupportOpen Q T a).ι r) :=
        by
  intro S
  apply ObjectProperty.hom_ext
  change ((boundedFlatCoefficientSupportSectionUnitIso
    (boundedFlatCoefficientFiberSupportOpen f T a).ι r).hom.app S).hom =
    ((boundedFlatCoefficientSupportSectionUnitIso
      (boundedFlatCoefficientSupportOpen Q T a).ι r).hom.app
      ((boundedFlatCoefficientSupportedFiberForget f T a).obj S)).hom
  rw [boundedFlatCoefficientSupportSectionUnitIso_hom,
    boundedFlatCoefficientSupportSectionUnitIso_hom]
  rfl

end Quillen.PerfectComplexes

end

end
