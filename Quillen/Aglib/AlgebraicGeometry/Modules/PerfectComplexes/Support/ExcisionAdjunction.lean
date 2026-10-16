/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.ExtensionByZero

/-!
# Supported extension-by-zero adjunction

For an open immersion whose image together with the auxiliary acyclicity open covers the scheme, the
unchanged extension-by-zero and restriction functors preserve the original supported objects and
exact sequences. Their unit, counit and triangle identities are literal.-/
@[expose] public section

open Quillen.Waldhausen


open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
open Waldhausen
attribute [local instance] Abelian.hasFiniteBiproducts

instance instPreservesFiniteLimitsExtensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  :
    PreservesFiniteLimits (extensionByZero j) := by unfold extensionByZero; infer_instance

instance instPreservesFiniteColimitsExtensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion
  j]
  :
    PreservesFiniteColimits (extensionByZero j) := by unfold extensionByZero; infer_instance

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

/-- Extension by zero on the supported perfect objects under the stated cover condition. -/
def perfectSupportedExtensionByZero : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory ⥤
    (perfectSupported T.ι).FullSubcategory :=
  (perfectSupported T.ι).lift ((perfectSupported (j ⁻¹ᵁ T).ι).ι ⋙ extensionByZero j)
    (fun K => perfectSupported_extensionByZero_of_cover j T hcover K.property)

instance instAdditivePerfectSupportedExtensionByZero : (perfectSupportedExtensionByZero j T
  hcover).Additive := by
  unfold perfectSupportedExtensionByZero
  infer_instance

/-- The exact functor on supported perfect objects induced by extension by zero. -/
def perfectSupportedExactExtensionByZero : CategoryTheory.ExactCategory.ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex U.Modules ℤ))
      (perfectSupported (j ⁻¹ᵁ
      T).ι))
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (perfectSupported T.ι))
      where
  toFunctor := perfectSupportedExtensionByZero j T hcover
  map_conflation S hS := by
    change ((S.map (perfectSupported (j ⁻¹ᵁ T).ι).ι).map (extensionByZero j)).ShortExact
    exact hS.map_of_exact _

/-- The original adjunction unit, with no change to its underlying chain map. -/
def perfectSupportedExcisionUnit : 𝟭 ((perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) ⟶
    perfectSupportedExtensionByZero j T hcover ⋙ perfectSupportedRestrict j T where
  app K := ObjectProperty.homMk ((extensionByZeroAdjunction j).unit.app K.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ ((extensionByZeroAdjunction j).unit.naturality f.hom)

/-- The original adjunction counit, with no change to its underlying chain map. -/
def perfectSupportedExcisionCounit :
    perfectSupportedRestrict j T ⋙ perfectSupportedExtensionByZero j T hcover ⟶
      𝟭 ((perfectSupported T.ι).FullSubcategory) where
  app K := ObjectProperty.homMk ((extensionByZeroAdjunction j).counit.app K.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ ((extensionByZeroAdjunction j).counit.naturality
    f.hom)

/-- The genuine supported adjunction retains both original triangle identities. -/
def perfectSupportedExcisionAdjunction :
    perfectSupportedExtensionByZero j T hcover ⊣ perfectSupportedRestrict j T where
  unit := perfectSupportedExcisionUnit j T hcover
  counit := perfectSupportedExcisionCounit j T hcover
  left_triangle_components K := ObjectProperty.hom_ext _
    ((extensionByZeroAdjunction j).left_triangle_components K.obj)
  right_triangle_components K := ObjectProperty.hom_ext _
    ((extensionByZeroAdjunction j).right_triangle_components K.obj)

end Quillen.PerfectComplexes

end

end
