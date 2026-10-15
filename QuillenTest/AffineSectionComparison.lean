/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineRestrictionSections

/-! # Original affine section comparison maps

These consumers expose pure tensors, actual geometric units and inverse comparison maps.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ChangeOfRings
namespace QuillenTest.AffineSectionComparison

open Quillen
open AlgebraicGeometry.Scheme.Modules
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- An original scalar-unit pure tensor maps to the original geometric pullback unit section. -/
theorem pullback_unit_section (M : (Spec R).Modules) [M.IsQuasicoherent]
    (x : moduleSpecΓFunctor.obj M) :
    (affinePullbackGlobalSectionsIso φ M).hom ((1 : S) ⊗ₜ[R,φ.hom] x) =
      ((pushforwardGlobalSectionsIso φ).hom.app
        ((Scheme.Modules.pullback (Spec.map φ)).obj M))
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) x) :=
  ConcreteCategory.congr_hom (affinePullbackGlobalSectionsIso_unit φ M) x

/-- The inverse returns the original scalar adjunction unit from its geometric counterpart. -/
theorem pullback_inverse_unit (M : (Spec R).Modules) [M.IsQuasicoherent] :
    moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
      (pushforwardGlobalSectionsIso φ).hom.app
          ((Scheme.Modules.pullback (Spec.map φ)).obj M) ≫
        (ModuleCat.restrictScalars φ.hom).map (affinePullbackGlobalSectionsIso φ M).inv =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (moduleSpecΓFunctor.obj M) := by
  rw [← Category.assoc, ← affinePullbackGlobalSectionsIso_unit]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

/-- Actual restriction of a section is the negative or positive scalar unit as specified by φ. -/
theorem restriction_unit_section [IsOpenImmersion (Spec.map φ)]
    (M : (Spec R).Modules) [M.IsQuasicoherent] (x : moduleSpecΓFunctor.obj M) :
    (affineRestrictGlobalSectionsIso φ M).hom ((1 : S) ⊗ₜ[R,φ.hom] x) =
      ((pushforwardGlobalSectionsIso φ).hom.app (M.restrict (Spec.map φ)))
        (moduleSpecΓFunctor.map ((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app M) x) :=
  ConcreteCategory.congr_hom (affineRestrictGlobalSectionsIso_unit φ M) x

/-- Every actual restricted section is recovered after inverse and forward comparison. -/
theorem restriction_roundtrip [IsOpenImmersion (Spec.map φ)]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (x : moduleSpecΓFunctor.obj (M.restrict (Spec.map φ))) :
    (affineRestrictGlobalSectionsIso φ M).hom
      ((affineRestrictGlobalSectionsIso φ M).inv x) = x :=
  Iso.inv_hom_id_apply _ x

end QuillenTest.AffineSectionComparison
