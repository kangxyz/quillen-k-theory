/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.SerreBoundary
public import Quillen.GTheory.SmallModelLocalization
public import Quillen.GTheory.FiniteModules.LocalizationSequence

/-!
# Scalar operations and the original SmallModel localization boundary

The canonical comparison with the standard abelian exact structure is induced
by its actual exact identity functor. Ordinary natural-automorphism compatibility
therefore proves action transport through this precise K-equivalence.
The resulting boundary formula uses the original SmallK source and the actual
kernel support term, retaining the original inverse sign.

The supported scalar automorphism is the restriction of the original lifted
SmallModel scalar automorphism. No linear structure on a chosen model or on the
formal Serre quotient is introduced.

For finite modules, the separate original smallAbelianKEquiv is treated through
its own exact identity comparison. The localization functor's ordinary scalar
compatibility follows from the R-linear mapExtendScalars, giving the formula for
the original finite-module connectingHom and its literal small torsion term.
The target action uses the original ring's scalars through its localization map.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Linear
attribute [local instance] Abelian.hasFiniteBiproducts
universe r w u₁ v₁ u₂ v₂
namespace Quillen.LowDegreeScalarAction.SmallModelBoundary

section StandardComparison
variable (C : Type u₁) [Category.{v₁} C] [Abelian C] [EssentiallySmall.{w} C]

/-- The original standard comparison transports degree-(0,1) action through
its actual exact identity functor. -/
theorem standardKEquiv_kZeroAction (u : Aut (𝟭 (SmallModel.{w} C)))
    (a : (abelianExactStructure C).SmallK.{w} 0) :
    SmallModelLocalization.standardKEquiv C 1
        (IdentityAutomorphism.kZeroAction (abelianExactStructure C).smallModel u a) =
      IdentityAutomorphism.kZeroAction (abelianExactStructure (SmallModel.{w} C)) u
        (SmallModelLocalization.standardKEquiv C 0 a) :=
  ExactNaturality.kZeroAction_natural.{w, w}
    (CategoryTheory.SmallModel.abelianExactComparison.{w} C) u u (fun _ => rfl) a

/-- The original standard comparison transports degree-(1,1) action through
its actual exact identity functor. -/
theorem standardKEquiv_kOneAction (u : Aut (𝟭 (SmallModel.{w} C)))
    (a : (abelianExactStructure C).SmallK.{w} 1) :
    SmallModelLocalization.standardKEquiv C 2
        (IdentityAutomorphism.kOneAction (abelianExactStructure C).smallModel u a) =
      IdentityAutomorphism.kOneAction (abelianExactStructure (SmallModel.{w} C)) u
        (SmallModelLocalization.standardKEquiv C 1 a) :=
  ExactNaturality.kOneAction_natural.{w, w}
    (CategoryTheory.SmallModel.abelianExactComparison.{w} C) u u (fun _ => rfl) a
end StandardComparison

section Restriction
variable {A : Type w} [SmallCategory A] [Abelian A] (P : ObjectProperty A)

/-- Actual restriction of identity automorphisms preserves their group product. -/
def restrictedNatAutHom : Aut (𝟭 A) →* Aut (𝟭 P.FullSubcategory) where
  toFun := SerreBoundary.restrictedNatAut P
  map_one' := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    rfl
  map_mul' u v := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    rfl
end Restriction

section Localization
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))
  [PreservesFiniteLimits F.toFunctor] [PreservesFiniteColimits F.toFunctor]
  [F.toFunctor.IsLocalization F.toFunctor.kernel.isoModSerre]

/-- The original SmallModel boundary has the signed identity-automorphism
formula from ordinary compatibility of the actual chosen-model functor. -/
theorem connectingHom_action (u : Aut (𝟭 (SmallModel.{w} C)))
    (v : Aut (𝟭 (SmallModel.{w} D)))
    (h : ∀ X, (CategoryTheory.SmallModel.functor F.toFunctor).map (u.hom.app X) =
      v.hom.app ((CategoryTheory.SmallModel.functor F.toFunctor).obj X))
    (a : (abelianExactStructure D).SmallK.{w} 1) :
    SmallModelGLocalization.connectingHom F 1
        (IdentityAutomorphism.kOneAction (abelianExactStructure D).smallModel v a) =
      (IdentityAutomorphism.kZeroAction
        (ObjectProperty.subcategoryExactStructure (SmallModelGLocalization.supported F))
        (SerreBoundary.restrictedNatAut (SmallModelGLocalization.supported F) u)
        (SmallModelGLocalization.connectingHom F 0 a))⁻¹ := by
  change SerreLocalization.actualConnectingHom (SmallModelGLocalization.supported F)
      (CategoryTheory.SmallModel.functor F.toFunctor) 1
      (SmallModelLocalization.standardKEquiv D 2
        (IdentityAutomorphism.kOneAction (abelianExactStructure D).smallModel v a)) = _
  rw [standardKEquiv_kOneAction]
  exact SerreBoundary.actualConnectingHom_action (SmallModelGLocalization.supported F) u
    (CategoryTheory.SmallModel.functor F.toFunctor) v h
    (SmallModelLocalization.standardKEquiv D 1 a)

variable (R : Type r) [Ring R] [Linear R C]

/-- The actual supported degree-(0,1) scalar operation, obtained by restricting
the original lifted scalar automorphism to the literal kernel subcategory. -/
def supportedKZeroAction :
    Rˣ →* (SmallModelGLocalization.SupportedK.{w} F 0 →*
      SmallModelGLocalization.SupportedK.{w} F 1) :=
  ScalarUnit.kZeroActionOf.{r, w, w} R
    (ObjectProperty.subcategoryExactStructure (SmallModelGLocalization.supported F))
    ((restrictedNatAutHom (SmallModelGLocalization.supported F)).comp
      (smallModelScalarNatAut R C))

omit [F.toFunctor.IsLocalization F.toFunctor.kernel.isoModSerre] in
/-- The supported operation retains exactly the restricted original automorphism. -/
@[simp] theorem supportedKZeroAction_apply (r : Rˣ)
    (a : SmallModelGLocalization.SupportedK.{w} F 0) :
    supportedKZeroAction F R r a = IdentityAutomorphism.kZeroAction
      (ObjectProperty.subcategoryExactStructure (SmallModelGLocalization.supported F))
      (SerreBoundary.restrictedNatAut (SmallModelGLocalization.supported F)
        (smallModelScalarNatAut R C r)) a := rfl

variable [Linear R D] [F.toFunctor.Linear R]

/-- Scalar compatibility for the original SmallK boundary follows from ordinary
linearity and the actual lifted automorphisms; neither model needs a linear structure. -/
theorem connectingHom_scalar (r : Rˣ) (a : (abelianExactStructure D).SmallK.{w} 1) :
    SmallModelGLocalization.connectingHom F 1
        (ScalarUnit.smallModelKOneAction R (abelianExactStructure D) r a) =
      (supportedKZeroAction F R r (SmallModelGLocalization.connectingHom F 0 a))⁻¹ :=
  connectingHom_action F (smallModelScalarNatAut R C r) (smallModelScalarNatAut R D r)
    (ScalarUnit.smallModelScalarNatAut_map R F r) a
end Localization

section FiniteModules
open scoped ModuleCat.Algebra
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (S : Submonoid R)

/-- The finite-module comparison transports the actual K-zero action through
its displayed exact identity functor. -/
theorem smallAbelianKEquiv_kZeroAction (A : Type u) [CommRing A] [IsNoetherianRing A]
    (v : Aut (𝟭 (SmallModel.{u} (FGModuleCat.{u} A))))
    (a : FiniteModuleLocalization.G A 0) :
    FiniteModuleLocalization.smallAbelianKEquiv A 1
        (IdentityAutomorphism.kZeroAction
          (ModuleCat.finiteModuleExactStructure.{u, u} A).smallModel v a) =
      IdentityAutomorphism.kZeroAction (abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} A)))
        v (FiniteModuleLocalization.smallAbelianKEquiv A 0 a) :=
  ExactNaturality.kZeroAction_natural.{u, u}
    (FiniteModuleLocalization.smallModelToAbelian A) v v (fun _ => rfl) a

/-- The finite-module comparison transports the actual K-one action through
its displayed exact identity functor. -/
theorem smallAbelianKEquiv_kOneAction (A : Type u) [CommRing A] [IsNoetherianRing A]
    (v : Aut (𝟭 (SmallModel.{u} (FGModuleCat.{u} A))))
    (a : FiniteModuleLocalization.G A 1) :
    FiniteModuleLocalization.smallAbelianKEquiv A 2
        (IdentityAutomorphism.kOneAction
          (ModuleCat.finiteModuleExactStructure.{u, u} A).smallModel v a) =
      IdentityAutomorphism.kOneAction (abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} A)))
        v (FiniteModuleLocalization.smallAbelianKEquiv A 1 a) :=
  ExactNaturality.kOneAction_natural.{u, u}
    (FiniteModuleLocalization.smallModelToAbelian A) v v (fun _ => rfl) a

/-- The original finite-module boundary retains its source, actual kernel
support term, and sign under ordinary compatibility of the chosen-model automorphisms. -/
theorem finiteConnectingHom_action (u : Aut (𝟭 (SmallModel.{u} (FGModuleCat.{u} R))))
    (v : Aut (𝟭 (SmallModel.{u} (FGModuleCat.{u} (Localization S)))))
    (h : ∀ X, (FiniteModuleLocalization.smallFunctor S).map (u.hom.app X) =
      v.hom.app ((FiniteModuleLocalization.smallFunctor S).obj X))
    (a : FiniteModuleLocalization.G (Localization S) 1) :
    FiniteModuleLocalization.connectingHom S 1
        (IdentityAutomorphism.kOneAction
          (ModuleCat.finiteModuleExactStructure.{u, u} (Localization S)).smallModel v a) =
      (IdentityAutomorphism.kZeroAction
        (ObjectProperty.subcategoryExactStructure (FiniteModuleLocalization.smallTorsion S))
        (SerreBoundary.restrictedNatAut (FiniteModuleLocalization.smallTorsion S) u)
        (FiniteModuleLocalization.connectingHom S 0 a))⁻¹ := by
  change SerreLocalization.actualConnectingHom (FiniteModuleLocalization.smallTorsion S)
      (FiniteModuleLocalization.smallFunctor S) 1
      (FiniteModuleLocalization.smallAbelianKEquiv (Localization S) 2
        (IdentityAutomorphism.kOneAction
          (ModuleCat.finiteModuleExactStructure.{u, u} (Localization S)).smallModel v a)) = _
  rw [smallAbelianKEquiv_kOneAction]
  exact SerreBoundary.actualConnectingHom_action (FiniteModuleLocalization.smallTorsion S) u
    (FiniteModuleLocalization.smallFunctor S) v h
    (FiniteModuleLocalization.smallAbelianKEquiv (Localization S) 1 a)

omit [IsNoetherianRing R] in
private theorem finiteLocalization_linear :
    (ModuleCat.FiniteLocalization.functor S).Linear R where
  map_smul {M N} f r := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    ext z
    change IsLocalizedModule.mapExtendScalars S (M.obj.localizedModuleMkLinearMap S)
        (N.obj.localizedModuleMkLinearMap S) (Localization S) (r • f.hom.hom) z =
      (algebraMap R (Localization S) r) •
        IsLocalizedModule.mapExtendScalars S (M.obj.localizedModuleMkLinearMap S)
          (N.obj.localizedModuleMkLinearMap S) (Localization S) f.hom.hom z
    rw [map_smul, LinearMap.smul_apply, algebraMap_smul]

/-- The actual finite-module supported scalar operation restricts the original
lifted scalar automorphism to the literal small torsion category. -/
def finiteSupportedKZeroAction :
    Rˣ →* (FiniteModuleLocalization.SupportedG S 0 →*
      FiniteModuleLocalization.SupportedG S 1) :=
  ScalarUnit.kZeroActionOf.{u, u, u} R
    (ObjectProperty.subcategoryExactStructure (FiniteModuleLocalization.smallTorsion S))
    ((restrictedNatAutHom (FiniteModuleLocalization.smallTorsion S)).comp
      (smallModelScalarNatAut R (FGModuleCat.{u} R)))

/-- Ring units satisfy the signed formula for the original finite-module
localization boundary, using the actual localization map on scalar morphisms. -/
theorem finiteConnectingHom_scalar (r : Rˣ)
    (a : FiniteModuleLocalization.G (Localization S) 1) :
    FiniteModuleLocalization.connectingHom S 1
        (ScalarUnit.smallModelKOneAction R
          (ModuleCat.finiteModuleExactStructure.{u, u} (Localization S)) r a) =
      (finiteSupportedKZeroAction S r (FiniteModuleLocalization.connectingHom S 0 a))⁻¹ := by
  let : (FiniteModuleLocalization.exactFunctor S).toFunctor.Linear R :=
    finiteLocalization_linear S
  exact finiteConnectingHom_action S (smallModelScalarNatAut R (FGModuleCat.{u} R) r)
    (smallModelScalarNatAut R (FGModuleCat.{u} (Localization S)) r)
    (ScalarUnit.smallModelScalarNatAut_map R (FiniteModuleLocalization.exactFunctor S) r) a
end FiniteModules

end Quillen.LowDegreeScalarAction.SmallModelBoundary
