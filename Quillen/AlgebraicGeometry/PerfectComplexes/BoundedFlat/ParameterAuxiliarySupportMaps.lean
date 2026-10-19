/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedPairDiagram
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Pairs

/-! # Original parameter support enlargement and supported restriction

The three original supported Models vanish on the union, the auxiliary open,
and its inverse image. Their maps are induced by actual open-pair squares.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
namespace ParameterAuxiliarySupport
attribute [local irreducible] globalModel

/-- The original product map in the fixed factor, without an openness assumption. -/
def productMap {X Y : Scheme.{u}} (g : X ⟶ Y) :
    baseProductFunctor (toIntegerBase X) ⟶ baseProductFunctor (toIntegerBase Y) :=
  baseProductTransformation _ _ g (toIntegerBase_naturality g)

/-- Product maps preserve the actual commutative square. -/
theorem productMap_square {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) (S : Scheme.{u}) :
    (productMap g.hom.left).app S ≫
        (GlobalSupportedParameter.openTransformation B.obj.hom).app S =
      (GlobalSupportedParameter.openTransformation A.obj.hom).app S ≫
        (productMap g.hom.right).app S := by
  dsimp only [productMap, GlobalSupportedParameter.openTransformation,
    baseProductTransformation, baseProductFunctor]
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- An original open-pair square acts at every genuine scheme parameter. -/
def pairTransformation {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    GlobalSupportedParameter.pairs A.obj.hom ⟶
      GlobalSupportedParameter.pairs B.obj.hom where
  app S := ObjectProperty.homMk (Arrow.homMk
    ((productMap g.hom.left).app S) ((productMap g.hom.right).app S)
    (productMap_square g S))
  naturality S T h := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact (productMap g.hom.left).naturality h
    · exact (productMap g.hom.right).naturality h

/-- The supported map is the original exact open-pair pullback. -/
def supportedMap {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    ParameterModels.supported B.obj.hom ⟶ ParameterModels.supported A.obj.hom :=
  Functor.whiskerRight (NatTrans.op (pairTransformation g)) pairSupported

/-- The ambient map uses the same original product pullback. -/
def ambientMap {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ParameterModels.ambient Y ⟶ ParameterModels.ambient X :=
  Functor.whiskerRight (NatTrans.op (productMap g)) globalModel

/-- Every supported component retains the literal original underlying functor. -/
theorem supportedMap_functor {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)
    (S : Scheme.{u}ᵒᵖ) :
    ((supportedMap g).app S).functor =
      supportedPairReindex ((pairTransformation g).app S.unop) := rfl

/-- The existing selected supported zero is preserved, with no new zero choice. -/
theorem supportedMap_zero {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)
    (S : Scheme.{u}ᵒᵖ) :
    ((supportedMap g).app S).functor.obj
        ((ParameterModels.supported B.obj.hom).obj S).waldhausen.zero =
      ((ParameterModels.supported A.obj.hom).obj S).waldhausen.zero :=
  ((supportedMap g).app S).zero

/-- Forgetting support retains the full original product pullback square. -/
theorem supportedMap_forget {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    supportedMap g ≫ ParameterModels.forget A.obj.hom =
      ParameterModels.forget B.obj.hom ≫ ambientMap g.hom.right := by
  apply NatTrans.ext
  funext S
  exact supportedPairModelMap_forget ((pairTransformation g).app S.unop)

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The source acyclicity open is the original union. -/
abbrev unionOpen : Q.Opens := T ⊔ f.opensRange

/-- The target acyclicity open is the literal inverse image. -/
abbrev inverseOpen : P.Opens := f ⁻¹ᵁ T

/-- Original sections vanishing on the union, not a homotopy-fiber definition. -/
abbrev fiber : Scheme.{u}ᵒᵖ ⥤ Model.{u+1} :=
  ParameterModels.supported (unionOpen f T).ι

/-- Original sections with the auxiliary closed support. -/
abbrev ambient : Scheme.{u}ᵒᵖ ⥤ Model.{u+1} :=
  ParameterModels.supported T.ι

/-- Original fine supported sections on the open scheme. -/
abbrev openModel : Scheme.{u}ᵒᵖ ⥤ Model.{u+1} :=
  ParameterModels.supported (inverseOpen f T).ι

/-- The actual inclusion of support opens has identity ambient leg. -/
def enlargementPair : supportOpenPair T ⟶ supportOpenPair (unionOpen f T) :=
  ObjectProperty.homMk (Arrow.homMk (Q.homOfLE (show T ≤ unionOpen f T from le_sup_left))
    (𝟙 Q) (by
      change Q.homOfLE _ ≫ (unionOpen f T).ι = T.ι ≫ 𝟙 Q
      simpa only [Category.comp_id] using Scheme.homOfLE_ι Q _))

/-- Forget only the extra vanishing on the localization open. -/
def enlargement : fiber f T ⟶ ambient T := by
  let h := supportedMap (enlargementPair f T)
  dsimp only [supportOpenPair] at h
  exact h

/-- Restrict the original auxiliary-supported sections to the actual open scheme. -/
def restriction : ambient T ⟶ openModel f T := by
  let h := supportedMap (supportRestrictionPair f T)
  dsimp only [supportOpenPair] at h
  exact h

/-- The enlargement's ambient product pullback is literally identity. -/
theorem ambientMap_id (X : Scheme.{u}) : ambientMap (𝟙 X) = 𝟙 (ParameterModels.ambient X) := by
  have h : productMap (𝟙 X) = 𝟙 (baseProductFunctor (toIntegerBase X)) := by
    apply NatTrans.ext
    funext S
    apply pullback.hom_ext <;> simp [productMap, baseProductTransformation, baseProductFunctor]
  simp [ambientMap, h, ParameterModels.ambient]

/-- Support enlargement followed by forgetting is the original union-support forgetting. -/
theorem enlargement_forget :
    enlargement f T ≫ ParameterModels.forget T.ι =
      ParameterModels.forget (unionOpen f T).ι := by
  have h := supportedMap_forget (enlargementPair f T)
  change enlargement f T ≫ ParameterModels.forget T.ι =
    ParameterModels.forget (unionOpen f T).ι ≫ ambientMap (𝟙 Q) at h
  simpa only [ambientMap_id, Category.comp_id] using h

omit [IsOpenImmersion f] in
/-- Supported restriction and original ambient restriction commute strictly. -/
theorem restriction_forget :
    restriction f T ≫ ParameterModels.forget (inverseOpen f T).ι =
      ParameterModels.forget T.ι ≫ ambientMap f :=
  supportedMap_forget (supportRestrictionPair f T)

end ParameterAuxiliarySupport
end Quillen.PerfectComplexes.GlobalSectionChangeIndex
