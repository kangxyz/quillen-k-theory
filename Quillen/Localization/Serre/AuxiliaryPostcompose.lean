/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Localization.Serre.AuxiliaryBaseChange
public import Quillen.Localization.Serre.ImageKernelComma

/-!
# Postcomposition equivalences for Serre auxiliary categories

For an arbitrary Serre-isomorphism of bases, the inclusion of the old
kernel into the composite kernel is natural on actual Q-spans. Comparing
with the proved kernel equivalences gives the postcomposition equivalence.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]

/-- Every old kernel maps canonically into the kernel of the composite. -/
def overPostcomposeKernelMap {M N : C} (i : M ⟶ N) (X : Over M) :
    (overKernel M).obj X ⟶ (overKernel N).obj ((Over.map i).obj X) :=
  pullback.lift (overKernelι X) 0 (by
    change overKernelι X ≫ (X.hom ≫ i) = 0 ≫ (0 : (0 : C) ⟶ N)
    simp)

@[reassoc (attr := simp)]
lemma overPostcomposeKernelMap_ι {M N : C} (i : M ⟶ N) (X : Over M) :
    overPostcomposeKernelMap i X ≫ overKernelι ((Over.map i).obj X) = overKernelι X :=
  pullback.lift_fst _ _ _

instance overPostcomposeKernelMap_mono {M N : C} (i : M ⟶ N) (X : Over M) :
    Mono (overPostcomposeKernelMap i X) :=
  mono_of_mono_fac (overPostcomposeKernelMap_ι i X)

@[reassoc]
lemma overPostcomposeKernelMap_naturality {M N : C} (i : M ⟶ N)
    {X Y : Over M} (f : X ⟶ Y) :
    (overKernel M).map f ≫ overPostcomposeKernelMap i Y =
      overPostcomposeKernelMap i X ≫ (overKernel N).map ((Over.map i).map f) := by
  apply (cancel_mono (overKernelι ((Over.map i).obj Y))).1
  simp

/-- The kernel inclusions are cartesian along every ordinary slice arrow. -/
theorem overPostcomposeKernelMap_isPullback {M N : C} (i : M ⟶ N)
    {X Y : Over M} (f : X ⟶ Y) :
    IsPullback ((overKernel M).map f) (overPostcomposeKernelMap i X)
      (overPostcomposeKernelMap i Y) ((overKernel N).map ((Over.map i).map f)) := by
  apply IsPullback.of_bot (t := overKernel_map_isPullback ((Over.map i).map f))
  · change IsPullback ((overKernel M).map f)
      (overPostcomposeKernelMap i X ≫ overKernelι ((Over.map i).obj X))
      (overPostcomposeKernelMap i Y ≫ overKernelι ((Over.map i).obj Y)) f.left
    rw [overPostcomposeKernelMap_ι, overPostcomposeKernelMap_ι]
    exact overKernel_map_isPullback f
  · exact overPostcomposeKernelMap_naturality i f

/-- Kernel inclusion remains a natural transformation after the actual
restricted-span construction. -/
def overPostcomposeKernelQMap {M N : C} (i : M ⟶ N) :
    overKernelQ M ⟶ overPostcomposeQ i ⋙ overKernelQ N where
  app X := Q.inflationArrow (overPostcomposeKernelMap i X.obj.of)
  naturality X Y f := by
    obtain ⟨s, rfl⟩ := Quotient.exists_rep f
    change Q.mkHom _ _ ((overKernelCompatible M).mapSpan s) ≫
        Q.inflationArrow (overPostcomposeKernelMap i Y.obj.of) =
      Q.inflationArrow (overPostcomposeKernelMap i X.obj.of) ≫
        Q.mkHom _ _ ((overKernelCompatible N).mapSpan ((overPostcomposeCompatible i).mapSpan s))
    apply Q.span_naturality_of_pullback _ _ _ _ (overPostcomposeKernelMap i s.apex)
    · simpa only [QCompatibleFunctor.mapSpan, overKernelCompatible, overPostcomposeCompatible,
        QCompatibleFunctor.ofPreservesPullbacks] using overPostcomposeKernelMap_isPullback i s.l
    · exact overPostcomposeKernelMap_naturality i s.r

variable (P : ObjectProperty C) [P.IsSerreClass]

/-- The same kernel inclusion takes values in the actual Serre Q-category. -/
def auxiliaryPostcomposeKernelMap {M N : C} (i : M ⟶ N) (hi : P.isoModSerre i) :
    auxiliaryKernelFunctor P M ⟶ auxiliaryPostcompose P i hi ⋙ auxiliaryKernelFunctor P N where
  app X := (Devissage.mapQ P).preimage ((overPostcomposeKernelQMap i).app X.obj)
  naturality X Y f := by
    apply (Devissage.mapQ P).map_injective
    simp only [Functor.map_comp, Functor.comp_map, auxiliaryPostcompose,
      auxiliaryKernelFunctor, Functor.map_preimage]
    exact (overPostcomposeKernelQMap i).naturality f.hom

/-- Any Serre-isomorphism of bases gives a homotopy equivalence of auxiliary
categories, with the actual postcomposition functor as its forward map. -/
def auxiliaryPostcomposeClassifyingHomotopyEquiv {M N : C} (i : M ⟶ N)
    (hi : P.isoModSerre i) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (AuxiliaryKernel P M))
      (ClassifyingSpace (AuxiliaryKernel P N)) := by
  let eM := auxiliaryKernelClassifyingHomotopyEquiv P M
  let eN := auxiliaryKernelClassifyingHomotopyEquiv P N
  let f := (classifyingSpaceMap (auxiliaryPostcompose P i hi)).hom
  have h : (eN.toFun.comp f).Homotopic eM.toFun := by
    simpa only [eM, eN, f, auxiliaryKernelClassifyingHomotopyEquiv_toFun,
      classifyingSpaceMap_comp, TopCat.hom_comp] using
      (show (classifyingSpaceMap (auxiliaryPostcompose P i hi ⋙ auxiliaryKernelFunctor P
        N)).hom.Homotopic
        (classifyingSpaceMap (auxiliaryKernelFunctor P M)).hom from
        ⟨(classifyingSpaceNaturalTransformationHomotopy (auxiliaryPostcomposeKernelMap P i
          hi)).symm⟩)
  apply TheoremA.homotopyEquivWithMap (eM.trans eN.symm) f
  exact (show f.Homotopic (eN.invFun.comp (eN.toFun.comp f)) from by
    simpa using ContinuousMap.Homotopic.comp eN.left_inv.symm (.refl f)).trans
      (ContinuousMap.Homotopic.comp (.refl eN.invFun) h)

@[simp]
theorem auxiliaryPostcomposeClassifyingHomotopyEquiv_toFun {M N : C} (i : M ⟶ N)
    (hi : P.isoModSerre i) :
    (auxiliaryPostcomposeClassifyingHomotopyEquiv P i hi).toFun =
      (classifyingSpaceMap (auxiliaryPostcompose P i hi)).hom := rfl

end Quillen.SerreLocalization
