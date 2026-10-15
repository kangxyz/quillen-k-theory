/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.FinitePushforward
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Restriction

/-! # Identity, composition and open base change for finite flat K-pushforward

Every comparison is inherited from the original sheaf direct image. The
induced maps concern genuine vector-bundle K-groups on the original schemes.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]

/-- Identity comparison inherited from the actual module-sheaf direct image. -/
def vectorBundlePushforwardIdIso (X : Scheme.{u}) [IsLocallyNoetherian X] :
    vectorBundlePushforward (𝟙 X) ≅ 𝟭 (FiniteLocallyFree X) :=
  Functor.fullyFaithfulCancelRight (finiteLocallyFree X).ι
    (Functor.isoWhiskerLeft (finiteLocallyFree X).ι (Scheme.Modules.pushforwardId X) ≪≫
      Functor.rightUnitor _)

/-- Composition comparison retains the original geometric direct images. -/
def vectorBundlePushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.IsFinite f] [Flat f] [AlgebraicGeometry.IsFinite g] [Flat g] :
    vectorBundlePushforward f ⋙ vectorBundlePushforward g ≅ vectorBundlePushforward (f ≫ g) :=
  Functor.fullyFaithfulCancelRight (finiteLocallyFree Z).ι
    (Functor.isoWhiskerLeft (finiteLocallyFree X).ι (Scheme.Modules.pushforwardComp f g))

/-- Identity direct image gives the identity original vector-bundle K-map. -/
@[simp] theorem schemeKPushforward_id (X : Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    schemeKPushforward (𝟙 X) n = MonoidHom.id (SchemeK X n) :=
  (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso
    (F := vectorBundlePushforwardExact (𝟙 X))
    (G := CategoryTheory.ExactCategory.ExactFunctor.id (vectorBundleExactStructure X))
    (vectorBundlePushforwardIdIso X) n).trans
      (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_id _ n)

/-- Actual finite flat direct images compose on the original K-groups. -/
@[simp] theorem schemeKPushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.IsFinite f] [Flat f] [AlgebraicGeometry.IsFinite g] [Flat g] (n : ℕ) :
    schemeKPushforward (f ≫ g) n = (schemeKPushforward g n).comp (schemeKPushforward f n) :=
  (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso
    (F := vectorBundlePushforwardExact (f ≫ g))
    (G := (vectorBundlePushforwardExact f).comp (vectorBundlePushforwardExact g))
    (vectorBundlePushforwardCompIso f g).symm n).trans
      (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp _ _ n)

/-- The original open base-change isomorphism restricts to vector bundles. -/
def vectorBundlePushforwardOpenBaseChange (f : X ⟶ Y)
    [AlgebraicGeometry.IsFinite f] [Flat f]
    {V : Scheme.{u}} [IsLocallyNoetherian V] (j : V ⟶ Y) [IsOpenImmersion j] :
    vectorBundlePushforward f ⋙ vectorBundleRestrict j ≅
      vectorBundleRestrict (pullback.fst f j) ⋙ vectorBundlePushforward (pullback.snd f j) :=
  Functor.fullyFaithfulCancelRight (finiteLocallyFree V).ι
    (Functor.isoWhiskerLeft (finiteLocallyFree X).ι (AlgebraicGeometry.Scheme.Modules.openBaseChange
      f j))

/-- Original open restriction and finite flat K-pushforward commute by actual base change. -/
theorem schemeKPushforward_openBaseChange (f : X ⟶ Y)
    [AlgebraicGeometry.IsFinite f] [Flat f]
    {V : Scheme.{u}} [IsLocallyNoetherian V] (j : V ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    (schemeKRestrict j n).comp (schemeKPushforward f n) =
      (schemeKPushforward (pullback.snd f j) n).comp (schemeKRestrict (pullback.fst f j) n) := by
  have h := CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := (vectorBundlePushforwardExact f).comp (vectorBundleExactRestrict j))
    (G := (vectorBundleExactRestrict (pullback.fst f j)).comp
      (vectorBundlePushforwardExact (pullback.snd f j)))
    (vectorBundlePushforwardOpenBaseChange f j) n
  simpa only [CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, schemeKPushforward,
    schemeKRestrict] using h

end AlgebraicGeometry.Scheme.Modules
