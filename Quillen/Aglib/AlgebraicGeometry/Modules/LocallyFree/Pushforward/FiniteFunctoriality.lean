/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Pushforward.Finite

/-!
# Functoriality of finite flat vector-bundle direct image

The original sheaf direct-image comparisons lift to identity, composition and open base change for
finite flat vector-bundle pushforward.-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

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

/-- The original open base-change isomorphism restricts to vector bundles. -/
def vectorBundlePushforwardOpenBaseChange (f : X ⟶ Y)
    [AlgebraicGeometry.IsFinite f] [Flat f]
    {V : Scheme.{u}} [IsLocallyNoetherian V] (j : V ⟶ Y) [IsOpenImmersion j] :
    vectorBundlePushforward f ⋙ vectorBundleRestrict j ≅
      vectorBundleRestrict (pullback.fst f j) ⋙ vectorBundlePushforward (pullback.snd f j) :=
  Functor.fullyFaithfulCancelRight (finiteLocallyFree V).ι
    (Functor.isoWhiskerLeft (finiteLocallyFree X).ι (AlgebraicGeometry.Scheme.Modules.openBaseChange
      f j))

end AlgebraicGeometry.Scheme.Modules
