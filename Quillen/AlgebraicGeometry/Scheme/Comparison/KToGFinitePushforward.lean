/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.FiniteFlatPushforward
public import Quillen.AlgebraicGeometry.Scheme.Comparison.KToG

/-! # The original K-to-G comparison under finite flat pushforward

Both composites are induced by literally the same underlying sheaf direct
image. Their exact-functor comparison gives a natural transformation from
finite flat vector-bundle K-theory to the established finite G-pushforward.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace Quillen.SchemeSheaf
variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] [Flat f]

/-- The original K-to-G comparison commutes with the actual finite flat direct image. -/
theorem schemeKToG_pushforward (n : ℕ) :
    (CoherentScheme.Finite.coherentPushforwardGMap f n).comp (schemeKToG Z n) =
      (schemeKToG X n).comp (schemeKPushforward f n) := by
  change ((CoherentScheme.Finite.coherentPushforwardExact f).smallKMap n).comp
      ((vectorBundleToCoherentExact Z).smallKMap n) =
    ((vectorBundleToCoherentExact X).smallKMap n).comp
      ((vectorBundlePushforwardExact f).smallKMap n)
  rw [← CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, ←
    CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp]
  exact CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso (Iso.refl _) n

end Quillen.SchemeSheaf

namespace Quillen.Scheme

/-- The actual K-to-G inclusions give a natural comparison of the covariant functors. -/
def KToGFiniteFlatPushforward (n : ℕ) :
    KFiniteFlatPushforwardFunctor n ⟶ forgetFiniteFlat ⋙ GFinitePushforwardFunctor n where
  app X := GrpCat.ofHom (KToG X.obj.obj n)
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    dsimp only [Functor.comp_map, KFiniteFlatPushforwardFunctor, forgetFiniteFlat,
      GFinitePushforwardFunctor, ObjectProperty.homMk, KToG, GrpCat.hom_comp, GrpCat.hom_ofHom]
    apply MonoidHom.ext
    intro x
    exact DFunLike.congr_fun (SchemeSheaf.schemeKToG_pushforward f.hom.hom n).symm x

end Quillen.Scheme
