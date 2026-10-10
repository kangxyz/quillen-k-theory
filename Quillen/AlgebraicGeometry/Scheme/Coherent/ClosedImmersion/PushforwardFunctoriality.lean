/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.GeneralPushforward

/-!
# Actual closed-immersion coherent pushforward functoriality

The original sheaf direct-image identity and composition comparisons restrict
to coherent sheaves on locally noetherian schemes. Their exact-functor K-maps
prove identity and composition for the existing closed-immersion G-pushforward.
Scheme isomorphisms give genuine inverse pushforwards on the original G-groups.
No quasi-compactness or global noetherianity is required. These are actual
closed-immersion maps; no general proper or nonexact direct image is introduced.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.CoherentScheme.ClosedImmersion.General
variable {X Y Z : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]

/-- Identity pushforward on actual coherent sheaves, from the original sheaf comparison. -/
def coherentPushforwardIdIso (X : Scheme.{u}) [IsLocallyNoetherian X] :
    coherentPushforward (𝟙 X) ≅ 𝟭 (FiniteTypeSheaves X) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules X)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules X) (Scheme.Modules.pushforwardId X) ≪≫
      Functor.rightUnitor _)

/-- Composition of the actual coherent direct images, retaining the original sheaf comparison. -/
def coherentPushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g] :
    coherentPushforward f ⋙ coherentPushforward g ≅ coherentPushforward (f ≫ g) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules Z)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules X) (Scheme.Modules.pushforwardComp f g))

/-- The original closed-immersion G-map preserves identity. -/
@[simp] theorem coherentPushforwardGMap_id (X : Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    coherentPushforwardGMap (𝟙 X) n = MonoidHom.id (G X n) := by
  exact (ExactFunctor.smallKMap_eq_of_natIso
    (F := coherentPushforwardExact (𝟙 X))
    (G := ExactFunctor.id (coherentExactStructure X))
    (coherentPushforwardIdIso X) n).trans (ExactFunctor.smallKMap_id _ n)

/-- The original G-maps compose covariantly along closed immersions. -/
@[simp] theorem coherentPushforwardGMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g] (n : ℕ) :
    coherentPushforwardGMap (f ≫ g) n =
      (coherentPushforwardGMap g n).comp (coherentPushforwardGMap f n) := by
  exact (ExactFunctor.smallKMap_eq_of_natIso
    (F := coherentPushforwardExact (f ≫ g))
    (G := (coherentPushforwardExact f).comp (coherentPushforwardExact g))
    (coherentPushforwardCompIso f g).symm n).trans (ExactFunctor.smallKMap_comp _ _ n)

/-- The original pushforwards along inverse scheme isomorphisms are mutual inverses. -/
@[simp] theorem coherentPushforwardGMap_iso_inv_comp
    (e : X ≅ Y) (n : ℕ) :
    (coherentPushforwardGMap e.inv n).comp (coherentPushforwardGMap e.hom n) =
      MonoidHom.id (G X n) := by
  simp only [← coherentPushforwardGMap_comp, e.hom_inv_id, coherentPushforwardGMap_id]

/-- The covariant G comparison for a scheme isomorphism uses the original pushforward. -/
def coherentPushforwardGEquiv (e : X ≅ Y) (n : ℕ) : G X n ≃* G Y n where
  toFun := coherentPushforwardGMap e.hom n
  invFun := coherentPushforwardGMap e.inv n
  left_inv x := DFunLike.congr_fun (coherentPushforwardGMap_iso_inv_comp e n) x
  right_inv x := DFunLike.congr_fun (coherentPushforwardGMap_iso_inv_comp e.symm n) x
  map_mul' x y := map_mul _ x y

@[simp] theorem coherentPushforwardGEquiv_toMonoidHom (e : X ≅ Y) (n : ℕ) :
    (coherentPushforwardGEquiv e n).toMonoidHom = coherentPushforwardGMap e.hom n := rfl

end Quillen.CoherentScheme.ClosedImmersion.General
