/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.Functoriality
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Finite.GeneralPushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Finite.AffineFunctoriality

/-!
# Functoriality of actual finite coherent direct image

Identity and composition of the original module-sheaf pushforward restrict
to coherent sheaves and their canonical G-maps. The finite construction
agrees with the existing finite affine and closed-immersion direct images.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen
open Quillen.CoherentScheme


-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme.Finite
export AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite
  (coherentPushforwardCompIso coherentPushforwardIdIso coherentPushforward_closed
  coherentPushforward_specMap)
end Quillen.CoherentScheme.Finite

end



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite
variable {X Y Z : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]

/-- The original finite G-map preserves identity. -/
@[simp] theorem coherentPushforwardGMap_id (X : Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    coherentPushforwardGMap (𝟙 X) n = MonoidHom.id (G X n) := by
  exact (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso
    (F := coherentPushforwardExact (𝟙 X))
    (G := CategoryTheory.ExactCategory.ExactFunctor.id (coherentExactStructure X))
    (coherentPushforwardIdIso X) n).trans (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_id _
      n)

/-- The original G-maps compose covariantly along finite morphisms. -/
@[simp] theorem coherentPushforwardGMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsFinite g] (n : ℕ) :
    coherentPushforwardGMap (f ≫ g) n =
      (coherentPushforwardGMap g n).comp (coherentPushforwardGMap f n) := by
  exact (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso
    (F := coherentPushforwardExact (f ≫ g))
    (G := (coherentPushforwardExact f).comp (coherentPushforwardExact g))
    (coherentPushforwardCompIso f g).symm n).trans
      (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp _ _ n)

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

@[simp] theorem coherentPushforwardGEquiv_coe (e : X ≅ Y) (n : ℕ) :
    (coherentPushforwardGEquiv e n : G X n →* G Y n) = coherentPushforwardGMap e.hom n := rfl

/-- The canonical finite G-map agrees with the existing finite affine map. -/
@[simp] theorem coherentPushforwardGMap_specMap {R S : CommRingCat.{u}}
    [IsNoetherianRing R] [IsNoetherianRing S] (φ : R ⟶ S)
    [AlgebraicGeometry.IsFinite (Spec.map φ)] (n : ℕ) :
    coherentPushforwardGMap (Spec.map φ) n =
      AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine.pushforwardG φ
      ((AlgebraicGeometry.IsFinite.SpecMap_iff φ).mp inferInstance) n := rfl

/-- The actual canonical G-map specializes to the established closed map. -/
theorem coherentPushforwardGMap_closed (f : X ⟶ Y) [IsClosedImmersion f] (n : ℕ) :
    coherentPushforwardGMap f n =
      AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.coherentPushforwardGMap
      f n := rfl

/-- Original open base change commutes with the canonical finite G-maps. -/
theorem coherentPushforwardGMap_openBaseChange (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f]
    {V : Scheme.{u}} [IsLocallyNoetherian V] (a : V ⟶ Y) [IsOpenImmersion a] (n : ℕ) :
    (restrictionGMap a n).comp (coherentPushforwardGMap f n) =
      (coherentPushforwardGMap (pullback.snd f a) n).comp
        (restrictionGMap (pullback.fst f a) n) := by
  have h := CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := (coherentPushforwardExact f).comp (coherentRestrictionExact a))
    (G := (coherentRestrictionExact (pullback.fst f a)).comp
      (coherentPushforwardExact (pullback.snd f a)))
    (coherentOpenBaseChange f a) n
  simpa only [CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, coherentPushforwardGMap,
    restrictionGMap] using h

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite
