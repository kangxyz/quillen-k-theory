/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealPushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.Principal

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ClosedImmersion
/-!
# Principal closed pushforward onto the annihilated coherent objects

Actual closed pushforward is an equivalence onto coherent sheaves whose
global-section module is annihilated by f. It is not an equivalence onto the
larger category with f-power-torsion sections; that passage needs dévissage.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent
open Quillen.FiniteModuleLocalization

open CategoryTheory.ExactCategory

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal
open FiniteModuleLocalization

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (f : R)

/-- Annihilation by f on actual affine coherent sheaves, tested on the
actual global-section module. This is stronger than power-torsion support. -/

def finiteTypeSheavesKilledBy : ObjectProperty (FiniteTypeSheaves (Spec R)) :=
  (killedBy f).inverseImage (finiteTypeSheavesSpecModuleEquivalence R).functor

instance killedBy_isoClosed : (killedBy f).IsClosedUnderIsomorphisms where
  of_iso e h := by
    intro n
    obtain ⟨m, rfl⟩ := (FGModuleCat.isoToLinearEquiv e).surjective n
    rw [← _root_.map_smul, h m, _root_.map_zero]

instance finiteTypeSheavesKilledBy_isoClosed : (finiteTypeSheavesKilledBy R
  f).IsClosedUnderIsomorphisms := by
  dsimp [finiteTypeSheavesKilledBy]
  infer_instance

/-- The affine global-section equivalence restricts to annihilated objects. -/

def killedModuleEquivalence :
    (finiteTypeSheavesKilledBy R f).FullSubcategory ≌ (killedBy f).FullSubcategory :=
  (finiteTypeSheavesSpecModuleEquivalence R).congrFullSubcategory rfl

omit [IsNoetherianRing R] in

/-- The actual closed pushforward is annihilated by the defining element. -/

theorem coherentPushforward_killed (M : FiniteTypeSheaves (Spec
  (Pushforward.ClosedImmersion.Ideal.closedRing R
  (Ideal.span {f})))) :
    finiteTypeSheavesKilledBy R f
      ((AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward
      (Pushforward.ClosedImmersion.Ideal.closedMap R
      (Ideal.span {f}))).obj M) := by
  let e := (coherentPushforwardSquare R f).app M
  intro m
  apply (FGModuleCat.isoToLinearEquiv e).injective
  rw [_root_.map_smul, _root_.map_zero]
  exact closedRestriction_killed f
    ((finiteTypeSheavesSpecModuleEquivalence
      (Pushforward.ClosedImmersion.Ideal.closedRing R
      (Ideal.span {f}))).functor.obj M) _

/-- Actual sheaf pushforward, with its codomain restricted to annihilated
objects rather than the larger supported category. -/

def coherentPushforwardToKilled :
    FiniteTypeSheaves (Spec
      (Pushforward.ClosedImmersion.Ideal.closedRing R
      (Ideal.span {f}))) ⥤ (finiteTypeSheavesKilledBy R f).FullSubcategory
      :=
  ObjectProperty.lift _ (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward
    (Pushforward.ClosedImmersion.Ideal.closedMap R
    (Ideal.span {f}))) (coherentPushforward_killed R f)

omit [IsNoetherianRing R] in

/-- Forgetting the annihilation proof recovers actual coherent pushforward. -/

theorem coherentPushforwardToKilled_comp_inclusion :
    coherentPushforwardToKilled R f ⋙ (finiteTypeSheavesKilledBy R f).ι =
      AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward
        (Pushforward.ClosedImmersion.Ideal.closedMap R
        (Ideal.span {f})) := rfl

/-- The comparison square restricts to the actual annihilated full subcategories. -/

def coherentPushforwardToKilledSquare :
    coherentPushforwardToKilled R f ⋙ (killedModuleEquivalence R f).functor ≅
      (finiteTypeSheavesSpecModuleEquivalence
        (Pushforward.ClosedImmersion.Ideal.closedRing R
        (Ideal.span {f}))).functor ⋙ closedToKilled f :=
  ((killedBy f).fullyFaithfulι.whiskeringRight _).preimageIso (coherentPushforwardSquare R f)

instance coherentPushforwardToKilled_full : (coherentPushforwardToKilled R f).Full :=
  Functor.Full.of_comp_faithful_iso (coherentPushforwardToKilledSquare R f)

instance coherentPushforwardToKilled_faithful : (coherentPushforwardToKilled R f).Faithful :=
  Functor.Faithful.of_comp_iso (coherentPushforwardToKilledSquare R f)

instance coherentPushforwardToKilled_essSurj : (coherentPushforwardToKilled R f).EssSurj := by
  have : (coherentPushforwardToKilled R f ⋙ (killedModuleEquivalence R f).functor).EssSurj :=
    Functor.essSurj_of_iso (coherentPushforwardToKilledSquare R f).symm
  exact Functor.essSurj_of_comp_fully_faithful (coherentPushforwardToKilled R f)
    (killedModuleEquivalence R f).functor

instance coherentPushforwardToKilled_isEquivalence :
    (coherentPushforwardToKilled R f).IsEquivalence := {}

/-- The equivalence onto exactly the f-annihilated coherent objects, induced
by the actual geometric closed pushforward. -/

def coherentClosedEquivalence :
    FiniteTypeSheaves (Spec
      (Pushforward.ClosedImmersion.Ideal.closedRing R
      (Ideal.span {f}))) ≌ (finiteTypeSheavesKilledBy R f).FullSubcategory
      :=
  (coherentPushforwardToKilled R f).asEquivalence

instance coherentKilled_hasFiniteProducts :
    HasFiniteProducts (finiteTypeSheavesKilledBy R f).FullSubcategory where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (coherentClosedEquivalence R f).inverse

/-- The annihilated category is abelian via its proved actual closed-sheaf
equivalence, without claiming that it is a Serre subcategory. -/

instance instAbelianCoherentKilledBy : Abelian (finiteTypeSheavesKilledBy R f).FullSubcategory :=
  abelianOfEquivalence (coherentClosedEquivalence R f).inverse

instance coherentPushforwardToKilled_additive : (coherentPushforwardToKilled R f).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (coherentPushforwardToKilled R f)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Actual closed pushforward is exact as an equivalence onto the annihilated
coherent category equipped with its standard abelian exact structure. -/

def coherentPushforwardToKilledExact :
    ExactFunctor (coherentExactStructure (Spec
      (Pushforward.ClosedImmersion.Ideal.closedRing R
      (Ideal.span {f}))))
      (abelianExactStructure (finiteTypeSheavesKilledBy R f).FullSubcategory) where
  toFunctor := coherentPushforwardToKilled R f
  map_conflation _ h := h.map_of_exact _

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal
