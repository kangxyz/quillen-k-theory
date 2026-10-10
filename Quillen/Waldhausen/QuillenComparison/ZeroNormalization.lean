/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.KTheory.Map.NaturalIso

/-! # Actual zero normalization of exact functors for Q/S naturality

Rebasing the original additive functor transports its genuine conflations.
For strictly zero-preserving functors, the already-defined Quillen K-map is
exactly the map of the unmodified Q-functor. No commutative K-square is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe v u

namespace Quillen

/-- Replacing an object by its equal image does not change the functor. -/
theorem rebaseFunctor_eq_of_eq {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d)
    (h : F.obj c = d) (he : e = eqToIso h) : rebaseFunctor F c d e = F := by
  subst d
  rw [he]
  exact rebaseFunctor_refl F c

namespace ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- The original equality isomorphism induces precisely equality transport in Q. -/
theorem qIsoOfIso_eqToIso_of_eq (E : ExactStructure C) {X Y : C} (h : X = Y) :
    E.qIsoOfIso (eqToIso h) = eqToIso (congrArg (Q.of E.deflation E.inflation) h) := by
  subst Y
  exact E.qIsoOfIso_refl X
end ExactStructure

namespace ExactFunctor
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- Normalize the original functor at the chosen zero, transporting additivity
and conflations through the actual component isomorphisms. -/
def zeroNormalized : ExactFunctor EC ED := by
  let G := rebaseFunctor F.toFunctor (0 : C) (0 : D) F.toFunctor.mapZeroObject
  let e : F.toFunctor ≅ G := rebaseFunctorIso F.toFunctor _ _ _
  letI : G.Additive := CategoryTheory.Functor.additive_of_iso e
  exact {
    toFunctor := G
    map_conflation S hS := ED.iso_closed (S.mapNatIso e) (F.map_conflation S hS) }

/-- This is the same objectwise rebasing used by based Waldhausen maps. -/
theorem zeroNormalized_toFunctor : F.zeroNormalized.toFunctor =
    rebaseFunctor F.toFunctor (0 : C) (0 : D) F.toFunctor.mapZeroObject := rfl

/-- The comparison is a genuine natural isomorphism of the original functors. -/
def zeroNormalizedIso : F.toFunctor ≅ F.zeroNormalized.toFunctor :=
  rebaseFunctorIso F.toFunctor (0 : C) (0 : D) F.toFunctor.mapZeroObject

/-- The normalized exact functor preserves the chosen zero strictly. -/
theorem zeroNormalized_obj_zero : F.zeroNormalized.toFunctor.obj (0 : C) = (0 : D) :=
  rebaseFunctor_obj_base F.toFunctor _ _ _

/-- Based natural-isomorphism invariance identifies its actual Quillen K-map. -/
theorem zeroNormalized_KMap (n : ℕ) : F.zeroNormalized.KMap n = F.KMap n :=
  (KMap_eq_of_natIso F.zeroNormalizedIso n).symm

/-- With strict zero preservation, the canonical zero isomorphism is equality transport. -/
theorem mapZeroObject_eq_eqToIso (h : F.toFunctor.obj (0 : C) = (0 : D)) :
    F.toFunctor.mapZeroObject = eqToIso h := by
  apply Iso.ext
  apply Subsingleton.elim

/-- No Q-rebasing is needed when the original functor already preserves zero strictly. -/
theorem normalizedQ_eq_mapQ_of_zeroEq (h : F.toFunctor.obj (0 : C) = (0 : D)) :
    F.normalizedQ = F.mapQ := by
  apply rebaseFunctor_eq_of_eq F.mapQ
    (Q.of EC.deflation EC.inflation (0 : C))
    (Q.of ED.deflation ED.inflation (0 : D)) _
    (congrArg (Q.of ED.deflation ED.inflation) h)
  rw [mapZeroObject_eq_eqToIso F h, ExactStructure.qIsoOfIso_eqToIso_of_eq]

/-- The unmodified Q-map is based when the functor strictly preserves zero. -/
theorem mapQ_map_point_of_zeroEq (h : F.toFunctor.obj (0 : C) = (0 : D)) :
    classifyingSpaceMap F.mapQ EC.kBasepoint = ED.kBasepoint := by
  rw [show EC.kBasepoint = classifyingSpacePoint (Q.of EC.deflation EC.inflation (0 : C)) from rfl,
    classifyingSpaceMap_point]
  exact congrArg (fun X ↦ classifyingSpacePoint (Q.of ED.deflation ED.inflation X)) h

/-- The actual normalized Quillen K-map agrees with the raw based map in this case. -/
theorem KMap_eq_piMap_of_zeroEq (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : ℕ) :
    F.KMap n = piMap n (classifyingSpaceMap F.mapQ).hom (F.mapQ_map_point_of_zeroEq h) := by
  simp only [KMap_eq_piMap, normalizedQ_eq_mapQ_of_zeroEq F h]

end ExactFunctor
end Quillen
