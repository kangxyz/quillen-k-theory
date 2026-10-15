/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.GlobalSections
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealPushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward
public import Aglib.Algebra.Category.ModuleCat.IdealClosedSupport
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.ComparisonGTheory
public import Quillen.CategoryTheory.SmallModel.Functoriality
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual coherent pushforward from an arbitrary affine closed subscheme

For every ideal I, the actual pushforward along Spec(R/I) → Spec(R) restricts
to an exact fully faithful functor on coherent sheaves. It is an equivalence
onto coherent sheaves with global sections annihilated by I. The canonical
G-maps commute with quotient-ring restriction under affine comparison.
-/
@[expose] public section

open ModuleCat.FiniteLocalization.IdealClosedSupport


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen





noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal


variable (R : CommRingCat.{u}) (I : Ideal R)

variable [IsNoetherianRing R]

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)


variable (R : CommRingCat.{u}) [IsNoetherianRing R]

variable (I : Ideal R)

/-- The canonical closed pushforward on the public global G-groups. -/
def coherentPushforwardGMap (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.Coherent.G (Spec (closedRing R I)) n →*
      AlgebraicGeometry.Scheme.Modules.Coherent.G (Spec R) n :=
  CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (coherentPushforwardExact R I) n

/-- The exact comparison square induces equality of canonical upper-universe
K-maps. The module term here is formed in the same universe as public scheme G. -/
theorem coherentPushforwardGMap_square (n : ℕ) :
    (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (globalSectionsExact R) n).comp
      (coherentPushforwardGMap R I n) =
    (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (closedRestrictionExact I) n).comp
      (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (globalSectionsExact (closedRing R
        I)) n) := by
  have h := CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := (coherentPushforwardExact R I).comp (globalSectionsExact R))
    (G := (globalSectionsExact (closedRing R I)).comp (closedRestrictionExact I))
    (coherentPushforwardSquare R I) n
  simpa only [CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, coherentPushforwardGMap]
    using h

/-- The same actual pushforward on the proved lowest-universe affine G-groups. -/
def specPushforwardGMap (n : ℕ) : SpecG (closedRing R I) n →* SpecG R n :=
  (coherentPushforwardExact R I).smallKMap n

/-- The affine G-comparison is precisely the canonical global-sections K-map. -/
theorem specGRingEquiv_eq_globalSections (n : ℕ) :
    (specGRingEquiv R n).toMonoidHom =
      CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u} (globalSectionsExact R) n := by
  rw [globalSectionsExact, CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp]
  rfl

/-- Actual closed sheaf pushforward matches actual quotient-ring restriction
of scalars under the proved affine G-theory equivalences. -/
theorem specPushforwardGMap_square (n : ℕ) :
    (specGRingEquiv R n).toMonoidHom.comp (specPushforwardGMap R I n) =
      ((closedRestrictionExact I).smallKMap n).comp
        (specGRingEquiv (closedRing R I) n).toMonoidHom := by
  rw [specGRingEquiv_eq_globalSections, specGRingEquiv_eq_globalSections]
  have h := CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u}
    (F := (coherentPushforwardExact R I).comp (globalSectionsExact R))
    (G := (globalSectionsExact (closedRing R I)).comp (closedRestrictionExact I))
    (coherentPushforwardSquare R I) n
  simpa only [CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, specPushforwardGMap] using h

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal
