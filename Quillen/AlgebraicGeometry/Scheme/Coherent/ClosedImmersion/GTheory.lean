/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.GlobalSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealPushforward
public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.Principal
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.ComparisonGTheory
public import Quillen.CategoryTheory.SmallModel.Functoriality

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ClosedImmersion
/-!
# Canonical G-maps of actual principal closed pushforward

The map is induced by the exact actual sheaf pushforward. Its compatibility
with quotient-ring restriction of scalars is proved by natural-isomorphism
invariance of the canonical K-map, including all small-model choices.
The public upper-universe map and the lowest-universe affine map are kept
separate; no cross-universe realization identification is used.
-/
@[expose] public section

open AlgebraicGeometry.Scheme

open Quillen.FiniteModuleLocalization


open AlgebraicGeometry.Scheme.Modules.Coherent
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

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

variable (f : R)

/-- The canonical principal closed pushforward on the public global G-groups. -/
def coherentPushforwardGMap (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.Coherent.G (Spec
      (Pushforward.ClosedImmersion.Ideal.closedRing R
      (Ideal.span {f}))) n →*
      AlgebraicGeometry.Scheme.Modules.Coherent.G (Spec R) n :=
  CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1}
    (Modules.Coherent.Pushforward.ClosedImmersion.Ideal.coherentPushforwardExact R (Ideal.span {f}))
    n

/-- The exact comparison square induces equality of canonical upper-universe
K-maps. The module term here is formed in the same universe as public scheme G. -/
theorem coherentPushforwardGMap_square (n : ℕ) :
    (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1}
      (AlgebraicGeometry.Scheme.Modules.Coherent.globalSectionsExact R) n).comp
      (coherentPushforwardGMap R f n) =
    (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (closedRestrictionExact f) n).comp
      (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1}
        (AlgebraicGeometry.Scheme.Modules.Coherent.globalSectionsExact
        (Pushforward.ClosedImmersion.Ideal.closedRing R
        (Ideal.span {f}))) n) := by
  have h := CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := (Modules.Coherent.Pushforward.ClosedImmersion.Ideal.coherentPushforwardExact R (Ideal.span
      {f})).comp (AlgebraicGeometry.Scheme.Modules.Coherent.globalSectionsExact R))
    (G := (AlgebraicGeometry.Scheme.Modules.Coherent.globalSectionsExact
      (Pushforward.ClosedImmersion.Ideal.closedRing R
      (Ideal.span {f}))).comp (closedRestrictionExact f))
    (coherentPushforwardSquare R f) n
  simpa only [CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, coherentPushforwardGMap]
    using h

/-- The same actual pushforward on the proved lowest-universe affine G-groups. -/
def specPushforwardGMap (n : ℕ) : SpecG
  (Pushforward.ClosedImmersion.Ideal.closedRing R
  (Ideal.span {f})) n →* SpecG R n :=
  (Modules.Coherent.Pushforward.ClosedImmersion.Ideal.coherentPushforwardExact R (Ideal.span
    {f})).smallKMap n

/-- The affine G-comparison is precisely the canonical global-sections K-map. -/
theorem specGRingEquiv_eq_globalSections (n : ℕ) :
    (specGRingEquiv R n).toMonoidHom =
      CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u}
        (AlgebraicGeometry.Scheme.Modules.Coherent.globalSectionsExact R) n := by
  rw [AlgebraicGeometry.Scheme.Modules.Coherent.globalSectionsExact,
    CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp]
  rfl

/-- Actual closed sheaf pushforward matches actual quotient-ring restriction
of scalars under the proved affine G-theory equivalences. -/
theorem specPushforwardGMap_square (n : ℕ) :
    (specGRingEquiv R n).toMonoidHom.comp (specPushforwardGMap R f n) =
      ((closedRestrictionExact f).smallKMap n).comp
        (specGRingEquiv
          (Pushforward.ClosedImmersion.Ideal.closedRing R
          (Ideal.span {f})) n).toMonoidHom := by
  rw [specGRingEquiv_eq_globalSections, specGRingEquiv_eq_globalSections]
  have h := CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u}
    (F := (Modules.Coherent.Pushforward.ClosedImmersion.Ideal.coherentPushforwardExact R (Ideal.span
      {f})).comp (AlgebraicGeometry.Scheme.Modules.Coherent.globalSectionsExact R))
    (G := (AlgebraicGeometry.Scheme.Modules.Coherent.globalSectionsExact
      (Pushforward.ClosedImmersion.Ideal.closedRing R
      (Ideal.span {f}))).comp (closedRestrictionExact f))
    (coherentPushforwardSquare R f) n
  simpa only [CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, specPushforwardGMap] using h

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal
