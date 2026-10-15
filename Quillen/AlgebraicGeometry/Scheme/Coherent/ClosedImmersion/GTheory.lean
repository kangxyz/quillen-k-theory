/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.Principal
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.ComparisonGTheory
public import Quillen.CategoryTheory.SmallModel.Functoriality

/-!
# Canonical G-maps of actual principal closed pushforward

The map is induced by the exact actual sheaf pushforward. Its compatibility
with quotient-ring restriction of scalars is proved by natural-isomorphism
invariance of the canonical K-map, including all small-model choices.
The public upper-universe map and the lowest-universe affine map are kept
separate; no cross-universe realization identification is used.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme.ClosedImmersion
open FiniteModuleLocalization

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- Actual global sections on the global coherent category as an exact functor. -/
def globalSectionsExact :
    ExactFunctor (coherentExactStructure (Spec R)) (finiteModuleExactStructure.{u, u} R) :=
  (coherentToAffineExact R).comp (affineGlobalSectionsExact R)

variable (f : R)

/-- The canonical principal closed pushforward on the public global G-groups. -/
def coherentPushforwardGMap (n : ℕ) :
    CoherentScheme.G (Spec (principalRing R f)) n →* CoherentScheme.G (Spec R) n :=
  CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (coherentPushforwardExact R f) n

/-- The exact comparison square induces equality of canonical upper-universe
K-maps. The module term here is formed in the same universe as public scheme G. -/
theorem coherentPushforwardGMap_square (n : ℕ) :
    (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (globalSectionsExact R) n).comp
      (coherentPushforwardGMap R f n) =
    (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (closedRestrictionExact f) n).comp
      (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (globalSectionsExact (principalRing
        R f)) n) := by
  have h := CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := (coherentPushforwardExact R f).comp (globalSectionsExact R))
    (G := (globalSectionsExact (principalRing R f)).comp (closedRestrictionExact f))
    (coherentPushforwardSquare R f) n
  simpa only [CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, coherentPushforwardGMap]
    using h

/-- The same actual pushforward on the proved lowest-universe affine G-groups. -/
def specPushforwardGMap (n : ℕ) : SpecG (principalRing R f) n →* SpecG R n :=
  (coherentPushforwardExact R f).smallKMap n

/-- The affine G-comparison is precisely the canonical global-sections K-map. -/
theorem specGRingEquiv_eq_globalSections (n : ℕ) :
    (specGRingEquiv R n).toMonoidHom =
      CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u} (globalSectionsExact R) n := by
  rw [globalSectionsExact, CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp]
  rfl

/-- Actual closed sheaf pushforward matches actual quotient-ring restriction
of scalars under the proved affine G-theory equivalences. -/
theorem specPushforwardGMap_square (n : ℕ) :
    (specGRingEquiv R n).toMonoidHom.comp (specPushforwardGMap R f n) =
      ((closedRestrictionExact f).smallKMap n).comp
        (specGRingEquiv (principalRing R f) n).toMonoidHom := by
  rw [specGRingEquiv_eq_globalSections, specGRingEquiv_eq_globalSections]
  have h := CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u}
    (F := (coherentPushforwardExact R f).comp (globalSectionsExact R))
    (G := (globalSectionsExact (principalRing R f)).comp (closedRestrictionExact f))
    (coherentPushforwardSquare R f) n
  simpa only [CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, specPushforwardGMap] using h

end Quillen.CoherentScheme.ClosedImmersion
