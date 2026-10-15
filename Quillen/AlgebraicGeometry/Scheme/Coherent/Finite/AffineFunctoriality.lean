/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.AffineFunctoriality
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Finite.AffinePushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.PushforwardFunctoriality

/-! # Actual sheaf identity/composition comparisons prove functoriality of finite affine
  G-pushforward. The established closed-pushforward maps and the exact original global-sections
  square are retained. -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent


open ModuleCat.FiniteRestrictionScalars

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen






noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine
variable {R S T : CommRingCat.{u}}
  [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]

@[simp] theorem pushforwardG_id (R : CommRingCat.{u}) [IsNoetherianRing R] (n : ℕ) :
    pushforwardG (𝟙 R) (RingHom.Finite.id R) n = MonoidHom.id (G (Spec R) n) := by
  exact (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := coherentPushforwardExact (𝟙 R) (RingHom.Finite.id R))
    (G := CategoryTheory.ExactCategory.ExactFunctor.id (coherentExactStructure (Spec R)))
    (coherentPushforwardIdIso R) n).trans (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_id _
      n)

@[simp] theorem pushforwardG_comp (φ : R ⟶ S) (hφ : φ.hom.Finite)
    (ψ : S ⟶ T) (hψ : ψ.hom.Finite) (n : ℕ) :
    pushforwardG (φ ≫ ψ) (hψ.comp hφ) n =
      (pushforwardG φ hφ n).comp (pushforwardG ψ hψ n) := by
  exact (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := coherentPushforwardExact (φ ≫ ψ) (hψ.comp hφ))
    (G := (coherentPushforwardExact ψ hψ).comp (coherentPushforwardExact φ hφ))
    (coherentPushforwardCompIso φ hφ ψ hψ).symm n).trans
      (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp _ _ n)

/-- New finite affine G-pushforward agrees with the existing public closed pushforward. -/
theorem pushforwardG_eq_closed (φ : R ⟶ S) (hφ : φ.hom.Finite)
    [IsClosedImmersion (Spec.map φ)] (n : ℕ) :
    pushforwardG φ hφ n =
      AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.coherentPushforwardGMap
      (Spec.map φ) n :=
  CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := coherentPushforwardExact φ hφ)
    (G :=
      AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.coherentPushforwardExact
      (Spec.map φ))
    (coherentPushforwardClosedIso φ hφ) n

/-- Actual global sections commute with the new upper-universe public G-map. -/
theorem pushforwardG_globalSections (φ : R ⟶ S) (hφ : φ.hom.Finite) (n : ℕ) :
    (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1}
      (AlgebraicGeometry.Scheme.Modules.Coherent.globalSectionsExact R) n).comp
      (pushforwardG φ hφ n) =
      (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (moduleRestrictionExact φ hφ)
        n).comp
        (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1}
          (AlgebraicGeometry.Scheme.Modules.Coherent.globalSectionsExact S) n) := by
  have h := CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := (coherentPushforwardExact φ hφ).comp
      (AlgebraicGeometry.Scheme.Modules.Coherent.globalSectionsExact R))
    (G := (AlgebraicGeometry.Scheme.Modules.Coherent.globalSectionsExact S).comp
      (moduleRestrictionExact φ hφ))
    (coherentPushforwardSquare φ hφ) n
  simpa only [CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, pushforwardG] using h

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine
