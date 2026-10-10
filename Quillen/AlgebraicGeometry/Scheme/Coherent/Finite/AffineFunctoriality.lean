/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Finite.AffinePushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.PushforwardFunctoriality

/-! # Actual sheaf identity/composition comparisons prove functoriality of finite affine
  G-pushforward. The established closed-pushforward maps and the exact original global-sections
  square are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.CoherentScheme.FiniteAffine
variable {R S T : CommRingCat.{u}}
  [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]

/-- The actual finite direct image retains the original sheaf identity comparison. -/
def coherentPushforwardIdIso (R : CommRingCat.{u}) [IsNoetherianRing R] :
    coherentPushforward (𝟙 R) (RingHom.Finite.id R) ≅ 𝟭 (FiniteTypeSheaves (Spec R)) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules (Spec R))
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules (Spec R))
      (show Scheme.Modules.pushforward (Spec.map (𝟙 R)) ≅ 𝟭 (Spec R).Modules by
        simpa only [Spec.map_id] using Scheme.Modules.pushforwardId (Spec R)) ≪≫
      Functor.rightUnitor _)

/-- The original finite affine direct images compose with the genuine sheaf comparison. -/
def coherentPushforwardCompIso (φ : R ⟶ S) (hφ : φ.hom.Finite)
    (ψ : S ⟶ T) (hψ : ψ.hom.Finite) :
    coherentPushforward ψ hψ ⋙ coherentPushforward φ hφ ≅
      coherentPushforward (φ ≫ ψ) (hψ.comp hφ) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules (Spec R))
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules (Spec T))
      (show Scheme.Modules.pushforward (Spec.map ψ) ⋙ Scheme.Modules.pushforward (Spec.map φ) ≅
        Scheme.Modules.pushforward (Spec.map (φ ≫ ψ)) by
        simpa only [Spec.map_comp] using Scheme.Modules.pushforwardComp (Spec.map ψ) (Spec.map φ)))

@[simp] theorem pushforwardG_id (R : CommRingCat.{u}) [IsNoetherianRing R] (n : ℕ) :
    pushforwardG (𝟙 R) (RingHom.Finite.id R) n = MonoidHom.id (G (Spec R) n) := by
  exact (ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := coherentPushforwardExact (𝟙 R) (RingHom.Finite.id R))
    (G := ExactFunctor.id (coherentExactStructure (Spec R)))
    (coherentPushforwardIdIso R) n).trans (ExactFunctor.smallKMap_id _ n)

@[simp] theorem pushforwardG_comp (φ : R ⟶ S) (hφ : φ.hom.Finite)
    (ψ : S ⟶ T) (hψ : ψ.hom.Finite) (n : ℕ) :
    pushforwardG (φ ≫ ψ) (hψ.comp hφ) n =
      (pushforwardG φ hφ n).comp (pushforwardG ψ hψ n) := by
  exact (ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := coherentPushforwardExact (φ ≫ ψ) (hψ.comp hφ))
    (G := (coherentPushforwardExact ψ hψ).comp (coherentPushforwardExact φ hφ))
    (coherentPushforwardCompIso φ hφ ψ hψ).symm n).trans
      (ExactFunctor.smallKMap_comp _ _ n)

/-- The established closed-immersion comparison is unchanged whenever this finite affine map is
  closed. -/
def coherentPushforwardClosedIso (φ : R ⟶ S) (hφ : φ.hom.Finite)
    [IsClosedImmersion (Spec.map φ)] :
    coherentPushforward φ hφ ≅ ClosedImmersion.General.coherentPushforward (Spec.map φ) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules (Spec R)) (Iso.refl _)

/-- New finite affine G-pushforward agrees with the existing public closed pushforward. -/
theorem pushforwardG_eq_closed (φ : R ⟶ S) (hφ : φ.hom.Finite)
    [IsClosedImmersion (Spec.map φ)] (n : ℕ) :
    pushforwardG φ hφ n = ClosedImmersion.General.coherentPushforwardGMap (Spec.map φ) n :=
  ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := coherentPushforwardExact φ hφ)
    (G := ClosedImmersion.General.coherentPushforwardExact (Spec.map φ))
    (coherentPushforwardClosedIso φ hφ) n

/-- Actual global sections commute with the new upper-universe public G-map. -/
theorem pushforwardG_globalSections (φ : R ⟶ S) (hφ : φ.hom.Finite) (n : ℕ) :
    (ExactFunctor.smallKMap.{u+1} (ClosedImmersion.Ideal.globalSectionsExact R) n).comp
      (pushforwardG φ hφ n) =
      (ExactFunctor.smallKMap.{u+1} (moduleRestrictionExact φ hφ) n).comp
        (ExactFunctor.smallKMap.{u+1} (ClosedImmersion.Ideal.globalSectionsExact S) n) := by
  have h := ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := (coherentPushforwardExact φ hφ).comp (ClosedImmersion.Ideal.globalSectionsExact R))
    (G := (ClosedImmersion.Ideal.globalSectionsExact S).comp (moduleRestrictionExact φ hφ))
    (coherentPushforwardSquare φ hφ) n
  simpa only [ExactFunctor.smallKMap_comp, pushforwardG] using h

end Quillen.CoherentScheme.FiniteAffine
