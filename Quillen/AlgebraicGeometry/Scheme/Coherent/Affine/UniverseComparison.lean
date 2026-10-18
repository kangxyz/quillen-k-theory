/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Map.SmallModelUniverse
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Finite.AffineFunctoriality
public import Quillen.GTheory.FiniteModules.LocalizationSequence
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Public affine coherent G-theory and native finite-module G-theory

The public upper-universe G-theory of actual coherent sheaves on `Spec R`
compares canonically with native lower-universe finite-module G-theory.
The comparison uses two models of the SAME coherent category followed by
the original affine global-sections equivalence. Its finite-affine square
retains the original sheaf pushforward and scalar-restriction K-maps.

At a maximal affine point, the native `Spec.residueFieldIso` identifies its
actual residue-field arrow with the original R-map into `Ideal.ResidueField`.
Original closed-immersion pushforward functoriality then proves the literal
residue-arrow G-theory square. No generic-boundary comparison or scheme
support assembly is asserted here, and no module-carrier universe is changed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicGeometry ModuleCat ModuleCat.FiniteRestrictionScalars
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent

attribute [local instance] Abelian.hasFiniteBiproducts

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- The public coherent group compares with native module G via the same original sheaf category. -/
def publicSpecGRingEquiv (n : ℕ) :
    G (Spec R) n ≃* Quillen.FiniteModuleLocalization.G R n :=
  ((coherentExactStructure (Spec R)).smallKUniverseEquiv.{u+1,u} n).trans
    (specGRingEquiv R n)

/-- The existing lower-universe affine equivalence retains the original global-sections K-map. -/
theorem specGRingEquiv_eq_globalSectionsKMap (n : ℕ) :
    (specGRingEquiv R n).toMonoidHom = (globalSectionsExact R).smallKMap.{u} n := by
  rw [specGRingEquiv_toMonoidHom]
  exact (ExactFunctor.smallKMap_comp (coherentToAffineExact R)
    (affineGlobalSectionsExact R) n).symm

/-- The forward map is the canonical model comparison followed by original global sections. -/
theorem publicSpecGRingEquiv_toMonoidHom (n : ℕ) :
    (publicSpecGRingEquiv R n).toMonoidHom =
      ((globalSectionsExact R).smallKMap.{u} n).comp
        ((ExactStructure.smallModelUniverseComparison.{u+1,u}
          (coherentExactStructure (Spec R))).universalKMap n) := by
  change (specGRingEquiv R n).toMonoidHom.comp
    (((coherentExactStructure (Spec R)).smallModelUniverseComparison.{u+1,u}).universalKMap n) = _
  rw [specGRingEquiv_eq_globalSectionsKMap]

variable {R} {S : CommRingCat.{u}} [IsNoetherianRing S] (φ : R ⟶ S) (hφ : φ.hom.Finite)

/-- Actual global sections commute with original finite pushforward in the lower model as well. -/
theorem lowerPushforwardG_globalSections (n : ℕ) :
    ((globalSectionsExact R).smallKMap.{u} n).comp
      ((Pushforward.Finite.Affine.coherentPushforwardExact φ hφ).smallKMap.{u} n) =
    ((moduleRestrictionExact φ hφ).smallKMap.{u} n).comp
      ((globalSectionsExact S).smallKMap.{u} n) := by
  have h := ExactFunctor.smallKMap_eq_of_natIso.{u}
    (F := (Pushforward.Finite.Affine.coherentPushforwardExact φ hφ).comp
      (globalSectionsExact R))
    (G := (globalSectionsExact S).comp (moduleRestrictionExact φ hφ))
    (Pushforward.Finite.Affine.coherentPushforwardSquare φ hφ) n
  simpa only [ExactFunctor.smallKMap_comp] using h

/-- The original public finite-affine pushforward commutes with the native module comparison. -/
theorem publicSpecGRingEquiv_pushforward (n : ℕ) :
    ((moduleRestrictionExact φ hφ).smallKMap.{u} n).comp
      (publicSpecGRingEquiv S n).toMonoidHom =
    (publicSpecGRingEquiv R n).toMonoidHom.comp
      (Pushforward.Finite.Affine.pushforwardG φ hφ n) := by
  have hn := ExactFunctor.smallKUniverseEquiv_naturality.{u+1,u}
    (Pushforward.Finite.Affine.coherentPushforwardExact φ hφ) n
  ext a
  change (moduleRestrictionExact φ hφ).smallKMap.{u} n
      (specGRingEquiv S n
        ((coherentExactStructure (Spec S)).smallKUniverseEquiv.{u+1,u} n a)) =
    specGRingEquiv R n
      ((coherentExactStructure (Spec R)).smallKUniverseEquiv.{u+1,u} n
        (Pushforward.Finite.Affine.pushforwardG φ hφ n a))
  have hs := DFunLike.congr_fun (specGRingEquiv_eq_globalSectionsKMap S n)
    ((coherentExactStructure (Spec S)).smallKUniverseEquiv.{u+1,u} n a)
  have hr := DFunLike.congr_fun (specGRingEquiv_eq_globalSectionsKMap R n)
    ((coherentExactStructure (Spec R)).smallKUniverseEquiv.{u+1,u} n
      (Pushforward.Finite.Affine.pushforwardG φ hφ n a))
  change specGRingEquiv S n
    ((coherentExactStructure (Spec S)).smallKUniverseEquiv.{u+1,u} n a) = _ at hs
  change specGRingEquiv R n
    ((coherentExactStructure (Spec R)).smallKUniverseEquiv.{u+1,u} n
      (Pushforward.Finite.Affine.pushforwardG φ hφ n a)) = _ at hr
  rw [hs, hr]
  exact (DFunLike.congr_fun (lowerPushforwardG_globalSections φ hφ n)
    ((coherentExactStructure (Spec S)).smallKUniverseEquiv.{u+1,u} n a)).symm.trans
      (congrArg ((globalSectionsExact R).smallKMap.{u} n) (DFunLike.congr_fun hn a))

section Residue

variable (R) (x : Spec R) [x.asIdeal.IsMaximal]

/-- The original ring map from the affine ring into its native ideal residue field. -/
abbrev nativeResidueFieldMap : R ⟶ CommRingCat.of x.asIdeal.ResidueField :=
  CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField)

omit [IsNoetherianRing R] in
/-- Maximality makes the original residue-field map finite. -/
theorem nativeResidueFieldMap_finite : (nativeResidueFieldMap R x).hom.Finite :=
  RingHom.Finite.of_surjective _ x.asIdeal.algebraMap_residueField_surjective

/-- The original affine residue-field map is a closed immersion on spectra. -/
instance nativeResidueFieldMap_isClosedImmersion :
    IsClosedImmersion (Spec.map (nativeResidueFieldMap R x)) :=
  IsClosedImmersion.spec_of_surjective _ x.asIdeal.algebraMap_residueField_surjective

/-- The native affine residue-field isomorphism, on spectra in the direction
of the residue arrow. -/
def residueFieldSpecIso :
    Spec ((Spec R).residueField x) ≅ Spec (CommRingCat.of x.asIdeal.ResidueField) :=
  asIso (Spec.map (Scheme.Spec.residueFieldIso R x).inv)

omit [IsNoetherianRing R] [x.asIdeal.IsMaximal] in
/-- This is precisely Mathlib's original affine residue-arrow comparison. -/
theorem residueFieldSpecIso_hom_comp :
    (residueFieldSpecIso R x).hom ≫ Spec.map (nativeResidueFieldMap R x) =
      (Spec R).fromSpecResidueField x :=
  Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R x

/-- At a maximal affine point, the literal scheme residue arrow is a closed immersion. -/
instance fromSpecResidueField_isClosedImmersion :
    IsClosedImmersion ((Spec R).fromSpecResidueField x) := by
  rw [← residueFieldSpecIso_hom_comp R x]
  infer_instance

/-- Public G of the actual scheme residue-field spectrum compares with native ideal-field G. -/
def schemeResidueFieldRingGEquiv (n : ℕ) :
    G (Spec ((Spec R).residueField x)) n ≃*
      Quillen.FiniteModuleLocalization.G x.asIdeal.ResidueField n :=
  (Pushforward.ClosedImmersion.coherentPushforwardGEquiv (residueFieldSpecIso R x) n).trans
    (publicSpecGRingEquiv (CommRingCat.of x.asIdeal.ResidueField) n)

/-- The literal scheme residue arrow retains original restriction along the R-map into the field. -/
theorem schemeResidueFieldRingGEquiv_pushforward (n : ℕ) :
    ((moduleRestrictionExact (nativeResidueFieldMap R x)
      (nativeResidueFieldMap_finite R x)).smallKMap.{u} n).comp
        (schemeResidueFieldRingGEquiv R x n).toMonoidHom =
    (publicSpecGRingEquiv R n).toMonoidHom.comp
      (Pushforward.ClosedImmersion.coherentPushforwardGMap
        ((Spec R).fromSpecResidueField x) n) := by
  have hp := publicSpecGRingEquiv_pushforward (nativeResidueFieldMap R x)
    (nativeResidueFieldMap_finite R x) n
  have hc : Pushforward.ClosedImmersion.coherentPushforwardGMap
      ((Spec R).fromSpecResidueField x) n =
      (Pushforward.ClosedImmersion.coherentPushforwardGMap
        (Spec.map (nativeResidueFieldMap R x)) n).comp
          (Pushforward.ClosedImmersion.coherentPushforwardGMap
            (residueFieldSpecIso R x).hom n) := by
    simpa only [residueFieldSpecIso_hom_comp] using
      (Pushforward.ClosedImmersion.coherentPushforwardGMap_comp
        (residueFieldSpecIso R x).hom (Spec.map (nativeResidueFieldMap R x)) n)
  ext a
  change (moduleRestrictionExact (nativeResidueFieldMap R x)
      (nativeResidueFieldMap_finite R x)).smallKMap.{u} n
      (publicSpecGRingEquiv (CommRingCat.of x.asIdeal.ResidueField) n
        (Pushforward.ClosedImmersion.coherentPushforwardGMap
          (residueFieldSpecIso R x).hom n a)) = _
  have ha := DFunLike.congr_fun hp
    (Pushforward.ClosedImmersion.coherentPushforwardGMap (residueFieldSpecIso R x).hom n a)
  change _ = publicSpecGRingEquiv R n
    (Pushforward.Finite.Affine.pushforwardG (nativeResidueFieldMap R x)
      (nativeResidueFieldMap_finite R x) n
        (Pushforward.ClosedImmersion.coherentPushforwardGMap
          (residueFieldSpecIso R x).hom n a)) at ha
  rw [Pushforward.Finite.Affine.pushforwardG_eq_closed] at ha
  exact ha.trans (congrArg (publicSpecGRingEquiv R n) (DFunLike.congr_fun hc a).symm)

end Residue

end AlgebraicGeometry.Scheme.Modules.Coherent
