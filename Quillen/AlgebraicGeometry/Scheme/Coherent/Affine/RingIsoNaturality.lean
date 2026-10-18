/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.LocalizationNaturality
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Original affine G-pullback along ring isomorphisms

For an actual isomorphism of noetherian rings, the original public coherent
pullback commutes with the canonical affine G-comparison. The native module
map is actual restriction of scalars along the inverse ring isomorphism.
The ordinary functor comparison follows from the affine tilde counit and the
original extension/restriction adjunctions before passing to K-theory.

This applies in every degree to the fraction-field and residue-field
isomorphisms in the principal local-DVR boundary. No statement for all flat
ring maps is made here.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory AlgebraicGeometry
open ModuleCat AlgebraicGeometry.Scheme.Modules.QuasiCoherent
namespace AlgebraicGeometry.Scheme.Modules.Coherent
attribute [local instance] Abelian.hasFiniteBiproducts
variable {R T : Type u} [CommRing R] [CommRing T] [IsNoetherianRing R] [IsNoetherianRing T]
  (e : R ≃+* T)

private def ringIsoRestrictionExact := ModuleCat.FiniteRestrictionScalars.moduleRestrictionExact
  (CommRingCat.ofHom e.symm.toRingHom) (RingHom.Finite.of_surjective _ e.symm.surjective)

private def ringIsoRestrictionExtensionIso :
    ModuleCat.restrictScalars e.symm.toRingHom ≅ ModuleCat.extendScalars e.toRingHom :=
  Adjunction.leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).toAdjunction
    (ModuleCat.extendRestrictScalarsAdj e.toRingHom)

private def coherentRingIsoGlobalSectionsIso :
    ((coherentExactPullback (Spec.map e.toCommRingCatIso.hom)).comp
      (globalSectionsExact (CommRingCat.of T))).toFunctor ≅
    ((globalSectionsExact (CommRingCat.of R)).comp (ringIsoRestrictionExact e)).toFunctor := by
  apply Functor.fullyFaithfulCancelRight (forget₂ (FGModuleCat T) (ModuleCat T))
  exact coherentPullbackGlobalSectionsExtensionIso e.toCommRingCatIso.hom ≪≫
    Functor.isoWhiskerLeft
      ((globalSectionsExact (CommRingCat.of R)).toFunctor ⋙ forget₂ (FGModuleCat R) (ModuleCat R))
      (ringIsoRestrictionExtensionIso e).symm

private theorem lowerPullbackG_globalSections_ringIso (n : ℕ) :
    ((globalSectionsExact (CommRingCat.of T)).smallKMap.{u} n).comp
      ((coherentExactPullback (Spec.map e.toCommRingCatIso.hom)).smallKMap.{u} n) =
    ((ringIsoRestrictionExact e).smallKMap n).comp
      ((globalSectionsExact (CommRingCat.of R)).smallKMap.{u} n) := by
  have h := ExactFunctor.smallKMap_eq_of_natIso.{u} (coherentRingIsoGlobalSectionsIso e) n
  simpa only [ExactFunctor.smallKMap_comp] using h

/-- Original affine pullback along the given ring isomorphism agrees with inverse
scalar restriction under the canonical public G-comparisons, in every degree. -/
theorem publicSpecGRingEquiv_ringIso_pullback (n : ℕ) :
    (publicSpecGRingEquiv (CommRingCat.of T) n).toMonoidHom.comp
      (Scheme.pullbackG (Spec.map e.toCommRingCatIso.hom) n) =
    ((ModuleCat.FiniteRestrictionScalars.moduleRestrictionExact
      (CommRingCat.ofHom e.symm.toRingHom)
      (RingHom.Finite.of_surjective _ e.symm.surjective)).smallKMap n).comp
      (publicSpecGRingEquiv (CommRingCat.of R) n).toMonoidHom := by
  let F := coherentExactPullback (Spec.map e.toCommRingCatIso.hom)
  have hn := ExactFunctor.smallKUniverseEquiv_naturality.{u+1,u} F n
  ext a
  change specGRingEquiv (CommRingCat.of T) n
      ((coherentExactStructure (Spec (CommRingCat.of T))).smallKUniverseEquiv.{u+1,u} n
        (Scheme.pullbackG (Spec.map e.toCommRingCatIso.hom) n a)) =
    (ringIsoRestrictionExact e).smallKMap n
      (specGRingEquiv (CommRingCat.of R) n
        ((coherentExactStructure (Spec (CommRingCat.of R))).smallKUniverseEquiv.{u+1,u} n a))
  have ht := DFunLike.congr_fun (specGRingEquiv_eq_globalSectionsKMap (CommRingCat.of T) n)
    ((coherentExactStructure (Spec (CommRingCat.of T))).smallKUniverseEquiv.{u+1,u} n
      (Scheme.pullbackG (Spec.map e.toCommRingCatIso.hom) n a))
  have hr := DFunLike.congr_fun (specGRingEquiv_eq_globalSectionsKMap (CommRingCat.of R) n)
    ((coherentExactStructure (Spec (CommRingCat.of R))).smallKUniverseEquiv.{u+1,u} n a)
  change specGRingEquiv (CommRingCat.of T) n _ = _ at ht
  change specGRingEquiv (CommRingCat.of R) n _ = _ at hr
  rw [ht, hr]
  exact (congrArg ((globalSectionsExact (CommRingCat.of T)).smallKMap.{u} n)
    (DFunLike.congr_fun hn a).symm).trans
      (DFunLike.congr_fun (lowerPullbackG_globalSections_ringIso e n)
        ((coherentExactStructure (Spec (CommRingCat.of R))).smallKUniverseEquiv.{u+1,u} n a))
end AlgebraicGeometry.Scheme.Modules.Coherent
