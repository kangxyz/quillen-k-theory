/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Regular.SmallComparison
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.UniverseComparison
public import Quillen.GTheory.DVR.UnitPairGeneration
public import Quillen.KTheory.LowDegreeScalarAction.ObjectClass
public import Aglib.AlgebraicGeometry.Modules.Linear
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.LocalBases

/-!
# Actual scalar unit pairs on affine scheme K2

The source is original scheme K-theory of finite locally free sheaves. A pair
uses the original scalar identity-automorphism operation and the literal
positive automorphism-first cube on the tilde of the free rank-one module.
The original K-to-G map and affine global sections send it to the existing
canonically lowered ring-unit product.

For the actual localization of a Dedekind ring at a height-one prime, the
existing PID K-to-G equivalence reflects the proved lower G2 unit-pair
generation, provided the actual residue ring map has a ring section. This
does not identify a separate finite-projective-module K-group or instantiate
an R5 geometric origin or its normalization records.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Linear AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped ZeroObject

namespace Quillen.LowDegreeScalarAction.SpecUnitPairs

attribute [local instance] Abelian.hasFiniteBiproducts

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- Structural linearity uses the original inverse ΓSpec isomorphism. -/
local instance modulesLinear : Linear R (Spec R).Modules :=
  moduleCategoryLinearOfHom (Spec R) (Scheme.ΓSpecIso R).inv.hom

/-- Original exact vector-bundle inclusion followed by actual affine global sections. -/
def toModulesExact : ExactFunctor (vectorBundleExactStructure (Spec R))
    (ModuleCat.finiteModuleExactStructure.{u, u} R) :=
  (vectorBundleToCoherentExact (Spec R)).comp (globalSectionsExact R)

instance toModulesExact_linear : (toModulesExact R).toFunctor.Linear R where
  map_smul {M N} f r := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((r • f.hom).val.app (Opposite.op ⊤)) x =
      ((Scheme.ΓSpecIso R).inv.hom r) • f.hom.val.app (Opposite.op ⊤) x
    rw [moduleCategoryLinearOfHom_smul_app]
    simp

/-- The original finite locally free sheaf associated to the Fin 1 free module. -/
def rankOneBundle : FiniteLocallyFree (Spec R) :=
  ⟨tilde (ModuleCat.of R (Fin 1 → R)),
    finiteLocallyFree_tilde_of_finite_projective R (ModuleCat.of R (Fin 1 → R))⟩

private def rankOneImageIso :
    (toModulesExact R).toFunctor.obj (rankOneBundle R) ≅
      FGModuleCat.of R (Fin 1 → R) :=
  ObjectProperty.isoMk _ ((tildeEquiv (R := R)).unitIso.app
    (ModuleCat.of R (Fin 1 → R))).symm

/-- The actual object class of the selected rank-one vector bundle. -/
def rankOneObjectClass : Scheme.K (Spec R) 0 :=
  (vectorBundleExactStructure (Spec R)).smallModel.{u + 1}.kZeroObjectClass
    ((equivSmallModel.{u + 1} (FiniteLocallyFree (Spec R))).functor.obj (rankOneBundle R))

/-- The literal positive scalar cube on the selected original rank-one bundle. -/
def positiveLineUnit (b : Rˣ) : Scheme.K (Spec R) 1 :=
  Quotient.mk' (Automorphism.Cube.automorphismFirstCube
    (vectorBundleExactStructure (Spec R)).smallModel.{u + 1}
    ((equivSmallModel.{u + 1} (FiniteLocallyFree (Spec R))).functor.obj (rankOneBundle R))
    ((equivSmallModel.{u + 1} (FiniteLocallyFree (Spec R))).functor.mapIso
      ((scalarNatAut R (FiniteLocallyFree (Spec R)) b).app (rankOneBundle R))))

omit [IsNoetherianRing R] in
/-- Both original normalization inverses are retained before cancelling them. -/
theorem positiveLineUnit_eq_inverse_objectAction (b : Rˣ) :
    positiveLineUnit R b =
      (ScalarUnit.smallModelKZeroAction.{u, u + 1, u, u + 1} R
        (vectorBundleExactStructure (Spec R)) b (rankOneObjectClass R))⁻¹ := by
  unfold rankOneObjectClass
  rw [ObjectClass.smallModelKZeroAction_mapped_objectClass_cube, inv_inv]
  rfl

/-- An actual ordered unit pair in original affine scheme K2. -/
def unitPair (a b : Rˣ) : Scheme.K (Spec R) 2 :=
  ScalarUnit.smallModelKOneAction.{u, u + 1, u, u + 1} R
    (vectorBundleExactStructure (Spec R)) a (positiveLineUnit R b)

private theorem rankOneObjectClass_image :
    (toModulesExact R).smallKMap.{u + 1} 0 (rankOneObjectClass R) =
      DvrSymbols.upperRankOneClass R := by
  unfold rankOneObjectClass DvrSymbols.upperRankOneClass
  change (toModulesExact R).smallModel.{u + 1}.KMap 0 _ = _
  rw [ExactFunctor.KMap_kZeroObjectClass]
  apply ExactStructure.kZeroObjectClass_iso
  exact (equivSmallModel.{u + 1} (FGModuleCat.{u} R)).functor.mapIso
    (((toModulesExact R).toFunctor.mapIso
      ((equivSmallModel.{u + 1} (FiniteLocallyFree (Spec R))).unitIso.app
        (rankOneBundle R))).symm ≪≫ rankOneImageIso R)

/-- Actual global sections carry the positive line cube to the original positive ring-unit class. -/
theorem positiveLineUnit_image (b : Rˣ) :
    (toModulesExact R).smallKMap.{u + 1} 1 (positiveLineUnit R b) =
      DvrSymbols.upperUnitKOne R b := by
  rw [positiveLineUnit_eq_inverse_objectAction, map_inv,
    ScalarUnit.smallModelKZeroAction_natural, rankOneObjectClass_image]
  rfl

/-- The genuine original exact functor preserves the actual scalar K1-to-K2 operation. -/
theorem toModulesExact_scalarAction (a : Rˣ) (z : Scheme.K (Spec R) 1) :
    (toModulesExact R).smallKMap.{u + 1} 2
        (ScalarUnit.smallModelKOneAction.{u, u + 1, u, u + 1} R
          (vectorBundleExactStructure (Spec R)) a z) =
      ScalarUnit.upperFiniteModuleKOneAction R a
        ((toModulesExact R).smallKMap.{u + 1} 1 z) :=
  ScalarUnit.smallModelKOneAction_natural R (toModulesExact R) a z

/-- The original scalar pair has exactly the existing upper ring-unit-product value. -/
theorem unitPair_upper_image (a b : Rˣ) :
    (toModulesExact R).smallKMap.{u + 1} 2 (unitPair R a b) =
      DvrSymbols.upperUnitProduct R a b := by
  unfold unitPair
  rw [toModulesExact_scalarAction, positiveLineUnit_image]
  rfl

/-- The literal original scheme K-to-G map followed by the public affine ring map. -/
def kToLowerG (n : ℕ) : Scheme.K (Spec R) n →* FiniteModuleLocalization.G R n :=
  (publicSpecGRingEquiv R n).toMonoidHom.comp (Scheme.KToG (Spec R) n)

private def modelRoundTripIso :
    let E := ModuleCat.finiteModuleExactStructure.{u, u} R
    (E.smallModelUniverseComparison.{u + 1, u}).toFunctor ⋙
        (E.smallModelUniverseComparison.{u, u + 1}).toFunctor ≅
            𝟭 (SmallModel.{u + 1} (FGModuleCat.{u} R)) :=
  Functor.isoWhiskerLeft (equivSmallModel.{u + 1} (FGModuleCat.{u} R)).inverse
    (Functor.isoWhiskerRight (equivSmallModel.{u} (FGModuleCat.{u} R)).unitIso.symm
      (equivSmallModel.{u + 1} (FGModuleCat.{u} R)).functor) ≪≫
    Functor.isoWhiskerLeft (equivSmallModel.{u + 1} (FGModuleCat.{u} R)).inverse
      (Functor.leftUnitor (equivSmallModel.{u + 1} (FGModuleCat.{u} R)).functor) ≪≫
        (equivSmallModel.{u + 1} (FGModuleCat.{u} R)).counitIso

private theorem modelUniverseRoundTrip (n : ℕ) :
    let E := ModuleCat.finiteModuleExactStructure.{u, u} R
    (E.smallKUniverseEquiv.{u, u + 1} n).toMonoidHom.comp
      (E.smallKUniverseEquiv.{u + 1, u} n).toMonoidHom = MonoidHom.id _ := by
  let E := ModuleCat.finiteModuleExactStructure.{u, u} R
  change ((E.smallModelUniverseComparison.{u, u + 1}).universalKMap n).comp
      ((E.smallModelUniverseComparison.{u + 1, u}).universalKMap n) = _
  rw [← ExactFunctor.universalKMap_comp]
  have h := ExactFunctor.universalKMap_eq_of_natIso
    (F := (E.smallModelUniverseComparison.{u + 1, u}).comp
      (E.smallModelUniverseComparison.{u, u + 1}))
    (G := ExactFunctor.id E.smallModel.{u + 1})
    (modelRoundTripIso R) n
  rw [ExactFunctor.universalKMap_eq_KMap
    (ExactFunctor.id E.smallModel.{u + 1}), ExactFunctor.KMap_id] at h
  exact h

private theorem globalSections_up (n : ℕ) (z : Scheme.G (Spec R) n) :
    (ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u, u + 1} n
        (publicSpecGRingEquiv R n z) =
      (globalSectionsExact R).smallKMap.{u + 1} n z := by
  have hn := DFunLike.congr_fun
    (ExactFunctor.smallKUniverseEquiv_naturality.{u + 1, u} (globalSectionsExact R) n) z
  have hs := DFunLike.congr_fun (publicSpecGRingEquiv_toMonoidHom R n) z
  change publicSpecGRingEquiv R n z = (globalSectionsExact R).smallKMap.{u} n
    ((coherentExactStructure (Spec R)).smallKUniverseEquiv.{u + 1, u} n z) at hs
  change (globalSectionsExact R).smallKMap.{u} n
      ((coherentExactStructure (Spec R)).smallKUniverseEquiv.{u + 1, u} n z) =
    (ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u + 1, u} n
      ((globalSectionsExact R).smallKMap.{u + 1} n z) at hn
  rw [hs, hn]
  exact DFunLike.congr_fun (modelUniverseRoundTrip R n)
    ((globalSectionsExact R).smallKMap.{u + 1} n z)

/-- Canonical upper promotion exposes the original vector-bundle/global-sections exact functor. -/
theorem kToLowerG_upper (n : ℕ) (z : Scheme.K (Spec R) n) :
    (ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u, u + 1} n
        (kToLowerG R n z) = (toModulesExact R).smallKMap.{u + 1} n z := by
  unfold kToLowerG
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [globalSections_up, Scheme.KToG_eq_smallKMap]
  exact (DFunLike.congr_fun (ExactFunctor.smallKMap_comp
    (vectorBundleToCoherentExact (Spec R)) (globalSectionsExact R) n) z).symm

/-- The literal K-to-G/affine map sends each actual scheme unit pair to the proved lower pair. -/
theorem kToLowerG_unitPair (a b : Rˣ) :
    kToLowerG R 2 (unitPair R a b) = DvrSymbols.loweredUnitProduct R a b := by
  let e := (ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u, u + 1} 2
  apply e.injective
  rw [kToLowerG_upper, unitPair_upper_image]
  exact (MulEquiv.apply_symm_apply _ _).symm

section Pid
variable [IsDomain R] [IsPrincipalIdealRing R]

/-- The existing PID comparison followed by the original public affine G-map. -/
def kToLowerGPIDEquiv (n : ℕ) : Scheme.K (Spec R) n ≃* FiniteModuleLocalization.G R n :=
  (Scheme.KToGPIDEquiv R n).trans (publicSpecGRingEquiv R n)

/-- The forward homomorphism is exactly the original K-to-G/affine map. -/
theorem kToLowerGPIDEquiv_toMonoidHom (n : ℕ) :
    (kToLowerGPIDEquiv R n).toMonoidHom = kToLowerG R n := rfl

end Pid

/-- The integer span of the actual scalar/cube unit pairs in original scheme K2. -/
def unitPairSpan : Submodule ℤ (Additive (Scheme.K (Spec R) 2)) :=
  Submodule.span ℤ {z | ∃ a b : Rˣ, z = Additive.ofMul (unitPair R a b)}

private theorem nativeSpan_le_image :
    DvrUnitPairGeneration.unitPairSpan R ≤ (unitPairSpan R).map
      ((kToLowerG R 2).toAdditive.toIntLinearMap) := by
  apply Submodule.span_le.mpr
  rintro z ⟨a, b, rfl⟩
  apply Submodule.mem_map.mpr
  refine ⟨Additive.ofMul (unitPair R a b), Submodule.subset_span ⟨a, b, rfl⟩, ?_⟩
  exact congrArg Additive.ofMul (kToLowerG_unitPair R a b)

section ActualLocalDvr
variable (B : Type u) [CommRing B] [IsDedekindDomain B]
  (p : IsDedekindDomain.HeightOneSpectrum B)
local notation "A" => Localization.AtPrime p.asIdeal
local instance : IsDiscreteValuationRing A :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B p.ne_bot _

/-- Actual unit/cube pairs generate original scheme K2 of the local DVR,
under a genuine section of its original residue ring map. -/
theorem unitPairSpan_eq_top_of_residueSection
    (s : p.asIdeal.ResidueField →+* A)
    (hs : (IsLocalRing.residue A).comp s = RingHom.id p.asIdeal.ResidueField) :
    unitPairSpan (CommRingCat.of A) = ⊤ := by
  let R₀ := CommRingCat.of A
  let L := (kToLowerG R₀ 2).toAdditive.toIntLinearMap
  have hnative : DvrUnitPairGeneration.unitPairSpan A = ⊤ :=
    DvrUnitPairGeneration.unitPairSpan_eq_top_of_residueSection B p s hs
  apply top_unique
  intro z _
  have hz : L z ∈ DvrUnitPairGeneration.unitPairSpan A := by rw [hnative]; trivial
  obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp (nativeSpan_le_image R₀ hz)
  have heq : y = z := by
    apply Additive.toMul.injective
    apply (kToLowerGPIDEquiv R₀ 2).injective
    exact congrArg Additive.toMul he
  exact heq ▸ hy

end ActualLocalDvr

end Quillen.LowDegreeScalarAction.SpecUnitPairs
