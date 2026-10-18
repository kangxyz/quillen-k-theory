/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.SpecUnitPairs
public import Quillen.KTheory.LowDegreeScalarAction.MilnorDvrBoundary
public import Quillen.AlgebraicGeometry.Scheme.Pullback
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.LocalizationNaturality
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Original generic and closed K-pullback values of actual scalar unit pairs

The original geometric pullback is exact on vector bundles, including for a
nonflat residue map. Its target global sections compare with ordinary scalar
extension by the existing affine functor isomorphism. This gives genuine
scalar-component compatibility and the actual image of the original rank-one
line. The existing identity-scalar operations and positive cube calibration
then retain the ordered coefficient images under original scheme K-pullback.

Only target K-to-G and affine comparison are applied. No coherent G-pullback
along the residue map, Milnor injectivity, inverse Matsumoto equivalence, or
negative R5 normalization is used.
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
open scoped ZeroObject TensorProduct ChangeOfRings

namespace Quillen.LowDegreeScalarAction.SpecUnitPairNaturality

attribute [local instance] Abelian.hasFiniteBiproducts

variable {R S : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing S] (φ : R ⟶ S)

/-- The source structural scalar is exactly the frozen scheme-pair scalar. -/
local instance sourceLinear : Linear R (Spec R).Modules := SpecUnitPairs.modulesLinear R

/-- Actual vector-bundle pullback followed by target-only original global sections. -/
def pullbackToModulesExact : ExactFunctor (vectorBundleExactStructure (Spec R))
    (ModuleCat.finiteModuleExactStructure.{u, u} S) :=
  (vectorBundleExactPullback (Spec.map φ)).comp (SpecUnitPairs.toModulesExact S)

private def sectionsExtensionIso :
    (pullbackToModulesExact φ).toFunctor ⋙ forget₂ (FGModuleCat S) (ModuleCat S) ≅
      (SpecUnitPairs.toModulesExact R).toFunctor ⋙ forget₂ (FGModuleCat R) (ModuleCat R) ⋙
        ModuleCat.extendScalars φ.hom :=
  Functor.isoWhiskerLeft (vectorBundleToCoherent (Spec R))
    (coherentPullbackGlobalSectionsExtensionIso φ)

omit [IsNoetherianRing R] [IsNoetherianRing S] in
private theorem extend_scalar_component (M : ModuleCat.{u} R) (a : Rˣ) :
    (ModuleCat.extendScalars φ.hom).map ((scalarNatAut R (ModuleCat.{u} R) a).hom.app M) =
      (scalarNatAut S (ModuleCat.{u} S) (Units.map φ.hom.toMonoidHom a)).hom.app
        ((ModuleCat.extendScalars φ.hom).obj M) := by
  let _ := φ.hom.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s m =>
    let s₀ : S := s
    change s₀ ⊗ₜ[R] ((a : R) • m) = (φ.hom (a : R) * s₀) ⊗ₜ[R] m
    rw [TensorProduct.tmul_smul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem ordinary_scalar_component (a : Rˣ) (X : FiniteLocallyFree (Spec R)) :
    (pullbackToModulesExact φ).toFunctor.map
        ((scalarNatAut R (FiniteLocallyFree (Spec R)) a).hom.app X) =
      (scalarNatAut S (FGModuleCat.{u} S) (Units.map φ.hom.toMonoidHom a)).hom.app
        ((pullbackToModulesExact φ).toFunctor.obj X) := by
  let e := sectionsExtensionIso φ
  let G := (SpecUnitPairs.toModulesExact R).toFunctor ⋙
    forget₂ (FGModuleCat R) (ModuleCat R)
  let T := G ⋙ ModuleCat.extendScalars φ.hom
  let r := (scalarNatAut R (FiniteLocallyFree (Spec R)) a).hom.app X
  have hR : G.map r = (scalarNatAut R (ModuleCat.{u} R) a).hom.app (G.obj X) :=
    scalarNatAut_map R G a X
  have hT : T.map r =
      (scalarNatAut S (ModuleCat.{u} S) (Units.map φ.hom.toMonoidHom a)).hom.app (T.obj X) := by
    change (ModuleCat.extendScalars φ.hom).map (G.map r) = _
    rw [hR]
    exact extend_scalar_component φ (G.obj X) a
  apply (ModuleCat.finiteModule S).ι.map_injective
  change ((pullbackToModulesExact φ).toFunctor ⋙
    forget₂ (FGModuleCat S) (ModuleCat S)).map r =
      (scalarNatAut S (ModuleCat.{u} S) (Units.map φ.hom.toMonoidHom a)).hom.app
        (((pullbackToModulesExact φ).toFunctor ⋙
          forget₂ (FGModuleCat S) (ModuleCat S)).obj X)
  apply (cancel_mono (e.hom.app X)).mp
  have hn := e.hom.naturality r
  change ((pullbackToModulesExact φ).toFunctor ⋙
    forget₂ (FGModuleCat S) (ModuleCat S)).map r ≫ e.hom.app X =
      e.hom.app X ≫ T.map r at hn
  rw [hT] at hn
  exact hn.trans ((scalarNatAut S (ModuleCat.{u} S)
    (Units.map φ.hom.toMonoidHom a)).hom.naturality (e.hom.app X))

private theorem small_scalar_component (a : Rˣ)
    (X : SmallModel.{u + 1} (FiniteLocallyFree (Spec R))) :
    (pullbackToModulesExact φ).smallModel.{u + 1}.toFunctor.map
        ((smallModelScalarNatAut.{u, u + 1, u, u + 1} R
          (FiniteLocallyFree (Spec R)) a).hom.app X) =
      (smallModelScalarNatAut.{u, u + 1, u, u + 1} S (FGModuleCat.{u} S)
        (Units.map φ.hom.toMonoidHom a)).hom.app
          ((pullbackToModulesExact φ).smallModel.{u + 1}.toFunctor.obj X) := by
  change (equivSmallModel.{u + 1} (FGModuleCat.{u} S)).functor.map
    ((pullbackToModulesExact φ).toFunctor.map
      ((equivSmallModel.{u + 1} (FiniteLocallyFree (Spec R))).inverse.map
        ((smallModelScalarNatAut.{u, u + 1, u, u + 1} R
          (FiniteLocallyFree (Spec R)) a).hom.app X))) = _
  rw [smallModelScalarNatAut_map_hom]
  change (equivSmallModel.{u + 1} (FGModuleCat.{u} S)).functor.map
    ((pullbackToModulesExact φ).toFunctor.map
      ((scalarNatAut R (FiniteLocallyFree (Spec R)) a).hom.app
        ((equivSmallModel.{u + 1} (FiniteLocallyFree (Spec R))).inverse.obj X))) = _
  rw [ordinary_scalar_component]
  exact smallModelScalarNatAut_functor_map_hom.{u, u + 1, u, u + 1}
    S (FGModuleCat.{u} S) (Units.map φ.hom.toMonoidHom a) _

private theorem scalarZero_natural (a : Rˣ) (z : Scheme.K (Spec R) 0) :
    (pullbackToModulesExact φ).smallKMap.{u + 1} 1
        (ScalarUnit.smallModelKZeroAction.{u, u + 1, u, u + 1} R
          (vectorBundleExactStructure (Spec R)) a z) =
      ScalarUnit.upperFiniteModuleKZeroAction S (Units.map φ.hom.toMonoidHom a)
        ((pullbackToModulesExact φ).smallKMap.{u + 1} 0 z) :=
  ExactNaturality.kZeroAction_natural.{u + 1, u + 1}
    (pullbackToModulesExact φ).smallModel.{u + 1}
    (smallModelScalarNatAut.{u, u + 1, u, u + 1} R (FiniteLocallyFree (Spec R)) a)
    (smallModelScalarNatAut.{u, u + 1, u, u + 1} S (FGModuleCat.{u} S)
      (Units.map φ.hom.toMonoidHom a))
    (small_scalar_component φ a) z

private theorem scalarOne_natural (a : Rˣ) (z : Scheme.K (Spec R) 1) :
    (pullbackToModulesExact φ).smallKMap.{u + 1} 2
        (ScalarUnit.smallModelKOneAction.{u, u + 1, u, u + 1} R
          (vectorBundleExactStructure (Spec R)) a z) =
      ScalarUnit.upperFiniteModuleKOneAction S (Units.map φ.hom.toMonoidHom a)
        ((pullbackToModulesExact φ).smallKMap.{u + 1} 1 z) :=
  ExactNaturality.kOneAction_natural.{u + 1, u + 1}
    (pullbackToModulesExact φ).smallModel.{u + 1}
    (smallModelScalarNatAut.{u, u + 1, u, u + 1} R (FiniteLocallyFree (Spec R)) a)
    (smallModelScalarNatAut.{u, u + 1, u, u + 1} S (FGModuleCat.{u} S)
      (Units.map φ.hom.toMonoidHom a))
    (small_scalar_component φ a) z

private def extendRankOneIso :
    (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of R (Fin 1 → R)) ≅
      ModuleCat.of S (Fin 1 → S) := by
  letI := φ.hom.toAlgebra
  exact ModuleCat.extendScalarsAlgebraObjIso R S (ModuleCat.of R (Fin 1 → R)) ≪≫
    (TensorProduct.piScalarRight R S S (Fin 1)).toModuleIso

private def rankOneImageIso :
    (pullbackToModulesExact φ).toFunctor.obj (SpecUnitPairs.rankOneBundle R) ≅
      FGModuleCat.of S (Fin 1 → S) :=
  ObjectProperty.isoMk _
    ((sectionsExtensionIso φ).app (SpecUnitPairs.rankOneBundle R) ≪≫
      (ModuleCat.extendScalars φ.hom).mapIso
        ((tildeEquiv (R := R)).unitIso.app (ModuleCat.of R (Fin 1 → R))).symm ≪≫
      extendRankOneIso φ)

private theorem rankOneObjectClass_image :
    (pullbackToModulesExact φ).smallKMap.{u + 1} 0 (SpecUnitPairs.rankOneObjectClass R) =
      DvrSymbols.upperRankOneClass S := by
  unfold SpecUnitPairs.rankOneObjectClass DvrSymbols.upperRankOneClass
  change (pullbackToModulesExact φ).smallModel.{u + 1}.KMap 0 _ = _
  rw [ExactFunctor.KMap_kZeroObjectClass]
  apply ExactStructure.kZeroObjectClass_iso
  exact (equivSmallModel.{u + 1} (FGModuleCat.{u} S)).functor.mapIso
    (((pullbackToModulesExact φ).toFunctor.mapIso
      ((equivSmallModel.{u + 1} (FiniteLocallyFree (Spec R))).unitIso.app
        (SpecUnitPairs.rankOneBundle R))).symm ≪≫ rankOneImageIso φ)

/-- The original positive rank-one cube keeps its positive mapped scalar value. -/
theorem positiveLineUnit_image (b : Rˣ) :
    (pullbackToModulesExact φ).smallKMap.{u + 1} 1 (SpecUnitPairs.positiveLineUnit R b) =
      DvrSymbols.upperUnitKOne S (Units.map φ.hom.toMonoidHom b) := by
  rw [SpecUnitPairs.positiveLineUnit_eq_inverse_objectAction, map_inv,
    scalarZero_natural, rankOneObjectClass_image]
  rfl

/-- Actual vector-bundle K-pullback followed by target global sections preserves the pair. -/
theorem unitPair_upper_image (a b : Rˣ) :
    (pullbackToModulesExact φ).smallKMap.{u + 1} 2 (SpecUnitPairs.unitPair R a b) =
      DvrSymbols.upperUnitProduct S (Units.map φ.hom.toMonoidHom a)
        (Units.map φ.hom.toMonoidHom b) := by
  unfold SpecUnitPairs.unitPair
  rw [scalarOne_natural, positiveLineUnit_image]
  rfl

omit [IsNoetherianRing R] in
private theorem pullback_targetComparison_upper (n : ℕ) (z : Scheme.K (Spec R) n) :
    (ModuleCat.finiteModuleExactStructure.{u, u} S).smallKUniverseEquiv.{u, u + 1} n
        (SpecUnitPairs.kToLowerG S n (Scheme.pullbackK (Spec.map φ) n z)) =
      (pullbackToModulesExact φ).smallKMap.{u + 1} n z := by
  rw [SpecUnitPairs.kToLowerG_upper, Scheme.pullbackK_eq_smallKMap]
  exact (DFunLike.congr_fun (ExactFunctor.smallKMap_comp
    (vectorBundleExactPullback (Spec.map φ)) (SpecUnitPairs.toModulesExact S) n) z).symm

/-- Original K-pullback first, then target-only KToG and affine comparison,
has the literal lower ring-unit-product value for any Noetherian ring map. -/
theorem pullback_unitPair_lower_value (a b : Rˣ) :
    SpecUnitPairs.kToLowerG S 2
        (Scheme.pullbackK (Spec.map φ) 2 (SpecUnitPairs.unitPair R a b)) =
      DvrSymbols.loweredUnitProduct S (Units.map φ.hom.toMonoidHom a)
        (Units.map φ.hom.toMonoidHom b) := by
  let e := (ModuleCat.finiteModuleExactStructure.{u, u} S).smallKUniverseEquiv.{u, u + 1} 2
  apply e.injective
  rw [pullback_targetComparison_upper, unitPair_upper_image]
  exact (MulEquiv.apply_symm_apply _ _).symm

section FieldTarget
variable (L : Type u) [Field L] (f : R →+* L)

/-- At a field target, the original pullback of the same actual pair equals
the actual target scalar/cube pair, using only the existing field K/G comparison. -/
theorem pullback_unitPair_field :
    ∀ a b : Rˣ,
    Scheme.pullbackK (Spec.map (CommRingCat.ofHom f)) 2 (SpecUnitPairs.unitPair R a b) =
      SpecUnitPairs.unitPair (CommRingCat.of L) (Units.map f.toMonoidHom a)
        (Units.map f.toMonoidHom b) := by
  intro a b
  let φ₀ : R ⟶ CommRingCat.of L := CommRingCat.ofHom f
  apply (SpecUnitPairs.kToLowerGPIDEquiv (CommRingCat.of L) 2).injective
  change SpecUnitPairs.kToLowerG (CommRingCat.of L) 2
    (Scheme.pullbackK (Spec.map φ₀) 2 (SpecUnitPairs.unitPair R a b)) =
      SpecUnitPairs.kToLowerG (CommRingCat.of L) 2 _
  rw [pullback_unitPair_lower_value φ₀ a b, SpecUnitPairs.kToLowerG_unitPair]
  rfl

/-- The literal mapped ordered Milnor symbol is the original field-comparison
value of the original K-pullback. No Milnor inverse or injectivity is used. -/
theorem pullback_unitPair_milnor (a b : Rˣ) :
    Additive.ofMul (SpecUnitPairs.kToLowerG (CommRingCat.of L) 2
      (Scheme.pullbackK (Spec.map (CommRingCat.ofHom f)) 2 (SpecUnitPairs.unitPair R a b))) =
      MilnorDvrBoundary.milnorToLowerModuleKTwo L
        (MilnorK.symbol ![Units.map f.toMonoidHom a, Units.map f.toMonoidHom b]) := by
  let φ₀ : R ⟶ CommRingCat.of L := CommRingCat.ofHom f
  change Additive.ofMul (SpecUnitPairs.kToLowerG (CommRingCat.of L) 2
    (Scheme.pullbackK (Spec.map φ₀) 2 (SpecUnitPairs.unitPair R a b))) = _
  rw [pullback_unitPair_lower_value φ₀ a b,
    MilnorDvrBoundary.milnorToLowerModuleKTwo_pair]
  rfl

end FieldTarget

section ActualLocalDvr
variable (B : Type u) [CommRing B] [IsDedekindDomain B]
  (p : IsDedekindDomain.HeightOneSpectrum B)
local notation "A" => Localization.AtPrime p.asIdeal

/-- For any given field algebra, in particular the supplied actual fraction
field, the literal original generic ring map has the mapped ordered-symbol value. -/
theorem generic_unitPair_milnor (K : Type u) [Field K]
    [Algebra (Localization.AtPrime p.asIdeal) K] (a b : Aˣ) :
    Additive.ofMul (SpecUnitPairs.kToLowerG (CommRingCat.of K) 2
      (Scheme.pullbackK (Spec.map (CommRingCat.ofHom (algebraMap A K))) 2
        (SpecUnitPairs.unitPair (CommRingCat.of A) a b))) =
      MilnorDvrBoundary.milnorToLowerModuleKTwo K
        (MilnorK.symbol ![Units.map (algebraMap A K).toMonoidHom a,
          Units.map (algebraMap A K).toMonoidHom b]) :=
  pullback_unitPair_milnor (R := CommRingCat.of A) K (algebraMap A K) a b

/-- The actual residue map is applied to original scheme K first. Its target
field KToG/affine value is the literal ordered symbol of the two reduced units. -/
theorem closed_unitPair_milnor (a b : Aˣ) :
    Additive.ofMul (SpecUnitPairs.kToLowerG (CommRingCat.of p.asIdeal.ResidueField) 2
      (Scheme.pullbackK (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) 2
        (SpecUnitPairs.unitPair (CommRingCat.of A) a b))) =
      MilnorDvrBoundary.milnorToLowerModuleKTwo p.asIdeal.ResidueField
        (MilnorK.symbol ![Units.map (IsLocalRing.residue A).toMonoidHom a,
          Units.map (IsLocalRing.residue A).toMonoidHom b]) :=
  pullback_unitPair_milnor (R := CommRingCat.of A)
    p.asIdeal.ResidueField (IsLocalRing.residue A) a b

end ActualLocalDvr

end Quillen.LowDegreeScalarAction.SpecUnitPairNaturality
