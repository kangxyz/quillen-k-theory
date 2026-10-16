/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Resolution.Property
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction

/-!
# Projective dimension on actual affine charts

Restriction and global sections give an exact finite chart-module functor. Finite local freeness is
equivalent to chart-module projectivity, and vector-bundle quotients lower projective dimension of
coherent syzygies.-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} [IsLocallyNoetherian X]
  (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j]

/-- Restrict a genuine coherent sheaf to an affine chart, take its finite
module under the tilde equivalence, and forget finiteness. -/
def coherentChartModule : AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X ⥤
  ModuleCat.{u} R := by
  letI := AlgebraicGeometry.Scheme.Modules.Coherent.noetherian_affineChart R j
  exact AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesRestriction j ⋙
    (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence
      R).functor ⋙
      (ModuleCat.finiteModule R).ι

instance coherentChartModule_additive : (coherentChartModule R j).Additive := by
  have := AlgebraicGeometry.Scheme.Modules.Coherent.noetherian_affineChart R j
  let E := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence R
  let := preservesBinaryBiproducts_of_preservesBinaryProducts E.functor
  have : E.functor.Additive := Functor.additive_of_preservesBinaryBiproducts _
  dsimp [coherentChartModule]
  infer_instance

/-- Actual global coherent short exact sequences stay exact in the module
category of an affine chart. -/
theorem coherentChartModule_shortExact (S : ShortComplex
  (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X))
    (hS : S.ShortExact) : (S.map (coherentChartModule R j)).ShortExact := by
  have := AlgebraicGeometry.Scheme.Modules.Coherent.noetherian_affineChart R j
  exact ((hS.map_of_exact
    (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesRestriction j)).map_of_exact
    (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence
      R).functor).map_of_exact
      (ModuleCat.finiteModule R).ι

/-- Finite local freeness on the affine chart is exactly projectivity of
its finite section module, expressed in the ambient module category. -/
theorem coherentChartModule_projective_iff (M :
  AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X) :
    Projective ((coherentChartModule R j).obj M) ↔
      IsFiniteLocallyFree (Spec R) (M.obj.restrict j) := by
  have := AlgebraicGeometry.Scheme.Modules.Coherent.noetherian_affineChart R j
  let N := (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesRestriction j).obj M
  change Projective
    (((AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence
    R).functor.obj N).obj)
    ↔
    coherentVectorBundle (Spec R) N
  exact (IsProjective.iff_projective
    (((AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence
      R).functor.obj N).obj)).symm.trans
      (coherentVectorBundle_iff_projective R N).symm

/-- A global vector bundle gives a projective module on every affine chart;
no global sheaf-projectivity assertion is made. -/
theorem coherentChartModule_projective (M :
  AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X)
    (hM : coherentVectorBundle X M) : Projective ((coherentChartModule R j).obj M) := by
  have : IsFiniteLocallyFree X M.obj := hM
  exact (coherentChartModule_projective_iff R j M).mpr (finiteLocallyFree_restrict j M.obj)

/-- Each genuine global vector-bundle cover drops the local projective
dimension of its coherent kernel by one on every affine chart. -/
theorem coherentChartModule_syzygy (S : ShortComplex
  (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X))
    (hS : S.ShortExact) (hP : coherentVectorBundle X S.X₂) (n : ℕ)
    [HasProjectiveDimensionLE ((coherentChartModule R j).obj S.X₃) (n + 1)] :
    HasProjectiveDimensionLE ((coherentChartModule R j).obj S.X₁) n := by
  have hdim : HasProjectiveDimensionLT (S.map (coherentChartModule R j)).X₃ (n + 2) := by
    change HasProjectiveDimensionLE ((coherentChartModule R j).obj S.X₃) (n + 1)
    infer_instance
  exact ((coherentChartModule_shortExact R j S hS).hasProjectiveDimensionLT_X₃_iff n
    (coherentChartModule_projective R j S.X₂ hP)).mp hdim

/-- The actual chart module is finite. -/
instance coherentChartModule_finite (M :
  AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X) :
    Module.Finite R ((coherentChartModule R j).obj M) := by
  have := AlgebraicGeometry.Scheme.Modules.Coherent.noetherian_affineChart R j
  change Module.Finite R
    (((AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence
      R).functor.obj
      ((AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesRestriction j).obj M)).obj)
  infer_instance

end AlgebraicGeometry.Scheme.Modules
