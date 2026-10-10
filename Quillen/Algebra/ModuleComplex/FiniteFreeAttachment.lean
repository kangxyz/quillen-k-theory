/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Actual finite-free attachments to highest homology

A map from a projective module to original homology lifts to an actual chain
map from a single complex, with its original homology map identified. Finite
highest homology admits a finite-free attachment. The original distinguished
mapping-cone triangle then lowers the upper cohomological bound by one.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex

namespace Quillen.ModuleComplex
variable {R : Type u} [CommRing R]

/-- A projective map to actual homology is realized by a genuine chain map
from the corresponding single complex. -/
def fromSingleHomologyLift (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (P : ModuleCat.{u} R) [Projective P] (g : P ⟶ K.homology n) :
    (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj P ⟶ K :=
  mkHomFromSingle (Projective.factorThru g (K.homologyπ n) ≫ K.iCycles n)
    (by intro j hj; simp)

/-- The original homology map of the projective chain lift is exactly the prescribed map. -/
lemma fromSingleHomologyLift_homology (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (P : ModuleCat.{u} R) [Projective P] (g : P ⟶ K.homology n) :
    (singleObjHomologySelfIso (.up ℤ) n P).inv ≫
      homologyMap (fromSingleHomologyLift K n P g) n = g := by
  let f := fromSingleHomologyLift K n P g
  have hc : (singleObjCyclesSelfIso (.up ℤ) n P).inv ≫ cyclesMap f n =
      Projective.factorThru g (K.homologyπ n) := by
    rw [← cancel_mono (K.iCycles n), Category.assoc, cyclesMap_i]
    dsimp [f, fromSingleHomologyLift]
    rw [mkHomFromSingle_f, ← Category.assoc, singleObjCyclesSelfIso_inv_iCycles]
    simp
  change (singleObjHomologySelfIso (.up ℤ) n P).inv ≫ homologyMap f n = g
  rw [← singleObjCyclesSelfIso_inv_homologyπ, Category.assoc, homologyπ_naturality,
    ← Category.assoc, hc, Projective.factorThru_comp]

/-- Finite original homology admits an actual finite-free single-complex attachment. -/
lemma exists_finiteFree_single_epi_homology
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [Module.Finite R (K.homology n)] :
    ∃ (m : ℕ) (f : (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R (Fin m → R)) ⟶ K), Epi (homologyMap f n) := by
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin' R (K.homology n)
  let P := ModuleCat.of R (Fin m → R)
  let g' : P ⟶ K.homology n := ModuleCat.ofHom g
  have : Epi g' := (ModuleCat.epi_iff_surjective g').mpr hg
  let f := fromSingleHomologyLift K n P g'
  refine ⟨m, f, ?_⟩
  exact epi_of_epi_fac (fromSingleHomologyLift_homology K n P g')

end Quillen.ModuleComplex

namespace Quillen.DerivedHomComparison
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- An epimorphism on highest homology lowers the upper bound of the third object in the original
  distinguished triangle. -/
lemma isLE_third_of_epi_top_homology (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (n : ℤ) [T.obj₁.IsLE n] [T.obj₂.IsLE n]
    [Epi ((DerivedCategory.homologyFunctor C n).map T.mor₁)] : T.obj₃.IsLE (n-1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  apply (DerivedCategory.HomologySequence.exact₃ T hT i (i+1) rfl).isZero_X₂
  · by_cases hin : i = n
    · subst i
      exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT n).mp inferInstance
    · exact (DerivedCategory.isZero_of_isLE T.obj₂ n i (by omega)).eq_of_src _ _
  · exact (DerivedCategory.isZero_of_isLE T.obj₁ n (i+1) (by omega)).eq_of_tgt _ _

end Quillen.DerivedHomComparison
namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The literal mapping cone lowers the upper cohomological bound after an actual top-homology
  epimorphism. -/
lemma mappingCone_isLE_of_epi_top_homology {P K : CochainComplex C ℤ} (f : P ⟶ K)
    (n : ℤ) [P.IsLE n] [K.IsLE n] [Epi (homologyMap f n)] :
    (CochainComplex.mappingCone f).IsLE (n-1) := by
  let : HasDerivedCategory C := HasDerivedCategory.standard _
  have hepi : Epi ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map f)) := by
    let e := DerivedCategory.homologyFunctorFactors C n
    have h : Epi (((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor C n).map f) ≫ e.hom.app K)
      := by
      rw [e.hom.naturality f]
      change Epi (e.hom.app P ≫ homologyMap f n)
      infer_instance
    exact (epi_comp_iff_of_isIso _ (e.hom.app K)).mp h
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  have : T.obj₁.IsLE n := inferInstanceAs ((DerivedCategory.Q.obj P).IsLE n)
  have : T.obj₂.IsLE n := inferInstanceAs ((DerivedCategory.Q.obj K).IsLE n)
  have : Epi ((DerivedCategory.homologyFunctor C n).map T.mor₁) := hepi
  rw [← DerivedCategory.isLE_Q_obj_iff]
  exact DerivedHomComparison.isLE_third_of_epi_top_homology T
    (DerivedCategory.mappingCone_triangle_distinguished f) n

end Quillen.CochainComplex
namespace Quillen.ModuleComplex
variable {R : Type u} [CommRing R]

/-- Attach a finite-free single complex to finite highest homology and lower the literal cone bound
  by one. -/
lemma exists_finiteFree_single_lowering_top
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [K.IsLE n]
    [Module.Finite R (K.homology n)] :
    ∃ (m : ℕ) (f : (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R (Fin m → R)) ⟶ K),
      Epi (homologyMap f n) ∧ (CochainComplex.mappingCone f).IsLE (n-1) := by
  obtain ⟨m, f, hf⟩ := exists_finiteFree_single_epi_homology K n
  exact ⟨m, f, hf, Quillen.CochainComplex.mappingCone_isLE_of_epi_top_homology f n⟩

end Quillen.ModuleComplex
