/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.RestrictionBounds


public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.SingleCycles


public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.LowerModels


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.DerivedRoofs
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Single
public import Aglib.AlgebraicGeometry.Modules.Complex.Homology
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Homology
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Charts
public import Quillen.Aglib.Algebra.Homology.ModuleCat.FiniteFreeAttachment
public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.KernelClosure
public import Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.AcyclicCycles
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.Algebra.Homology.CochainComplex.Cycles
/-! # Finite attachments with an explicit local lower bound

The actual cone of an attachment strictly above a local lower term bound
retains that bound on each affine chart. Highest-homology surjectivity lowers
the upper cohomological bound. The existence of a global finite locally free
attachment is a separate geometric step.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open HomologicalComplex
open AlgebraicGeometry.Scheme.ProjectiveLine AlgebraicGeometry.Scheme.Modules
namespace Quillen.PerfectComplexes.ProjectiveLine

attribute [local instance] finiteAttachmentStandard

/-- The two original polynomial charts have genuine strict derived models with one
common lower term bound. No global strict model is included in this predicate. -/
def twoChartStrictLowerModels (R : CommRingCat.{u}) (K : CochainComplex (twoChartLine R).Modules ℤ)
    (a : ℤ) : Prop :=
  affineStrictLowerModel (.of (Polynomial R))
    ((restrict (plusChart R)).obj K) a ∧
  affineStrictLowerModel (.of (Polynomial R))
    ((restrict (minusChart R)).obj K) a

/-- Every original locally perfect object on the two-chart line has one common
lower term bound for genuine models on both whole polynomial charts. -/
theorem exists_twoChartStrictLowerModels (R : CommRingCat.{u})
    {K : CochainComplex (twoChartLine R).Modules ℤ} (hK : locallyPerfect (twoChartLine R) K) :
    ∃ a : ℤ, twoChartStrictLowerModels R K a := by
  obtain ⟨P, ⟨eP⟩⟩ := Affine.locallyPerfect_exists_strictPerfect_representative
    (.of (Polynomial R)) (locallyPerfect_restrict (plusChart R) hK)
  obtain ⟨N, ⟨eN⟩⟩ := Affine.locallyPerfect_exists_strictPerfect_representative
    (.of (Polynomial R)) (locallyPerfect_restrict (minusChart R) hK)
  obtain ⟨a, b, hab⟩ := P.property.1
  obtain ⟨c, d, hcd⟩ := N.property.1
  exact ⟨min a c, ⟨P, fun i hi => hab i (Or.inl (lt_of_lt_of_le hi (min_le_left _ _))),
    ⟨eP.symm⟩⟩, ⟨N, fun i hi => hcd i (Or.inl (lt_of_lt_of_le hi (min_le_right _ _))),
    ⟨eN.symm⟩⟩⟩

/-- The genuine local lower models make the terminal homology a global
finite locally free sheaf on the original projective line. -/
theorem finiteLocallyFree_homology_of_twoChartStrictLowerModels
    (R : CommRingCat.{u}) (K : CochainComplex (twoChartLine R).Modules ℤ) (a : ℤ) [K.IsLE a]
    (hK : twoChartStrictLowerModels R K a) :
    IsFiniteLocallyFree (twoChartLine R) (K.homology a) := by
  let j : Bool → (Spec (.of (Polynomial R)) ⟶ twoChartLine R) :=
    fun b => if b then plusChart R else minusChart R
  let (b : Bool) : IsOpenImmersion (j b) := by cases b <;> dsimp [j] <;> infer_instance
  apply finiteLocallyFree_of_affineCharts (K.homology a)
    (fun _ : Bool => CommRingCat.of (Polynomial R)) j
  · intro x
    rcases charts_jointly_surjective R x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨true, y, hy⟩
    · exact ⟨false, y, hy⟩
  · intro b
    have hlocal : affineStrictLowerModel (.of (Polynomial R)) ((restrict (j b)).obj K) a := by
      cases b
      · exact hK.2
      · exact hK.1
    have := restrict_isLE (j b) K a
    have := finiteLocallyFree_homology_of_affineStrictLowerModel (.of (Polynomial R))
      ((restrict (j b)).obj K) a hlocal
    exact finiteLocallyFree_of_iso (restrictHomologyIso (j b) K a)

/-- A finite locally free top attachment preserves the genuine local lower term
bound and decreases the upper cohomological bound by one. The epimorphism is an
explicit input; constructing it globally is a separate geometric obligation. -/
theorem twoChartStrictLowerModels_mappingCone_single
    (R : CommRingCat.{u}) (K : CochainComplex (twoChartLine R).Modules ℤ)
    (V : (twoChartLine R).Modules)
    [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree (twoChartLine R) V]
    (a b : ℤ) (hab : a < b) [K.IsLE b]
    (hK : twoChartStrictLowerModels R K a)
    (f : (CochainComplex.singleFunctor _ b).obj V ⟶ K)
    [Epi (homologyMap f b)] :
    (CochainComplex.mappingCone f).IsLE (b - 1) ∧
      twoChartStrictLowerModels R (CochainComplex.mappingCone f) a := by
  let P : StrictPerfect (twoChartLine R) :=
    ⟨_, single_strictPerfect_int V b⟩
  have hP (i : ℤ) (hi : i < a + 1) : IsZero (P.obj.X i) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  refine ⟨Quillen.CochainComplex.mappingCone_isLE_of_epi_top_homology f b, ?_, ?_⟩
  · exact affineStrictLowerModel_restrict_mappingCone
      (plusChart R) P f a hP hK.1
  · exact affineStrictLowerModel_restrict_mappingCone
      (minusChart R) P f a hP hK.2

/-- The actual top attachment has strict derived cone models in the smaller
closed interval [a,b-1] on each original chart. This is the finite decreasing
amplitude assertion needed by induction. -/
theorem twoChartStrictLowerModels_mappingCone_single_windows
    (R : CommRingCat.{u}) (K : CochainComplex (twoChartLine R).Modules ℤ)
    (V : (twoChartLine R).Modules) [IsFiniteLocallyFree (twoChartLine R) V]
    (a b : ℤ) (hab : a < b) [K.IsLE b] (hK : twoChartStrictLowerModels R K a)
    (f : (CochainComplex.singleFunctor _ b).obj V ⟶ K) [Epi (homologyMap f b)]
    (j : Spec (.of (Polynomial R)) ⟶ twoChartLine R) [IsOpenImmersion j]
    (hj : j = plusChart R ∨ j = minusChart R) :
      ∃ P : StrictPerfect (Spec (.of (Polynomial R))),
        (∀ i, i < a ∨ b - 1 < i → IsZero (P.obj.X i)) ∧
        Nonempty ((DerivedCategory.Q).obj ((restrict j).obj (CochainComplex.mappingCone f)) ≅
          (DerivedCategory.Q).obj P.obj) := by
  obtain ⟨hupper, hmodels⟩ := twoChartStrictLowerModels_mappingCone_single R K V a b hab hK f
  have : (CochainComplex.mappingCone f).IsLE (b - 1) := hupper
  rcases hj with rfl | rfl
  · have := restrict_isLE (plusChart R) (CochainComplex.mappingCone f) (b - 1)
    exact affineStrictLowerModel_exists_window _ _ a (b - 1) (by omega) hmodels.1
  · have := restrict_isLE (minusChart R) (CochainComplex.mappingCone f) (b - 1)
    exact affineStrictLowerModel_exists_window _ _ a (b - 1) (by omega) hmodels.2

/-- The terminal stage has an actual finite locally free single-complex
quasi-isomorphism into the original representative. No global projectivity
of that vector bundle is assumed. -/
theorem terminal_single_vectorBundle_model
    (R : CommRingCat.{u}) (K : CochainComplex (twoChartLine R).Modules ℤ) (a : ℤ)
    [K.IsStrictlyGE a] [K.IsLE a] (hK : twoChartStrictLowerModels R K a) :
    IsFiniteLocallyFree (twoChartLine R) (K.cycles a) ∧
      QuasiIso (singleCyclesMap K a) := by
  have := finiteLocallyFree_homology_of_twoChartStrictLowerModels R K a hK
  refine ⟨?_, singleCyclesMap_quasiIso K a⟩
  exact finiteLocallyFree_of_iso (K.isoHomologyπ (a - 1) a (by simp)
    ((K.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _)).symm

end Quillen.PerfectComplexes.ProjectiveLine
