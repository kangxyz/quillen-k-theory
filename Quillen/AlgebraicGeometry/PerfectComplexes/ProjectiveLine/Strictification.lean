/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.RestrictionBounds


public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.SingleCycleLift


public import Quillen.Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteFreeLift


public import Quillen.Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.SectionDenominators


public import Quillen.Aglib.AlgebraicGeometry.Modules.Restriction.UnitSections


public import Quillen.Aglib.AlgebraicGeometry.Modules.Restriction.GraphGluing


public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Reassembly


public import Quillen.Aglib.Algebra.Homology.DerivedCategory.TopSingleRepresentative


public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Homology
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Single
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Closure
public import Quillen.Aglib.AlgebraicGeometry.Modules.RankOne.Gluing
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Tautological
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FiniteAttachment
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.ChartAffineness
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteGenerators
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.Restriction.Overlap
public import Aglib.AlgebraicGeometry.Modules.Subobjects.Gluing
/-! # Actual graph attachments and strict reassembly on the projective line

The local maps and denominator equations retain their original geometric
morphisms. Strict reassembly uses only chain realization into a top single,
not global projectivity of vector bundles or unrestricted chain realization.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.ProjectiveLine


open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
  AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

attribute [local instance] reassemblyStandard

/-- A compatible pair of actual chart sections, with transition T^n, is
realized by a genuine global map from a finite locally free rank-one sheaf.
The construction glues graph subobjects inside the unit square times M. -/
theorem exists_vectorBundle_map_of_compatible_chart_maps
    (R : CommRingCat.{u}) (M : (twoChartLine R).Modules) (n : ℕ)
    (f : (SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf) ⟶
      M.restrict (plusChart R))
    (g : (SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf) ⟶
      M.restrict (minusChart R))
    (hfg : (Scheme.Modules.restrictFunctor
        (pullback.fst (plusChart R) (minusChart R))).map f ≫
        (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso (plusChart R) (minusChart
          R)).hom.app M =
      (columnTransition (plusChart R) (minusChart R) (overlapCoordinateUnit R ^ n)).hom ≫
        (Scheme.Modules.restrictFunctor
          (pullback.snd (plusChart R) (minusChart R))).map g) :
    ∃ (V : (twoChartLine R).Modules) (p : V ⟶ M), IsFiniteLocallyFree (twoChartLine R) V ∧
      ∃ (eU : V.restrict (plusChart R) ≅
          SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf)
        (eV : V.restrict (minusChart R) ≅
          SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf),
        (Scheme.Modules.restrictFunctor (plusChart R)).map p = eU.hom ≫ f ∧
        (Scheme.Modules.restrictFunctor (minusChart R)).map p = eV.hom ≫ g := by
  have hplus : (pullback.fst (plusChart R) (minusChart R)).appTop.hom
      (polynomialCoordinate R ^ n) = ↑(overlapCoordinateUnit R ^ n) := by
    simp only [map_pow, Units.val_pow_eq_pow_val]
    rfl
  have hminus : (pullback.snd (plusChart R) (minusChart R)).appTop.hom
      (polynomialCoordinate R ^ n) = ↑((overlapCoordinateUnit R ^ n)⁻¹) := by
    simp only [map_pow, ← inv_pow, Units.val_pow_eq_pow_val]
    rfl
  let := firstColumn_mono (plusChart R) (polynomialCoordinate R ^ n)
  let := secondColumn_mono (minusChart R) (polynomialCoordinate R ^ n)
  obtain ⟨V, p, eU, eV, hU, hV⟩ := exists_glued_graph_map (plusChart R) (minusChart R)
    (firstColumn (plusChart R) (polynomialCoordinate R ^ n))
    (secondColumn (minusChart R) (polynomialCoordinate R ^ n)) f g
    (columnTransition (plusChart R) (minusChart R) (overlapCoordinateUnit R ^ n))
    (columns_compatible (plusChart R) (minusChart R)
      (polynomialCoordinate R ^ n) (polynomialCoordinate R ^ n)
      (overlapCoordinateUnit R ^ n) hplus hminus) hfg
  refine ⟨V, p, ?_, eU, eV, hU, hV⟩
  let j : Bool → (Spec (.of (Polynomial R)) ⟶ twoChartLine R) :=
    fun b => if b then plusChart R else minusChart R
  let (b : Bool) : IsOpenImmersion (j b) := by cases b <;> dsimp [j] <;> infer_instance
  apply finiteLocallyFree_of_affineCharts V (fun _ : Bool => CommRingCat.of (Polynomial R)) j
  · intro x
    rcases charts_jointly_surjective R x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨true, y, hy⟩
    · exact ⟨false, y, hy⟩
  · intro b
    have : IsFiniteLocallyFree (Spec (.of (Polynomial R)))
        (SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf) := by
      let e : SheafOfModules.free
          (R := (Spec (.of (Polynomial R))).ringCatSheaf) (ULift.{u} Unit) ≅
          SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf := coproductUniqueIso _
      exact finiteLocallyFree_of_iso e
    cases b
    · exact finiteLocallyFree_of_iso eV.symm
    · exact finiteLocallyFree_of_iso eU.symm


/-- Every actual map from the positive-chart unit into a quasicoherent sheaf
extends from a genuine global vector bundle, preserving that exact chart map. -/
theorem exists_vectorBundle_lift_plus (R : CommRingCat.{u})
    (M : (twoChartLine R).Modules) [M.IsQuasicoherent]
    (f : (SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf) ⟶
      M.restrict (plusChart R)) :
    ∃ (V : (twoChartLine R).Modules) (g : V ⟶ M), IsFiniteLocallyFree (twoChartLine R) V ∧
      ∃ e : V.restrict (plusChart R) ≅
        SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf,
        (Scheme.Modules.restrictFunctor (plusChart R)).map g = e.hom ≫ f := by
  let j := plusChart R
  let k := minusChart R
  let p := pullback.fst j k
  let q := pullback.snd j k
  let u : (SheafOfModules.unit (pullback j k).ringCatSheaf) ⟶
      (M.restrict k).restrict q :=
    (Scheme.Modules.restrictUnitIso p).inv ≫ (Scheme.Modules.restrictFunctor p).map f ≫
      (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.app M
  have hq : q ''ᵁ ⊤ = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) := by
    rw [q.image_top_eq_opensRange]
    dsimp only [q]
    rw [Scheme.Hom.opensRange_pullbackSnd]
    exact (minusChart_preimage_plusRange R).trans
      (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus_opensRange R)
  obtain ⟨n, g, hg⟩ := exists_unit_map_denominator q (M.restrict k) Polynomial.X hq u
  have hcoord : q.appTop.hom ((Scheme.ΓSpecIso (.of (Polynomial R))).inv.hom
      (Polynomial.X ^ n)) = ↑((overlapCoordinateUnit R ^ n)⁻¹) := by
    simp only [map_pow, ← inv_pow, Units.val_pow_eq_pow_val]
    rfl
  have hfg : (Scheme.Modules.restrictFunctor p).map f ≫
        (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.app M =
      (columnTransition j k (overlapCoordinateUnit R ^ n)).hom ≫
        (Scheme.Modules.restrictFunctor q).map g := by
    symm
    dsimp only [columnTransition, Iso.trans_hom, Iso.symm_hom, unitMulIso]
    simp only [Category.assoc]
    rw [hg, hcoord]
    rw [← Category.assoc (unitMul _ _), ← unitMul_mul]
    simp [u, p, ← mul_pow, unitMul_one]
  obtain ⟨V, h, hV, eU, _, hU, _⟩ :=
    exists_vectorBundle_map_of_compatible_chart_maps R M n f g hfg
  exact ⟨V, h, hV, eU, hU⟩

/-- The symmetric actual extension preserves an arbitrary negative-chart
unit map into a quasicoherent sheaf. -/
theorem exists_vectorBundle_lift_minus (R : CommRingCat.{u})
    (M : (twoChartLine R).Modules) [M.IsQuasicoherent]
    (g : (SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf) ⟶
      M.restrict (minusChart R)) :
    ∃ (V : (twoChartLine R).Modules) (h : V ⟶ M), IsFiniteLocallyFree (twoChartLine R) V ∧
      ∃ e : V.restrict (minusChart R) ≅
        SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf,
        (Scheme.Modules.restrictFunctor (minusChart R)).map h = e.hom ≫ g := by
  let j := plusChart R
  let k := minusChart R
  let p := pullback.fst j k
  let q := pullback.snd j k
  let u : (SheafOfModules.unit (pullback j k).ringCatSheaf) ⟶
      (M.restrict j).restrict p :=
    (Scheme.Modules.restrictUnitIso q).inv ≫ (Scheme.Modules.restrictFunctor q).map g ≫
      (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).inv.app M
  have hp : p ''ᵁ ⊤ = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) := by
    rw [p.image_top_eq_opensRange]
    dsimp only [p]
    rw [Scheme.Hom.opensRange_pullbackFst]
    exact (plusChart_preimage_minusRange R).trans
      (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentPlus_opensRange R)
  obtain ⟨n, f, hf⟩ := exists_unit_map_denominator p (M.restrict j) Polynomial.X hp u
  have hcoord : p.appTop.hom ((Scheme.ΓSpecIso (.of (Polynomial R))).inv.hom
      (Polynomial.X ^ n)) = ↑(overlapCoordinateUnit R ^ n) := by
    simp only [map_pow, Units.val_pow_eq_pow_val]
    rfl
  have hfg : (Scheme.Modules.restrictFunctor p).map f ≫
        (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.app M =
      (columnTransition j k (overlapCoordinateUnit R ^ n)).hom ≫
        (Scheme.Modules.restrictFunctor q).map g := by
    apply (cancel_epi (Scheme.Modules.restrictUnitIso p).inv).mp
    rw [← Category.assoc, hf, hcoord]
    dsimp only [columnTransition, Iso.trans_hom, Iso.symm_hom, unitMulIso]
    simp [u, p, q, Category.assoc]
    rfl
  obtain ⟨V, h, hV, _, eV, _, hV'⟩ :=
    exists_vectorBundle_map_of_compatible_chart_maps R M n f g hfg
  exact ⟨V, h, hV, eV, hV'⟩

/-- A quasicoherent epimorphism onto a target finite on the two original
charts admits a finite locally free global source. The source maps into M,
so the construction applies to chosen top cycles rather than only homology. -/
theorem exists_vectorBundle_lift_of_finite_twoChart_epi
    (R : CommRingCat.{u}) {M H : (twoChartLine R).Modules}
    [M.IsQuasicoherent] [H.IsQuasicoherent] (q : M ⟶ H) [Epi q]
    [Module.Finite (Polynomial R)
      (moduleSpecΓFunctor.obj (H.restrict (plusChart R)))]
    [Module.Finite (Polynomial R)
      (moduleSpecΓFunctor.obj (H.restrict (minusChart R)))] :
    ∃ (V : (twoChartLine R).Modules) (f : V ⟶ M),
      IsFiniteLocallyFree (twoChartLine R) V ∧ Epi (f ≫ q) := by
  classical
  let A := Scheme.Modules.restrictFunctor (plusChart R)
  let B := Scheme.Modules.restrictFunctor (minusChart R)
  obtain ⟨I, hI, l, hl⟩ := exists_finite_free_lift_of_affine_epi (.of (Polynomial R)) (A.map q)
  obtain ⟨J, hJ, m, hm⟩ := exists_finite_free_lift_of_affine_epi (.of (Polynomial R)) (B.map q)
  let : Finite I := hI
  let : Finite J := hJ
  choose V v hV eV heV using fun i : I =>
    exists_vectorBundle_lift_plus R M (SheafOfModules.ιFree i ≫ l)
  choose W w hW eW heW using fun j : J =>
    exists_vectorBundle_lift_minus R M (SheafOfModules.ιFree j ≫ m)
  let F : I ⊕ J → (twoChartLine R).Modules := Sum.elim V W
  let d : ∀ z, F z ⟶ M := fun z => by
    cases z with
    | inl i => exact v i
    | inr j => exact w j
  let T := ∐ F
  let f : T ⟶ M := Sigma.desc d
  have hF (z : I ⊕ J) : IsFiniteLocallyFree (twoChartLine R) (F z) := by
    cases z with
    | inl i => exact hV i
    | inr j => exact hW j
  have hT : IsFiniteLocallyFree (twoChartLine R) T :=
    (finiteLocallyFree (twoChartLine R)).prop_of_iso
      ((biproduct.isoProduct F).symm ≪≫ biproduct.isoCoproduct F)
      ((finiteLocallyFree (twoChartLine R)).prop_pi F hF)
  let gA : SheafOfModules.free (R := (Spec (.of (Polynomial R))).ringCatSheaf) I ⟶ A.obj T :=
    Sigma.desc (fun i => (eV i).inv ≫ A.map (Sigma.ι F (.inl i)))
  let gB : SheafOfModules.free (R := (Spec (.of (Polynomial R))).ringCatSheaf) J ⟶ B.obj T :=
    Sigma.desc (fun j => (eW j).inv ≫ B.map (Sigma.ι F (.inr j)))
  have hA : gA ≫ A.map f = l := by
    apply Sigma.hom_ext
    intro i
    simp only [gA, Sigma.ι_comp_desc_assoc]
    rw [Category.assoc, ← A.map_comp]
    dsimp only [f]
    rw [Sigma.ι_comp_desc]
    change (eV i).inv ≫ A.map (v i) = _
    rw [heV i]
    simp [SheafOfModules.ιFree]
  have hB : gB ≫ B.map f = m := by
    apply Sigma.hom_ext
    intro j
    simp only [gB, Sigma.ι_comp_desc_assoc]
    rw [Category.assoc, ← B.map_comp]
    dsimp only [f]
    rw [Sigma.ι_comp_desc]
    change (eW j).inv ≫ B.map (w j) = _
    rw [heW j]
    simp [SheafOfModules.ιFree]
  have hAepi : Epi (A.map (f ≫ q)) := by
    have : Epi (l ≫ A.map q) := hl
    apply epi_of_epi_fac (show gA ≫ A.map (f ≫ q) = l ≫ A.map q from ?_)
    rw [Functor.map_comp, ← Category.assoc, hA]
  have hBepi : Epi (B.map (f ≫ q)) := by
    have : Epi (m ≫ B.map q) := hm
    apply epi_of_epi_fac (show gB ≫ B.map (f ≫ q) = m ≫ B.map q from ?_)
    rw [Functor.map_comp, ← Category.assoc, hB]
  refine ⟨T, f, hT, ?_⟩
  let c : Bool → (Spec (.of (Polynomial R)) ⟶ twoChartLine R) :=
    fun b => if b then plusChart R else minusChart R
  let (b : Bool) : IsOpenImmersion (c b) := by cases b <;> dsimp [c] <;> infer_instance
  apply Preadditive.epi_of_isZero_cokernel
  apply isZero_of_restrict_openCover (fun _ : Bool => Spec (.of (Polynomial R))) c
    (fun x => by
      rcases charts_jointly_surjective R x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, y, hy⟩)
  intro b
  have : Epi ((Scheme.Modules.restrictFunctor (c b)).map (f ≫ q)) := by
    cases b
    · exact hBepi
    · exact hAepi
  exact (isZero_cokernel_of_epi ((Scheme.Modules.restrictFunctor (c b)).map (f ≫ q))).of_iso
    (PreservesCokernel.iso (Scheme.Modules.restrictFunctor (c b)) (f ≫ q))

/-- Actual top cycles of a termwise quasicoherent complex admit a finite
locally free attachment onto top homology over every base ring. The given
local strict models supply finiteness; no global resolution is assumed. -/
theorem exists_vectorBundle_single_epi_top (R : CommRingCat.{u})
    (K : CochainComplex (twoChartLine R).Modules ℤ) (hqc : ∀ i, (K.X i).IsQuasicoherent)
    (a b : ℤ) (hab : a ≤ b) [K.IsLE b] (hK : twoChartStrictLowerModels R K a) :
    ∃ V : (twoChartLine R).Modules, IsFiniteLocallyFree (twoChartLine R) V ∧
      ∃ f : (CochainComplex.singleFunctor _ b).obj V ⟶ K,
        Epi (HomologicalComplex.homologyMap f b) := by
  have : (K.cycles b).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (twoChartLine R).ringCatSheaf).prop_of_isLimit
      (K.cyclesIsKernel b (b + 1) (by simp)) (by
        rintro (_ | _)
        · exact hqc b
        · exact hqc (b + 1))
  have : (K.homology b).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.QuasiCoherent.quasicoherent_homology K hqc b
  have : Module.Finite (Polynomial R)
      (moduleSpecΓFunctor.obj ((K.homology b).restrict (plusChart R))) := by
    have := restriction_isLE (plusChart R) K b
    have := finite_top_homology_sections (.of (Polynomial R))
      ((restrict (plusChart R)).obj K) a b hab hK.1
    exact Module.Finite.equiv
      (moduleSpecΓFunctor.mapIso (restrictHomologyIso (plusChart R) K b)).toLinearEquiv
  have : Module.Finite (Polynomial R)
      (moduleSpecΓFunctor.obj ((K.homology b).restrict (minusChart R))) := by
    have := restriction_isLE (minusChart R) K b
    have := finite_top_homology_sections (.of (Polynomial R))
      ((restrict (minusChart R)).obj K) a b hab hK.2
    exact Module.Finite.equiv
      (moduleSpecΓFunctor.mapIso (restrictHomologyIso (minusChart R) K b)).toLinearEquiv
  obtain ⟨V, v, hV, hv⟩ :=
    exists_vectorBundle_lift_of_finite_twoChart_epi R (K.homologyπ b)
  have : Epi (v ≫ K.homologyπ b) := hv
  exact ⟨V, hV, singleCycleLift K b V v,
    epi_of_epi_fac (singleCycleLift_homology K b V v)⟩

/-- The constructed finite locally free top attachment genuinely lowers local
strict amplitude. The original chain map and original cone are retained.
Actual [a,b-1] chart windows follow from the named window theorem. -/
theorem exists_vectorBundle_top_attachment (R : CommRingCat.{u})
    (K : CochainComplex (twoChartLine R).Modules ℤ) (hqc : ∀ i, (K.X i).IsQuasicoherent)
    (a b : ℤ) (hab : a < b) [K.IsLE b] (hK : twoChartStrictLowerModels R K a) :
    ∃ V : (twoChartLine R).Modules, IsFiniteLocallyFree (twoChartLine R) V ∧
      ∃ f : (CochainComplex.singleFunctor _ b).obj V ⟶ K,
        Epi (HomologicalComplex.homologyMap f b) ∧
        (CochainComplex.mappingCone f).IsLE (b - 1) ∧
        twoChartStrictLowerModels R (CochainComplex.mappingCone f) a := by
  obtain ⟨V, hV, f, hf⟩ := exists_vectorBundle_single_epi_top R K hqc a b (by omega) hK
  have : IsFiniteLocallyFree (twoChartLine R) V := hV
  have : Epi (HomologicalComplex.homologyMap f b) := hf
  exact ⟨V, hV, f, hf,
    twoChartStrictLowerModels_mappingCone_single R K V a b hab hK f⟩

/-- Finite attachment and top-single reassembly strictify a termwise
quasicoherent representative with the specified finite local amplitude.
The induction decreases the actual integer upper bound and retains a. -/
theorem exists_strict_window_of_twoChart_models (R : CommRingCat.{u})
    (K : CochainComplex (twoChartLine R).Modules ℤ) (hqc : ∀ i, (K.X i).IsQuasicoherent)
    (a b : ℤ) (hab : a ≤ b) [K.IsStrictlyGE a] [K.IsLE b]
    (hK : twoChartStrictLowerModels R K a) :
    ∃ P : StrictPerfect (twoChartLine R),
      (∀ i, i < a ∨ b < i → IsZero (P.obj.X i)) ∧
      Nonempty ((DerivedCategory.Q).obj P.obj ≅ (DerivedCategory.Q).obj K) := by
  induction b, hab using Int.leInduction generalizing K with
  | base =>
    obtain ⟨hV, hf⟩ := terminal_single_vectorBundle_model R K a hK
    have : IsFiniteLocallyFree (twoChartLine R) (K.cycles a) := hV
    have : QuasiIso (singleCyclesMap K a) := hf
    refine ⟨⟨_, single_strictPerfect_int (K.cycles a) a⟩, ?_,
      ⟨asIso ((DerivedCategory.Q).map (singleCyclesMap K a))⟩⟩
    intro i hi
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  | succ n hn ih =>
    obtain ⟨V, hV, f, hf, hupper, hmodels⟩ :=
      exists_vectorBundle_top_attachment R K hqc a (n + 1) (by omega) hK
    have : IsFiniteLocallyFree (twoChartLine R) V := hV
    have : (CochainComplex.mappingCone f).IsLE n := by simpa using hupper
    have : (CochainComplex.mappingCone f).IsStrictlyGE a := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      exact (CochainComplex.mappingCone.isZero_X_iff f i).mpr
        ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega),
          K.isZero_of_isStrictlyGE a i hi⟩
    have hconeQC (i : ℤ) : ((CochainComplex.mappingCone f).X i).IsQuasicoherent := by
      let Q := SheafOfModules.isQuasicoherent (twoChartLine R).ringCatSheaf
      have h₁ : Q (((CochainComplex.singleFunctor _ (n + 1)).obj V).X (i + 1)) := by
        have := (single_strictPerfect_int V (n + 1)).2 (i + 1)
        infer_instance
      have h₂ : Q (K.X i) := hqc i
      have hp : Q ((((CochainComplex.singleFunctor _ (n + 1)).obj V).X (i + 1)) ⊞ K.X i) :=
        Q.prop_of_iso (biprod.isoProd _ _).symm (Q.prop_prod _ _ h₁ h₂)
      exact Q.prop_of_iso
        (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl).symm hp
    obtain ⟨P, hP, ⟨eP⟩⟩ := ih (CochainComplex.mappingCone f) hconeQC hmodels
    exact strict_model_of_top_attachment K V a (n + 1) (by omega) f P
      (by simpa using hP) eP.symm

/-- Every bounded-below, termwise quasicoherent, locally perfect complex on
the original two-chart line has an actual global strict derived model.
No noetherianity or global vector-bundle resolution premise is assumed. -/
theorem exists_strict_model_of_boundedBelow_quasicoherent (R : CommRingCat.{u})
    (K : CochainComplex (twoChartLine R).Modules ℤ) (c : ℤ) [K.IsStrictlyGE c]
    (hqc : ∀ i, (K.X i).IsQuasicoherent) (hK : locallyPerfect (twoChartLine R) K) :
    ∃ P : StrictPerfect (twoChartLine R),
      Nonempty ((DerivedCategory.Q).obj P.obj ≅ (DerivedCategory.Q).obj K) := by
  obtain ⟨d, hmodels⟩ := exists_twoChartStrictLowerModels R hK
  obtain ⟨e, b, hb⟩ := locallyPerfect_homology_bounded hK
  have : K.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hb i (Or.inr hi)
  let a := min c (min d b)
  have hac : a ≤ c := min_le_left _ _
  have had : a ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hab : a ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  have : K.IsStrictlyGE a := K.isStrictlyGE_of_ge a c hac
  have ha : twoChartStrictLowerModels R K a := by
    obtain ⟨⟨P, hP, eP⟩, ⟨N, hN, eN⟩⟩ := hmodels
    exact ⟨⟨P, fun i hi => hP i (lt_of_lt_of_le hi had), eP⟩,
      ⟨N, fun i hi => hN i (lt_of_lt_of_le hi had), eN⟩⟩
  obtain ⟨P, _, eP⟩ := exists_strict_window_of_twoChart_models R K hqc a b hab ha
  exact ⟨P, eP⟩

end Quillen.PerfectComplexes.ProjectiveLine
