/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Homology
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.Single
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Closure
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.RankOneGluing
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

/-- A derived map from a complex supported at most n to a single in degree n
has an actual chain representative. The degree condition is essential; no
projectivity of the source terms is asserted. -/
theorem exists_chain_to_top_single
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyLE n] (M : C)
    (α : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C n).obj M)) :
    ∃ f : K ⟶ (CochainComplex.singleFunctor C n).obj M, DerivedCategory.Q.map f = α := by
  obtain ⟨L, _, _, g, s, hs, hα⟩ :=
    DerivedCategory.left_fac_of_isStrictlyLE_of_isStrictlyGE n n α
  have : IsIso (DerivedCategory.Q.map s) := hs
  obtain ⟨N, ⟨e⟩⟩ := L.exists_iso_single n
  obtain ⟨φ, hφ⟩ := (CochainComplex.singleFunctor C n).map_surjective (s ≫ e.hom)
  have : IsIso ((DerivedCategory.singleFunctor C n).map φ) := by
    change IsIso (DerivedCategory.Q.map ((CochainComplex.singleFunctor C n).map φ))
    rw [hφ, Functor.map_comp]
    infer_instance
  have : IsIso φ := isIso_of_reflects_iso φ (DerivedCategory.singleFunctor C n)
  have : IsIso (s ≫ e.hom) := by rw [← hφ]; infer_instance
  have : IsIso s := IsIso.of_isIso_comp_right _ e.hom
  refine ⟨g ≫ inv s, ?_⟩
  rw [Functor.map_comp, Functor.map_inv, hα]

/-- The standard derived category of module sheaves, used for strict-model reassembly. -/
local instance reassemblyStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- A strict model of the cone of a top-degree vector-bundle attachment
reassembles to a strict model of the original object in the exact interval.
Only maps to the top single are realized by chain maps. -/
theorem strict_model_of_top_attachment {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (V : X.Modules) [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X V]
    (a b : ℤ) (hab : a ≤ b)
    (f : (CochainComplex.singleFunctor X.Modules b).obj V ⟶ K)
    (P : StrictPerfect X)
    (hP : ∀ i, i < a ∨ b - 1 < i → IsZero (P.obj.X i))
    (eP : (DerivedCategory.Q (C := X.Modules)).obj (CochainComplex.mappingCone f) ≅
      (DerivedCategory.Q (C := X.Modules)).obj P.obj) :
    ∃ S : StrictPerfect X, (∀ i, i < a ∨ b < i → IsZero (S.obj.X i)) ∧
      Nonempty ((DerivedCategory.Q (C := X.Modules)).obj S.obj ≅
        (DerivedCategory.Q (C := X.Modules)).obj K) := by
  let A := (CochainComplex.singleFunctor X.Modules b).obj V
  let B := (CochainComplex.singleFunctor X.Modules (b - 1)).obj V
  let T := (DerivedCategory.Q (C := X.Modules)).mapTriangle.obj
    (CochainComplex.mappingCone.triangle f)
  let eV : ((DerivedCategory.Q (C := X.Modules)).obj A)⟦(1 : ℤ)⟧ ≅
    (DerivedCategory.Q (C := X.Modules)).obj B :=
    ((DerivedCategory.singleFunctors X.Modules).shiftIso 1 (b - 1) b (by omega)).app V
  have : P.obj.IsStrictlyLE (b - 1) :=
    (CochainComplex.isStrictlyLE_iff _ _).mpr (fun i hi => hP i (Or.inr hi))
  let α : (DerivedCategory.Q (C := X.Modules)).obj P.obj ⟶
    (DerivedCategory.Q (C := X.Modules)).obj B :=
    eP.inv ≫ T.mor₃ ≫ eV.hom
  obtain ⟨g, hg⟩ := exists_chain_to_top_single P.obj (b - 1) V α
  change (DerivedCategory.Q (C := X.Modules)).map g = α at hg
  have hT : T ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished f
  have hcomm : (DerivedCategory.Q (C := X.Modules)).map g ≫ eV.inv = eP.inv
    ≫ T.rotate.rotate.mor₁ := by
    change (DerivedCategory.Q (C := X.Modules)).map g ≫ eV.inv = eP.inv ≫ T.mor₃
    rw [hg]
    simp [α]
  let eC : (DerivedCategory.Q (C := X.Modules)).obj (CochainComplex.mappingCone g) ≅
      ((DerivedCategory.Q (C := X.Modules)).obj K)⟦(1 : ℤ)⟧ :=
    Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ T.rotate.rotate
      (DerivedCategory.mappingCone_triangle_distinguished g)
      (rot_of_distTriang _ (rot_of_distTriang _ hT)) eP.symm eV.symm hcomm)
  let S : StrictPerfect X := ⟨(CochainComplex.mappingCone g)⟦(-1 : ℤ)⟧,
    strictPerfect_shift
      (strictPerfect_mappingCone P.property (single_strictPerfect_int V (b - 1)) g) (-1)⟩
  refine ⟨S, ?_, ⟨?_⟩⟩
  · intro i hi
    change IsZero ((CochainComplex.mappingCone g).X (i + -1))
    apply (CochainComplex.mappingCone.isZero_X_iff g (i + -1)).mpr
    constructor
    · apply hP
      rcases hi with hi | hi
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by rcases hi with hi | hi <;> omega)
  · change (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.mappingCone g)⟦(-1 : ℤ)⟧) ≅ _
    exact ((DerivedCategory.Q (C := X.Modules)).commShiftIso (-1)).app
      (CochainComplex.mappingCone g) ≪≫
      (shiftFunctor (DerivedCategory X.Modules) (-1)).mapIso eC ≪≫
      (shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1) (by omega)).app
        ((DerivedCategory.Q (C := X.Modules)).obj K)


/-- A pair of chart maps into two ambient sheaves, viewed as a chart map
into their actual ambient product. -/
def restrictionGraph {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : U.Modules} {G M : X.Modules} (i : A ⟶ G.restrict j) (f : A ⟶ M.restrict j) :
    A ⟶ (G ⨯ M).restrict j :=
  prod.lift i f ≫ inv (prodComparison (Scheme.Modules.restrictFunctor j) G M)

@[reassoc (attr := simp)]
theorem restrictionGraph_fst {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : U.Modules} {G M : X.Modules} (i : A ⟶ G.restrict j) (f : A ⟶ M.restrict j) :
    restrictionGraph j i f ≫ (Scheme.Modules.restrictFunctor j).map prod.fst = i := by
  simp [restrictionGraph, Category.assoc, inv_prodComparison_map_fst]

@[reassoc (attr := simp)]
theorem restrictionGraph_snd {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : U.Modules} {G M : X.Modules} (i : A ⟶ G.restrict j) (f : A ⟶ M.restrict j) :
    restrictionGraph j i f ≫ (Scheme.Modules.restrictFunctor j).map prod.snd = f := by
  simp [restrictionGraph, Category.assoc, inv_prodComparison_map_snd]

instance restrictionGraph_mono {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : U.Modules} {G M : X.Modules} (i : A ⟶ G.restrict j) (f : A ⟶ M.restrict j)
    [Mono i] : Mono (restrictionGraph j i f) := by
  have : Mono (restrictionGraph j i f ≫ (Scheme.Modules.restrictFunctor j).map prod.fst) := by
    rw [restrictionGraph_fst]
    infer_instance
  exact mono_of_mono (restrictionGraph j i f)
    ((Scheme.Modules.restrictFunctor j).map (prod.fst : G ⨯ M ⟶ G))

/-- Compatible chart graph maps give an actual global source and morphism,
with both original chart maps retained by the supplied trivializations. -/
theorem exists_glued_graph_map {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k]
    {A : U.Modules} {B : V.Modules} {G M : X.Modules}
    (i : A ⟶ G.restrict j) (l : B ⟶ G.restrict k) [Mono i] [Mono l]
    (f : A ⟶ M.restrict j) (g : B ⟶ M.restrict k)
    (e : A.restrict (pullback.fst j k) ≅ B.restrict (pullback.snd j k))
    (hG : (Scheme.Modules.restrictFunctor (pullback.fst j k)).map i ≫
        (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.app G =
      e.hom ≫ (Scheme.Modules.restrictFunctor (pullback.snd j k)).map l)
    (hM : (Scheme.Modules.restrictFunctor (pullback.fst j k)).map f ≫
        (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.app M =
      e.hom ≫ (Scheme.Modules.restrictFunctor (pullback.snd j k)).map g) :
    ∃ (N : X.Modules) (h : N ⟶ M),
      ∃ (eU : N.restrict j ≅ A) (eV : N.restrict k ≅ B),
        (Scheme.Modules.restrictFunctor j).map h = eU.hom ≫ f ∧
        (Scheme.Modules.restrictFunctor k).map h = eV.hom ≫ g := by
  have hc : (Scheme.Modules.restrictFunctor (pullback.fst j k)).map
        (restrictionGraph j i f) ≫ (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j
          k).hom.app (G ⨯ M) =
      e.hom ≫ (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
        (restrictionGraph k l g) := by
    let F := Scheme.Modules.restrictFunctor k ⋙
      Scheme.Modules.restrictFunctor (pullback.snd j k)
    apply (cancel_mono (prodComparison F G M)).mp
    apply prod.hom_ext
    · simp only [Category.assoc, prodComparison_fst]
      change (Scheme.Modules.restrictFunctor (pullback.fst j k)).map
          (restrictionGraph j i f) ≫ (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j
            k).hom.app (G ⨯ M) ≫
          (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
            ((Scheme.Modules.restrictFunctor k).map prod.fst) = _
      have hn := (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.naturality
        (show G ⨯ M ⟶ G from prod.fst)
      dsimp only [Functor.comp_map] at hn
      dsimp only [F, Functor.comp_map]
      rw [← hn, ← Category.assoc, ← Functor.map_comp, restrictionGraph_fst]
      rw [← Functor.map_comp, restrictionGraph_fst]
      exact hG
    · simp only [Category.assoc, prodComparison_snd]
      change (Scheme.Modules.restrictFunctor (pullback.fst j k)).map
          (restrictionGraph j i f) ≫ (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j
            k).hom.app (G ⨯ M) ≫
          (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
            ((Scheme.Modules.restrictFunctor k).map prod.snd) = _
      have hn := (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.naturality
        (show G ⨯ M ⟶ M from prod.snd)
      dsimp only [Functor.comp_map] at hn
      dsimp only [F, Functor.comp_map]
      rw [← hn, ← Category.assoc, ← Functor.map_comp, restrictionGraph_snd]
      rw [← Functor.map_comp, restrictionGraph_snd]
      exact hM
  obtain ⟨N, h, _, eU, eV, hU, hV⟩ := AlgebraicGeometry.Scheme.Modules.exists_glued_subobject j k
    (restrictionGraph j i f) (restrictionGraph k l g) e hc
  refine ⟨N, h ≫ prod.snd, eU, eV, ?_, ?_⟩
  · rw [Functor.map_comp, hU, Category.assoc, restrictionGraph_snd]
  · rw [Functor.map_comp, hV, Category.assoc, restrictionGraph_snd]

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


/-- A section on the whole scheme, with all of its actual restrictions. -/
def moduleTopSection {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk (fun U =>
    (M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom s) (by
      intro U V f
      change (M.presheaf.map f).hom
        ((M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom s) = _
      rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp]
      rfl)

/-- The actual map from the unit module determined by a global section. -/
def unitMapOfTopSection {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    (SheafOfModules.unit X.ringCatSheaf) ⟶ M :=
  M.unitHomEquiv.symm (moduleTopSection M s)

/-- The unit map acts by the original scalar action on restricted sections. -/
theorem unitMapOfTopSection_app {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤))
    (U : X.Opens) (r : Γ(X, U)) :
    Scheme.Modules.Hom.app (unitMapOfTopSection M s) U r =
      r • (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom s := rfl

/-- Maps from the actual unit sheaf are determined by their original global section. -/
theorem unit_hom_ext_top {X : Scheme.{u}} {M : X.Modules}
    {f g : (SheafOfModules.unit X.ringCatSheaf) ⟶ M}
    (h : Scheme.Modules.Hom.app f ⊤ (1 : Γ(X, ⊤)) =
      Scheme.Modules.Hom.app g ⊤ (1 : Γ(X, ⊤))) : f = g := by
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  have hf := PresheafOfModules.sections_property (M.unitHomEquiv f)
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  have hg := PresheafOfModules.sections_property (M.unitHomEquiv g)
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  rw [← hf, ← hg]
  exact congrArg (fun x => (M.presheaf.map (homOfLE le_top).op).hom x) h

/-- Scalar multiplication of a section is literal precomposition with the
original structure-module scalar map. -/
theorem unitMapOfTopSection_smul {X : Scheme.{u}} (M : X.Modules)
    (r : Γ(X, ⊤)) (s : Γ(M, ⊤)) :
    unitMapOfTopSection M (r • s) = unitMul X r ≫ unitMapOfTopSection M s := by
  apply unit_hom_ext_top
  change Scheme.Modules.Hom.app (unitMapOfTopSection M (r • s)) ⊤ (1 : Γ(X, ⊤)) =
    Scheme.Modules.Hom.app (unitMapOfTopSection M s) ⊤
      (Scheme.Modules.Hom.app (unitMul X r) ⊤ (1 : Γ(X, ⊤)))
  simp [unitMapOfTopSection_app, unitMul_app]

/-- The original restriction of a global module section to the image of an open immersion. -/
def restrictedTopSection {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (s : Γ(M, ⊤)) : Γ(M.restrict j, ⊤) :=
  (M.presheaf.map (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op).hom s

/-- The original unit-restriction comparison carries the section map to the
map defined by its actual restricted global section. -/
theorem unitMapOfTopSection_restrict {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (s : Γ(M, ⊤)) :
    (Scheme.Modules.restrictUnitIso j).inv ≫
        (Scheme.Modules.restrictFunctor j).map (unitMapOfTopSection M s) =
      unitMapOfTopSection (M.restrict j) (restrictedTopSection j M s) := by
  apply unit_hom_ext_top
  change Scheme.Modules.Hom.app (unitMapOfTopSection M s) (j ''ᵁ ⊤)
      ((j.appIso ⊤).inv.hom (1 : Γ(X, ⊤))) =
    Scheme.Modules.Hom.app (unitMapOfTopSection (M.restrict j)
      (restrictedTopSection j M s)) ⊤ (1 : Γ(X, ⊤))
  simp [unitMapOfTopSection_app, restrictedTopSection]

/-- Every section on a genuine principal affine open has a numerator after
multiplication by a power of the original coordinate-ring element. -/
theorem affine_section_denominator (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [M.IsQuasicoherent] (r : R) (s : Γ(M, PrimeSpectrum.basicOpen r)) :
    ∃ (n : ℕ) (t : Γ(M, ⊤)),
      M.presheaf.map (PrimeSpectrum.basicOpen r).leTop.op t = r ^ n • s := by
  have h : IsLocalizedModule.Away r
      ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance r
  obtain ⟨n, t, ht⟩ := h.surj _ _ s
  exact ⟨n, t, ht.symm⟩

/-- Recover an arbitrary unit-sheaf map from its actual value at the global unit section. -/
theorem unitMapOfTopSection_of_map {X : Scheme.{u}} {M : X.Modules}
    (f : (SheafOfModules.unit X.ringCatSheaf) ⟶ M) :
    unitMapOfTopSection M (Scheme.Modules.Hom.app f ⊤ (1 : Γ(X, ⊤))) = f := by
  apply unit_hom_ext_top
  simp [unitMapOfTopSection_app]

/-- The actual affine coordinate action agrees with the action after restricting
along an arbitrary open immersion, through the original section comparison. -/
theorem affine_scalar_restrict_section {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) [IsOpenImmersion j] (M : (Spec R).Modules)
    (r : R) (s : Γ(M.restrict j, ⊤)) :
    (M.restrictAppIso j ⊤).hom (j.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) • s) =
      r • (M.restrictAppIso j ⊤).hom s := by
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, Scheme.Modules.smul_Spec_def]
  have he : j.appTop ≫ (j.appIso ⊤).inv =
      (Spec R).presheaf.map (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op := by
    simpa [Scheme.Hom.appTop, Scheme.Hom.appLE] using
      j.appLE_appIso_inv (U := ⊤) (V := ⊤) (by simp)
  exact congrArg (fun c => c • (M.restrictAppIso j ⊤).hom s)
    (congrArg (fun f => CommRingCat.Hom.hom f ((Scheme.ΓSpecIso R).inv.hom r)) he)

/-- An actual unit-sheaf map on a principal affine open extends after a power
of the original coordinate. The equation retains the original restriction
unit, scalar map, and local morphism. -/
theorem exists_unit_map_denominator {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) [IsOpenImmersion j] (M : (Spec R).Modules) [M.IsQuasicoherent]
    (r : R) (himage : j ''ᵁ ⊤ = PrimeSpectrum.basicOpen r)
    (f : (SheafOfModules.unit X.ringCatSheaf) ⟶ M.restrict j) :
    ∃ (n : ℕ) (g : (SheafOfModules.unit (Spec R).ringCatSheaf) ⟶ M),
      (Scheme.Modules.restrictUnitIso j).inv ≫ (Scheme.Modules.restrictFunctor j).map g =
        unitMul X (j.appTop.hom ((Scheme.ΓSpecIso R).inv.hom (r ^ n))) ≫ f := by
  let N := (modulesSpecToSheaf.obj M).obj
  let e : N.obj (op (j ''ᵁ ⊤)) ≅ N.obj (op (PrimeSpectrum.basicOpen r)) :=
    (N.mapIso (eqToIso himage).op).symm
  let x : Γ(M.restrict j, ⊤) := Scheme.Modules.Hom.app f ⊤ (1 : Γ(X, ⊤))
  obtain ⟨n, t, ht⟩ := affine_section_denominator R M r
    (e.hom ((M.restrictAppIso j ⊤).hom x))
  have he : N.map (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op ≫ e.hom =
      N.map (PrimeSpectrum.basicOpen r).leTop.op := by
    dsimp only [e, Iso.symm_hom, Functor.mapIso_inv]
    rw [← N.map_comp]
    congr 1
  have hsec : restrictedTopSection j M t =
      j.appTop.hom ((Scheme.ΓSpecIso R).inv.hom (r ^ n)) • x := by
    apply (ConcreteCategory.bijective_of_isIso (M.restrictAppIso j ⊤).hom).1
    rw [affine_scalar_restrict_section]
    apply e.toLinearEquiv.injective
    change e.hom.hom (M.presheaf.map
        (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op t) =
      e.hom.hom (r ^ n • (M.restrictAppIso j ⊤).hom x)
    rw [_root_.map_smul]
    have he' := congrArg (fun q => (q : N.obj (op ⊤) ⟶
      N.obj (op (PrimeSpectrum.basicOpen r))) t) he
    change e.hom.hom (M.presheaf.map
      (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op t) =
        M.presheaf.map (PrimeSpectrum.basicOpen r).leTop.op t at he'
    rw [he']
    exact ht
  refine ⟨n, unitMapOfTopSection M t, ?_⟩
  rw [unitMapOfTopSection_restrict, hsec, unitMapOfTopSection_smul]
  change _ ≫ unitMapOfTopSection (M.restrict j)
      (Scheme.Modules.Hom.app f ⊤ (1 : Γ(X, ⊤))) = _
  rw [unitMapOfTopSection_of_map]

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

/-- A sheaf epimorphism onto a finite quasicoherent affine target admits
finitely many actual unit-sheaf lifts jointly generating that target. -/
theorem exists_finite_free_lift_of_affine_epi (R : CommRingCat.{u})
    {M H : (Spec R).Modules} [M.IsQuasicoherent] [H.IsQuasicoherent]
    (q : M ⟶ H) [Epi q] [Module.Finite R (moduleSpecΓFunctor.obj H)] :
    ∃ I : Type u, Finite I ∧
      ∃ l : SheafOfModules.free (R := (Spec R).ringCatSheaf) I ⟶ M, Epi (l ≫ q) := by
  obtain ⟨G, hG⟩ :=
    AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineFiniteSheaf_exists_generatingSections R
    (M := H) ⟨inferInstance, inferInstance⟩
  have : G.IsFiniteType := hG
  have : Epi (moduleSpecΓFunctor.map q) := epi_globalSections_of_quasicoherent R q
  have hsurj := (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map q)).mp inferInstance
  have hlift (i : G.I) : ∃ t : Γ(M, ⊤),
      Scheme.Modules.Hom.app q ⊤ t = Scheme.Modules.Hom.app
        (SheafOfModules.ιFree i ≫ G.π) ⊤ (1 : Γ(Spec R, ⊤)) := by
    exact hsurj (Scheme.Modules.Hom.app
      (SheafOfModules.ιFree i ≫ G.π) ⊤ (1 : Γ(Spec R, ⊤)))
  choose t ht using hlift
  let u (i : G.I) := unitMapOfTopSection M (t i)
  have hu (i : G.I) : u i ≫ q = SheafOfModules.ιFree i ≫ G.π := by
    apply unit_hom_ext_top
    change Scheme.Modules.Hom.app q ⊤
      (Scheme.Modules.Hom.app (unitMapOfTopSection M (t i)) ⊤ (1 : Γ(Spec R, ⊤))) = _
    have hx : Scheme.Modules.Hom.app (unitMapOfTopSection M (t i)) ⊤
        (1 : Γ(Spec R, ⊤)) = t i := by simp [unitMapOfTopSection_app]
    rw [hx]
    exact ht i
  let l : SheafOfModules.free (R := (Spec R).ringCatSheaf) G.I ⟶ M := Sigma.desc u
  have he : l ≫ q = G.π := by
    apply Sigma.hom_ext
    intro i
    simpa [l, SheafOfModules.ιFree] using hu i
  exact ⟨G.I, inferInstance, l, by rw [he]; exact G.epi⟩

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

/-- An actual morphism into the cycle sheaf gives the corresponding original
single-complex chain map, without a projectivity hypothesis. -/
def singleCycleLift {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (b : ℤ)
    (V : X.Modules) (v : V ⟶ K.cycles b) :
    (CochainComplex.singleFunctor X.Modules b).obj V ⟶ K :=
  HomologicalComplex.mkHomFromSingle (v ≫ K.iCycles b) (by intro j hj; simp)

/-- The original homology map of the cycle lift is its specified map to homology. -/
theorem singleCycleLift_homology {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (b : ℤ)
    (V : X.Modules) (v : V ⟶ K.cycles b) :
    (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) b V).inv ≫
      HomologicalComplex.homologyMap (singleCycleLift K b V v) b = v ≫ K.homologyπ b := by
  have hc : (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) b V).inv ≫
      HomologicalComplex.cyclesMap (singleCycleLift K b V v) b = v := by
    rw [← cancel_mono (K.iCycles b), Category.assoc, HomologicalComplex.cyclesMap_i]
    dsimp only [singleCycleLift]
    rw [HomologicalComplex.mkHomFromSingle_f, ← Category.assoc,
      HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles]
    simp
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ, Category.assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc, hc]

private theorem restriction_isLE {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (K : CochainComplex X.Modules ℤ) (b : ℤ) [K.IsLE b] :
    ((restrict j).obj K).IsLE b := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  exact (K.exactAt_of_isLE b i hi).map (Scheme.Modules.restrictFunctor j)

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
