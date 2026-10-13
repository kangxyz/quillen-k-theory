/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.Single
public import Quillen.AlgebraicGeometry.PerfectComplexes.Homology
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Charts
public import Quillen.Algebra.ModuleComplex.FiniteFreeAttachment
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.KernelClosure
public import Quillen.Waldhausen.GilletWaldhausen.AcyclicCycles

/-! # Finite attachments with an explicit local lower bound

The actual cone of an attachment strictly above a local lower term bound
retains that bound on each affine chart. Highest-homology surjectivity lowers
the upper cohomological bound. The existence of a global finite locally free
attachment is a separate geometric step.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open HomologicalComplex
open Quillen.Scheme.ProjectiveLine Quillen.SchemeSheaf
namespace Quillen.PerfectComplexes.ProjectiveLine

/-- The standard derived category of module sheaves, used for finite attachments. -/
local instance finiteAttachmentStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- Above the cohomological upper bound, cycles of a bounded vector-bundle
complex are finite locally free. The argument uses local kernel closure,
without treating a vector bundle as a projective object of all sheaves. -/
theorem finiteLocallyFree_cycles_above_bound {X : Scheme.{u}} (K : Complex X)
    (n b : ℤ) [K.IsLE n] (hbound : ∀ i, b < i → IsZero (K.X i))
    (hterms : ∀ i, IsFiniteLocallyFree X (K.X i)) (i : ℤ) (hi : n ≤ i) :
    IsFiniteLocallyFree X (K.cycles i) := by
  have top (j : ℤ) (hj : b ≤ j) : IsFiniteLocallyFree X (K.cycles j) := by
    let := hterms j
    exact finiteLocallyFree_of_iso (K.iCyclesIso j (j + 1) (by simp)
      ((hbound (j + 1) (by omega)).eq_of_tgt _ _)).symm
  by_cases hib : i ≤ b
  · induction i, hib using Int.leInductionDown with
    | base => exact top b le_rfl
    | pred j hj ih =>
      have := ih (by omega)
      have : IsFiniteLocallyFree X
          (Quillen.Waldhausen.GilletWaldhausen.cycleSequence K (j - 1)).X₂ := hterms (j - 1)
      have hS := Quillen.Waldhausen.GilletWaldhausen.cycleSequence_shortExact K (j - 1)
        (by simpa using K.exactAt_of_isLE n j (by omega))
      have : IsFiniteLocallyFree X
          (Quillen.Waldhausen.GilletWaldhausen.cycleSequence K (j - 1)).X₃ := by
        simpa only [Quillen.Waldhausen.GilletWaldhausen.cycleSequence, sub_add_cancel]
          using (ih (by omega))
      exact finiteLocallyFree_kernel_of_shortExact hS
  · exact top i (by omega)

/-- A strict model with no cohomology above b admits its actual good truncation
with the exact term window [a,b]. The boundary cycle remains a vector bundle. -/
theorem strictPerfect_truncLE_window {X : Scheme.{u}} (P : StrictPerfect X)
    (a b : ℤ) (hab : a ≤ b) (hbelow : ∀ i, i < a → IsZero (P.obj.X i))
    [P.obj.IsLE b] :
    strictPerfect X (P.obj.truncLE b) ∧
      (∀ i, i < a ∨ b < i → IsZero ((P.obj.truncLE b).X i)) ∧
      QuasiIso (P.obj.ιTruncLE b) := by
  obtain ⟨c, d, hbd⟩ := P.property.1
  have hbnd (i : ℤ) (hi : i < a ∨ b < i) : IsZero ((P.obj.truncLE b).X i) := by
    rcases hi with hi | hi
    · exact (hbelow i hi).of_iso (P.obj.truncLEXIso b i (by omega))
    · exact (P.obj.truncLE b).isZero_of_isStrictlyLE b i hi
  have hterms (i : ℤ) : IsFiniteLocallyFree X ((P.obj.truncLE b).X i) := by
    rcases lt_trichotomy i b with hi | heq | hi
    · let := P.property.2 i
      exact finiteLocallyFree_of_iso (P.obj.truncLEXIso b i hi).symm
    · subst i
      have := finiteLocallyFree_cycles_above_bound P.obj b d
        (fun i hi => hbd i (Or.inr hi)) P.property.2 b le_rfl
      exact finiteLocallyFree_of_iso (P.obj.truncLEXIsoCycles b).symm
    · exact finiteLocallyFree_of_isZero (hbnd i (Or.inr hi))
  exact ⟨⟨⟨a, b, hbnd⟩, hterms⟩, hbnd, inferInstance⟩

/-- A genuine affine strict model with its lower term bound retained explicitly. -/
def affineStrictLowerModel (R : CommRingCat.{u}) (K : Complex (Spec R)) (a : ℤ) : Prop :=
  ∃ P : StrictPerfect (Spec R), (∀ i, i < a → IsZero (P.obj.X i)) ∧
    Nonempty ((toDerived (Spec R)).obj K ≅ (toDerived (Spec R)).obj P.obj)

/-- An actual attachment from a strict source preserves the local lower term bound;
only the affine source of the derived comparison is used for chain realization. -/
theorem affineStrictLowerModel_mappingCone (R : CommRingCat.{u})
    {K : Complex (Spec R)} (P : StrictPerfect (Spec R)) (f : P.obj ⟶ K) (a : ℤ)
    (hP : ∀ i, i < a + 1 → IsZero (P.obj.X i))
    (hK : affineStrictLowerModel R K a) :
    affineStrictLowerModel R (CochainComplex.mappingCone f) a := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hK
  obtain ⟨g, hg⟩ := Affine.exists_strict_chain_representative R P L
    ((toDerived (Spec R)).map f ≫ e.hom)
  refine ⟨⟨CochainComplex.mappingCone g,
    strictPerfect_mappingCone P.property L.property g⟩, ?_, ⟨?_⟩⟩
  · intro i hi
    exact (CochainComplex.mappingCone.isZero_X_iff g i).mpr
      ⟨hP (i + 1) (by omega), hL i hi⟩
  · exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _
      (mappingConeTriangle_distinguished f) (mappingConeTriangle_distinguished g)
      (Iso.refl _) e (by simpa using hg.symm))

/-- A local lower model and the actual upper cohomological bound give an
actual strict model in the stated closed interval, not just homology vanishing. -/
theorem affineStrictLowerModel_exists_window (R : CommRingCat.{u})
    (K : Complex (Spec R)) (a b : ℤ) (hab : a ≤ b) [K.IsLE b]
    (hK : affineStrictLowerModel R K a) :
    ∃ P : StrictPerfect (Spec R),
      (∀ i, i < a ∨ b < i → IsZero (P.obj.X i)) ∧
      Nonempty ((toDerived (Spec R)).obj K ≅ (toDerived (Spec R)).obj P.obj) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hK
  have : DerivedCategory.IsLE (C := (Spec R).Modules) ((toDerived (Spec R)).obj K) b :=
    inferInstanceAs ((DerivedCategory.Q.obj K).IsLE b)
  have : P.obj.IsLE b := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isLE_of_iso e b
  obtain ⟨hstrict, hwindow, hq⟩ := strictPerfect_truncLE_window P a b hab hP
  have : QuasiIso (P.obj.ιTruncLE b) := hq
  exact ⟨⟨P.obj.truncLE b, hstrict⟩, hwindow,
    ⟨e ≪≫ (asIso ((toDerived (Spec R)).map (P.obj.ιTruncLE b))).symm⟩⟩

/-- Restricting an actual cone to a specified affine chart preserves the same local
lower term bound, using the original cone/restriction comparison. -/
theorem affineStrictLowerModel_restrict_mappingCone
    {R : CommRingCat.{u}} {X : Scheme.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
    {K : Complex X} (P : StrictPerfect X) (f : P.obj ⟶ K) (a : ℤ)
    (hP : ∀ i, i < a + 1 → IsZero (P.obj.X i))
    (hK : affineStrictLowerModel R ((restrict j).obj K) a) :
    affineStrictLowerModel R ((restrict j).obj (CochainComplex.mappingCone f)) a := by
  let P' : StrictPerfect (Spec R) :=
    ⟨(restrict j).obj P.obj, strictPerfect_restrict j P.property⟩
  obtain ⟨C, hC, ⟨eC⟩⟩ := affineStrictLowerModel_mappingCone R P' ((restrict j).map f) a
    (fun i hi => (Scheme.Modules.restrictFunctor j).map_isZero (hP i hi)) hK
  exact ⟨C, hC, ⟨(toDerived (Spec R)).mapIso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f
      (Scheme.Modules.restrictFunctor j)) ≪≫ eC⟩⟩

/-- The two original polynomial charts have genuine strict derived models with one
common lower term bound. No global strict model is included in this predicate. -/
def twoChartStrictLowerModels (R : CommRingCat.{u}) (K : Complex (twoChartLine R))
    (a : ℤ) : Prop :=
  affineStrictLowerModel (.of (Polynomial R))
    ((restrict (plusChart R)).obj K) a ∧
  affineStrictLowerModel (.of (Polynomial R))
    ((restrict (minusChart R)).obj K) a

/-- Every original locally perfect object on the two-chart line has one common
lower term bound for genuine models on both whole polynomial charts. -/
theorem exists_twoChartStrictLowerModels (R : CommRingCat.{u})
    {K : Complex (twoChartLine R)} (hK : locallyPerfect (twoChartLine R) K) :
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

private theorem restrict_isLE {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (K : Complex X) (b : ℤ) [K.IsLE b] :
    ((restrict j).obj K).IsLE b := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  exact (K.exactAt_of_isLE b i hi).map (Scheme.Modules.restrictFunctor j)

/-- On an affine scheme, an epimorphism between actual quasicoherent sheaves
is surjective on original global module sections. -/
theorem epi_globalSections_of_quasicoherent (R : CommRingCat.{u})
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] : Epi (moduleSpecΓFunctor.map f) := by
  let Q := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let g : (⟨M, inferInstance⟩ : Q.FullSubcategory) ⟶ ⟨N, inferInstance⟩ :=
    ObjectProperty.homMk f
  have : Epi g := Functor.epi_of_epi_map Q.ι (inferInstanceAs (Epi f))
  exact inferInstanceAs (Epi ((tildeEquiv (R := R)).inverse.map g))

/-- Genuine affine lower models and the actual upper bound make top homology
finite over the base ring. This does not claim finiteness of lower homology
over a noncoherent ring. -/
theorem finite_top_homology_sections (R : CommRingCat.{u})
    (K : Complex (Spec R)) (a b : ℤ) (hab : a ≤ b) [K.IsLE b]
    (hK : affineStrictLowerModel R K a) :
    Module.Finite R (moduleSpecΓFunctor.obj (K.homology b)) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := affineStrictLowerModel_exists_window R K a b hab hK
  let e : P.obj.cycles b ≅ P.obj.X b := P.obj.iCyclesIso b (b + 1) (by simp)
    ((hP (b + 1) (Or.inr (by omega))).eq_of_tgt _ _)
  have : IsFiniteLocallyFree (Spec R) (P.obj.cycles b) := by
    let := P.property.2 b
    exact finiteLocallyFree_of_iso e.symm
  have : (P.obj.homology b).IsQuasicoherent :=
    CoherentScheme.quasicoherent_homology P.obj (fun i => by
      let := P.property.2 i
      infer_instance) b
  have : Epi (moduleSpecΓFunctor.map (P.obj.homologyπ b)) :=
    epi_globalSections_of_quasicoherent R (P.obj.homologyπ b)
  have : Module.Finite R (moduleSpecΓFunctor.obj (P.obj.cycles b)) :=
    finite_globalSections_of_finiteLocallyFree R (P.obj.cycles b)
  have : Module.Finite R (moduleSpecΓFunctor.obj (P.obj.homology b)) :=
    Module.Finite.of_surjective (moduleSpecΓFunctor.map (P.obj.homologyπ b)).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  exact Module.Finite.equiv
    (moduleSpecΓFunctor.mapIso (homologyIsoOfDerivedIso eP b)).toLinearEquiv.symm

/-- At the common lower edge, an affine strict model forces the original
homology sheaf to be a vector bundle. Cohomological concentration alone
would not give this conclusion. -/
theorem finiteLocallyFree_homology_of_affineStrictLowerModel
    (R : CommRingCat.{u}) (K : Complex (Spec R)) (a : ℤ) [K.IsLE a]
    (hK : affineStrictLowerModel R K a) :
    IsFiniteLocallyFree (Spec R) (K.homology a) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := affineStrictLowerModel_exists_window R K a a le_rfl hK
  let e : P.obj.homology a ≅ P.obj.X a :=
    (P.obj.isoHomologyπ (a - 1) a (by simp)
      ((hP (a - 1) (Or.inl (by omega))).eq_of_src _ _)).symm ≪≫
    P.obj.iCyclesIso a (a + 1) (by simp)
      ((hP (a + 1) (Or.inr (by omega))).eq_of_tgt _ _)
  let := P.property.2 a
  exact finiteLocallyFree_of_iso (homologyIsoOfDerivedIso eP a ≪≫ e).symm

/-- The genuine local lower models make the terminal homology a global
finite locally free sheaf on the original projective line. -/
theorem finiteLocallyFree_homology_of_twoChartStrictLowerModels
    (R : CommRingCat.{u}) (K : Complex (twoChartLine R)) (a : ℤ) [K.IsLE a]
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
    (R : CommRingCat.{u}) (K : Complex (twoChartLine R))
    (V : (twoChartLine R).Modules)
    [SchemeSheaf.IsFiniteLocallyFree (twoChartLine R) V]
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
    (R : CommRingCat.{u}) (K : Complex (twoChartLine R))
    (V : (twoChartLine R).Modules) [IsFiniteLocallyFree (twoChartLine R) V]
    (a b : ℤ) (hab : a < b) [K.IsLE b] (hK : twoChartStrictLowerModels R K a)
    (f : (CochainComplex.singleFunctor _ b).obj V ⟶ K) [Epi (homologyMap f b)]
    (j : Spec (.of (Polynomial R)) ⟶ twoChartLine R) [IsOpenImmersion j]
    (hj : j = plusChart R ∨ j = minusChart R) :
      ∃ P : StrictPerfect (Spec (.of (Polynomial R))),
        (∀ i, i < a ∨ b - 1 < i → IsZero (P.obj.X i)) ∧
        Nonempty ((toDerived _).obj ((restrict j).obj (CochainComplex.mappingCone f)) ≅
          (toDerived _).obj P.obj) := by
  obtain ⟨hupper, hmodels⟩ := twoChartStrictLowerModels_mappingCone_single R K V a b hab hK f
  have : (CochainComplex.mappingCone f).IsLE (b - 1) := hupper
  rcases hj with rfl | rfl
  · have := restrict_isLE (plusChart R) (CochainComplex.mappingCone f) (b - 1)
    exact affineStrictLowerModel_exists_window _ _ a (b - 1) (by omega) hmodels.1
  · have := restrict_isLE (minusChart R) (CochainComplex.mappingCone f) (b - 1)
    exact affineStrictLowerModel_exists_window _ _ a (b - 1) (by omega) hmodels.2

/-- A map from the original cycle sheaf, placed in its original degree,
to the original complex. Its only nonzero component is the cycle inclusion. -/
def singleCyclesMap {X : Scheme.{u}} (K : Complex X) (a : ℤ) :
    (CochainComplex.singleFunctor X.Modules a).obj (K.cycles a) ⟶ K :=
  mkHomFromSingle (K.iCycles a) (by intro j hj; simp)

/-- The single-cycle map induces exactly the original cycle-to-homology map. -/
theorem singleCyclesMap_homology {X : Scheme.{u}} (K : Complex X) (a : ℤ) :
    (singleObjHomologySelfIso (.up ℤ) a (K.cycles a)).inv ≫
      homologyMap (singleCyclesMap K a) a = K.homologyπ a := by
  have hc : (singleObjCyclesSelfIso (.up ℤ) a (K.cycles a)).inv ≫
      cyclesMap (singleCyclesMap K a) a = 𝟙 _ := by
    rw [← cancel_mono (K.iCycles a), Category.assoc, cyclesMap_i]
    dsimp only [singleCyclesMap]
    rw [mkHomFromSingle_f, ← Category.assoc, singleObjCyclesSelfIso_inv_iCycles]
    simp
  rw [← singleObjCyclesSelfIso_inv_homologyπ, Category.assoc, homologyπ_naturality,
    ← Category.assoc, hc, Category.id_comp]

/-- When the original complex starts at its sole cohomological degree, the
actual cycle inclusion is a quasi-isomorphism from a single complex. -/
theorem singleCyclesMap_quasiIso {X : Scheme.{u}} (K : Complex X) (a : ℤ)
    [K.IsStrictlyGE a] [K.IsLE a] : QuasiIso (singleCyclesMap K a) := by
  have : IsIso (K.homologyπ a) := by
    change IsIso ((K.isoHomologyπ (a - 1) a (by simp)
      ((K.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _)).hom)
    infer_instance
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = a
  · subst i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have h := singleCyclesMap_homology K a
    have : IsIso ((singleObjHomologySelfIso (.up ℤ) a (K.cycles a)).inv ≫
        homologyMap (singleCyclesMap K a) a) := by rw [h]; infer_instance
    exact (isIso_comp_left_iff
      (singleObjHomologySelfIso (.up ℤ) a (K.cycles a)).inv _).mp inferInstance
  · apply (quasiIsoAt_iff_exactAt _ i
      (exactAt_single_obj (.up ℤ) a (K.cycles a) i hi)).mpr
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact K.exactAt_of_isGE a i hi
    · exact K.exactAt_of_isLE a i hi

/-- The terminal stage has an actual finite locally free single-complex
quasi-isomorphism into the original representative. No global projectivity
of that vector bundle is assumed. -/
theorem terminal_single_vectorBundle_model
    (R : CommRingCat.{u}) (K : Complex (twoChartLine R)) (a : ℤ)
    [K.IsStrictlyGE a] [K.IsLE a] (hK : twoChartStrictLowerModels R K a) :
    IsFiniteLocallyFree (twoChartLine R) (K.cycles a) ∧
      QuasiIso (singleCyclesMap K a) := by
  have := finiteLocallyFree_homology_of_twoChartStrictLowerModels R K a hK
  refine ⟨?_, singleCyclesMap_quasiIso K a⟩
  exact finiteLocallyFree_of_iso (K.isoHomologyπ (a - 1) a (by simp)
    ((K.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _)).symm

end Quillen.PerfectComplexes.ProjectiveLine
