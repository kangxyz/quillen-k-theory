/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.DerivedRoofs
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Single
public import Aglib.AlgebraicGeometry.Modules.Complex.Homology
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Homology
public import Quillen.Aglib.Algebra.Homology.ModuleCat.FiniteFreeAttachment
public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.KernelClosure
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.Algebra.Homology.CochainComplex.Cycles

/-!
# Affine strict models with retained lower bounds

Actual strict models, cycles, good truncation windows and their cone comparisons retain the stated integer bounds. Top homology is finite only under the displayed upper cohomological bound; no lower-homology finiteness over a noncoherent ring is claimed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry Opposite ModuleCat HomologicalComplex
open AlgebraicGeometry.Scheme.Modules.Complex AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
/-- The standard derived category of module sheaves, used for finite attachments. -/
local instance finiteAttachmentStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- Above the cohomological upper bound, cycles of a bounded vector-bundle
complex are finite locally free. The argument uses local kernel closure,
without treating a vector bundle as a projective object of all sheaves. -/
theorem finiteLocallyFree_cycles_above_bound {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
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
          (_root_.CochainComplex.cycleSequence K (j - 1)).X₂ := hterms (j - 1)
      have hS := _root_.CochainComplex.cycleSequence_shortExact K (j - 1)
        (by simpa using K.exactAt_of_isLE n j (by omega))
      have : IsFiniteLocallyFree X
          (_root_.CochainComplex.cycleSequence K (j - 1)).X₃ := by
        simpa only [_root_.CochainComplex.cycleSequence, sub_add_cancel]
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
def affineStrictLowerModel (R : CommRingCat.{u}) (K : CochainComplex (Spec R).Modules ℤ)
    (a : ℤ) : Prop :=
  ∃ P : StrictPerfect (Spec R), (∀ i, i < a → IsZero (P.obj.X i)) ∧
    Nonempty ((DerivedCategory.Q (C := (Spec R).Modules)).obj K ≅
      (DerivedCategory.Q (C := (Spec R).Modules)).obj P.obj)

/-- An actual attachment from a strict source preserves the local lower term bound;
only the affine source of the derived comparison is used for chain realization. -/
theorem affineStrictLowerModel_mappingCone (R : CommRingCat.{u})
    {K : CochainComplex (Spec R).Modules ℤ} (P : StrictPerfect (Spec R)) (f : P.obj ⟶ K) (a : ℤ)
    (hP : ∀ i, i < a + 1 → IsZero (P.obj.X i))
    (hK : affineStrictLowerModel R K a) :
    affineStrictLowerModel R (CochainComplex.mappingCone f) a := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hK
  obtain ⟨g, hg⟩ := Affine.exists_strict_chain_representative R P L
    ((DerivedCategory.Q (C := (Spec R).Modules)).map f ≫ e.hom)
  refine ⟨⟨CochainComplex.mappingCone g,
    strictPerfect_mappingCone P.property L.property g⟩, ?_, ⟨?_⟩⟩
  · intro i hi
    exact (CochainComplex.mappingCone.isZero_X_iff g i).mpr
      ⟨hP (i + 1) (by omega), hL i hi⟩
  · exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _
      (DerivedCategory.mappingCone_triangle_distinguished f)
        (DerivedCategory.mappingCone_triangle_distinguished g)
      (Iso.refl _) e (by simpa using hg.symm))

/-- A local lower model and the actual upper cohomological bound give an
actual strict model in the stated closed interval, not just homology vanishing. -/
theorem affineStrictLowerModel_exists_window (R : CommRingCat.{u})
    (K : CochainComplex (Spec R).Modules ℤ) (a b : ℤ) (hab : a ≤ b) [K.IsLE b]
    (hK : affineStrictLowerModel R K a) :
    ∃ P : StrictPerfect (Spec R),
      (∀ i, i < a ∨ b < i → IsZero (P.obj.X i)) ∧
      Nonempty ((DerivedCategory.Q (C := (Spec R).Modules)).obj K ≅
        (DerivedCategory.Q (C := (Spec R).Modules)).obj P.obj) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hK
  have : DerivedCategory.IsLE (C := (Spec R).Modules)
    ((DerivedCategory.Q (C := (Spec R).Modules)).obj K) b :=
    inferInstanceAs ((DerivedCategory.Q.obj K).IsLE b)
  have : P.obj.IsLE b := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isLE_of_iso e b
  obtain ⟨hstrict, hwindow, hq⟩ := strictPerfect_truncLE_window P a b hab hP
  have : QuasiIso (P.obj.ιTruncLE b) := hq
  exact ⟨⟨P.obj.truncLE b, hstrict⟩, hwindow,
    ⟨e ≪≫ (asIso ((DerivedCategory.Q (C := (Spec R).Modules)).map (P.obj.ιTruncLE b))).symm⟩⟩

/-- Restricting an actual cone to a specified affine chart preserves the same local
lower term bound, using the original cone/restriction comparison. -/
theorem affineStrictLowerModel_restrict_mappingCone
    {R : CommRingCat.{u}} {X : Scheme.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
    {K : CochainComplex X.Modules ℤ} (P : StrictPerfect X) (f : P.obj ⟶ K) (a : ℤ)
    (hP : ∀ i, i < a + 1 → IsZero (P.obj.X i))
    (hK : affineStrictLowerModel R ((restrict j).obj K) a) :
    affineStrictLowerModel R ((restrict j).obj (CochainComplex.mappingCone f)) a := by
  let P' : StrictPerfect (Spec R) :=
    ⟨(restrict j).obj P.obj, strictPerfect_restrict j P.property⟩
  obtain ⟨C, hC, ⟨eC⟩⟩ := affineStrictLowerModel_mappingCone R P' ((restrict j).map f) a
    (fun i hi => (Scheme.Modules.restrictFunctor j).map_isZero (hP i hi)) hK
  exact ⟨C, hC, ⟨(DerivedCategory.Q (C := (Spec R).Modules)).mapIso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f
      (Scheme.Modules.restrictFunctor j)) ≪≫ eC⟩⟩

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
    (K : CochainComplex (Spec R).Modules ℤ) (a b : ℤ) (hab : a ≤ b) [K.IsLE b]
    (hK : affineStrictLowerModel R K a) :
    Module.Finite R (moduleSpecΓFunctor.obj (K.homology b)) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := affineStrictLowerModel_exists_window R K a b hab hK
  let e : P.obj.cycles b ≅ P.obj.X b := P.obj.iCyclesIso b (b + 1) (by simp)
    ((hP (b + 1) (Or.inr (by omega))).eq_of_tgt _ _)
  have : IsFiniteLocallyFree (Spec R) (P.obj.cycles b) := by
    let := P.property.2 b
    exact finiteLocallyFree_of_iso e.symm
  have : (P.obj.homology b).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.QuasiCoherent.quasicoherent_homology P.obj (fun i => by
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
    (R : CommRingCat.{u}) (K : CochainComplex (Spec R).Modules ℤ) (a : ℤ) [K.IsLE a]
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


end Quillen.PerfectComplexes.ProjectiveLine
end
end
