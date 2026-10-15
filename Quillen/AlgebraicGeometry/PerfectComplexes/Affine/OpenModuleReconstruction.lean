/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenPushforwardCounit
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenSectionsBounds

/-!
# Bounded module reconstruction on a quasi-compact affine open

For any compact open `W` of `Spec R`, every original bounded-QC complex on W
has a bounded R-module representative whose associated sheaf, after actual
restriction to W, is isomorphic to the original object in D(all module sheaves).
In particular this applies to every locally-perfect complex on W.

The construction retains an actual injective-resolution arrow `E → I`. The
module source is literally an upper good truncation of original `Γ(j_*I)`.
Its lower term bound is the exact requested lower cohomology bound of E;
its finite upper bound is proved from the finite-principal Mayer--Vietoris
bound, transported through the original top-to-W section isomorphism.

The second roof arrow is an actual quasi-isomorphism `restrict(~P) → I`,
composed from the original truncation inclusion, affine counit, and open
restriction counit. Both equations for the resulting original derived
isomorphism are proved. No ambient QC or upper bound is assumed for the
constructed direct image. The module terms are bounded but are not asserted
finite or projective; perfect complements and extension are later steps.

Arbitrary rings, empty opens and independent derived-category universes are
allowed. Compactness of W is explicit.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
namespace Quillen.PerfectComplexes.Affine

/-- The literal finite upper truncation of actual sections of an open direct image. -/
abbrev openPushforwardSectionsTruncation (R : CommRingCat.{u})
    (W : (Spec R).Opens) (I : Complex W.toScheme) (c : ℤ) : ModuleComplex R :=
  ((sectionsComplex R).obj ((pushforwardComplex W.ι).obj I)).truncLE c

/-- The actual comparison from the restricted associated truncated-section complex:
original truncation inclusion, original affine counit, and original open counit. -/
def openPushforwardSectionsTruncationComparison (R : CommRingCat.{u})
    (W : (Spec R).Opens) (I : Complex W.toScheme) (c : ℤ) :
    (restrict W.ι).obj ((associatedComplex R).obj (openPushforwardSectionsTruncation R W I c)) ⟶ I
      :=
  (restrict W.ι).map
    ((associatedComplex R).map (((sectionsComplex R).obj ((pushforwardComplex W.ι).obj I)).ιTruncLE
      c) ≫
      associatedSectionsCounit R ((pushforwardComplex W.ι).obj I)) ≫
        ((pushforwardComplexRestrictIso W.ι).app I).hom

/-- Actual sections of the original direct image have an upper bound, proved
from the geometric bound on W and the literal top-to-W restriction isomorphism. -/
lemma exists_isLE_sections_openPushforward {R : CommRingCat.{u}}
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (I : Complex W.toScheme) (a b : ℤ) (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n)) (hqc : ∀ n, (I.homology n).IsQuasicoherent) [I.IsLE b] :
    ∃ c : ℤ, ((sectionsComplex R).obj ((pushforwardComplex W.ι).obj I)).IsLE c := by
  let J := (pushforwardComplex W.ι).obj I
  let e := (pushforwardComplexRestrictIso W.ι).app I
  have hJb (n : ℤ) (hn : n < a) : IsZero (J.X n) :=
    (Scheme.Modules.pushforward W.ι).map_isZero (hbound n hn)
  have hJi (n : ℤ) : Injective (J.X n) := by
    let := hinj n
    exact injective_pushforward W.ι (I.X n)
  have hJqc (n : ℤ) : (((restrict W.ι).obj J).homology n).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      (((homologyFunctor W.toScheme.Modules (.up ℤ) n).mapIso e).symm) (hqc n)
  have hJle : ((restrict W.ι).obj J).IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro n hn
    exact (I.exactAt_of_isLE b n hn).of_iso e.symm
  obtain ⟨c, hc⟩ := exists_isLE_sections_compactOpen_of_injective J a b hJb hJi W hW hJqc
  have ht : W.ι ⁻¹ᵁ W = ⊤ := by
    simpa only [Scheme.Opens.opensRange_ι] using Scheme.Hom.preimage_opensRange W.ι
  let := isIso_affineSectionsComplexRestriction_pushforward W.ι I
    (le_top : W ≤ ⊤) (by simp [ht])
  refine ⟨c, ?_⟩
  exact CochainComplex.isLE_of_iso
    (asIso (affineSectionsComplexRestriction R (le_top : W ≤ ⊤) J)).symm c

/-- The displayed literal comparison is weak whenever the actual module
section complex has been bounded above. Its source keeps the exact lower term bound. -/
lemma openPushforwardSectionsTruncation_bounds_quasiIso {R : CommRingCat.{u}}
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (I : Complex W.toScheme) (a c : ℤ) (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n)) (hqc : ∀ n, (I.homology n).IsQuasicoherent)
    [((sectionsComplex R).obj ((pushforwardComplex W.ι).obj I)).IsLE c] :
    (openPushforwardSectionsTruncation R W I c).IsStrictlyGE a ∧
      (openPushforwardSectionsTruncation R W I c).IsStrictlyLE c ∧
      QuasiIso (openPushforwardSectionsTruncationComparison R W I c) := by
  let J := (pushforwardComplex W.ι).obj I
  let K := (sectionsComplex R).obj J
  have hKa : K.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact moduleSpecΓFunctor.map_isZero
      ((Scheme.Modules.pushforward W.ι).map_isZero (hbound n hn))
  let := quasiIso_openPushforward_associatedSectionsCounit W hW I a hbound hinj hqc
  refine ⟨?_, ?_, ?_⟩
  · change (K.truncLE c).IsStrictlyGE a
    infer_instance
  · change (K.truncLE c).IsStrictlyLE c
    infer_instance
  · dsimp only [openPushforwardSectionsTruncationComparison]
    infer_instance

/-- A bounded-QC original complex on a compact affine open has an actual
injective-resolution roof whose other leg is the displayed bounded module
section truncation. Both arrows are genuine chain quasi-isomorphisms. -/
lemma exists_bounded_module_open_roof (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (a b : ℤ) [E.IsGE a] [E.IsLE b]
    (hqc : ∀ n, (E.homology n).IsQuasicoherent) :
    ∃ (I : Complex W.toScheme) (q : E ⟶ I) (c : ℤ),
      I.IsStrictlyGE a ∧ (∀ n, Injective (I.X n)) ∧ QuasiIso q ∧
      (openPushforwardSectionsTruncation R W I c).IsStrictlyGE a ∧
      (openPushforwardSectionsTruncation R W I c).IsStrictlyLE c ∧
      QuasiIso (openPushforwardSectionsTruncationComparison R W I c) := by
  let : HasDerivedCategory.{u + 1} W.toScheme.Modules := HasDerivedCategory.standard _
  have : QuasiIso (E.πTruncGE a) := (E.quasiIso_πTruncGE_iff a).mpr inferInstance
  obtain ⟨I, s, hs, hI, hIa⟩ :=
    _root_.CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective (E.truncGE a) a
  let := hs
  let := hIa
  let q : E ⟶ I := E.πTruncGE a ≫ s
  have hq : QuasiIso q := inferInstance
  have hqcI (n : ℤ) : (I.homology n).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      (isoOfQuasiIsoAt q n) (hqc n)
  have hIb : I.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro n hn
    exact (exactAt_iff_of_quasiIsoAt q n).mp (E.exactAt_of_isLE b n hn)
  obtain ⟨c, hc⟩ := exists_isLE_sections_openPushforward W hW I a b
    (fun n hn => I.isZero_of_isStrictlyGE a n hn) hI hqcI
  obtain ⟨hPa, hPc, hφ⟩ := openPushforwardSectionsTruncation_bounds_quasiIso W hW I a c
    (fun n hn => I.isZero_of_isStrictlyGE a n hn) hI hqcI
  exact ⟨I, q, c, hIa, hI, hq, hPa, hPc, hφ⟩

/-- The original derived comparison determined by the displayed genuine
injective-resolution roof. -/
def openModuleReconstructionIso (R : CommRingCat.{u}) (W : (Spec R).Opens)
    {E I : Complex W.toScheme} (q : E ⟶ I) (c : ℤ) [QuasiIso q]
    [QuasiIso (openPushforwardSectionsTruncationComparison R W I c)] :
    (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj
      (openPushforwardSectionsTruncation R W I c))) ≅ (toDerived W.toScheme).obj E :=
  asIso ((toDerived W.toScheme).map (openPushforwardSectionsTruncationComparison R W I c)) ≪≫
    (asIso ((toDerived W.toScheme).map q)).symm

@[reassoc]
lemma openModuleReconstructionIso_hom_comp (R : CommRingCat.{u}) (W : (Spec R).Opens)
    {E I : Complex W.toScheme} (q : E ⟶ I) (c : ℤ) [QuasiIso q]
    [QuasiIso (openPushforwardSectionsTruncationComparison R W I c)] :
    (openModuleReconstructionIso R W q c).hom ≫ (toDerived W.toScheme).map q =
      (toDerived W.toScheme).map (openPushforwardSectionsTruncationComparison R W I c) := by
  simp [openModuleReconstructionIso]

@[reassoc]
lemma openModuleReconstructionIso_inv_comp (R : CommRingCat.{u}) (W : (Spec R).Opens)
    {E I : Complex W.toScheme} (q : E ⟶ I) (c : ℤ) [QuasiIso q]
    [QuasiIso (openPushforwardSectionsTruncationComparison R W I c)] :
    (openModuleReconstructionIso R W q c).inv ≫
        (toDerived W.toScheme).map (openPushforwardSectionsTruncationComparison R W I c) =
      (toDerived W.toScheme).map q := by
  simp [openModuleReconstructionIso]

/-- Genuine bounded module reconstruction on a quasi-compact open of an affine
scheme, in the original ambient derived category of all module sheaves. -/
lemma exists_bounded_module_open_representative (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (a b : ℤ) [E.IsGE a] [E.IsLE b]
    (hqc : ∀ n, (E.homology n).IsQuasicoherent) :
    ∃ (P : ModuleComplex R) (c : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE c ∧
      Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ≅
        (toDerived W.toScheme).obj E) := by
  obtain ⟨I, q, c, hIa, hi, hq, hPa, hPc, hφ⟩ :=
    exists_bounded_module_open_roof R W hW E a b hqc
  let := hq
  let := hφ
  refine ⟨openPushforwardSectionsTruncation R W I c, c, hPa, hPc, ⟨?_⟩⟩
  exact asIso ((toDerived W.toScheme).map (openPushforwardSectionsTruncationComparison R W I c)) ≪≫
    (asIso ((toDerived W.toScheme).map q)).symm

/-- Every original locally-perfect complex on a compact affine open admits a
bounded module representative after actual open restriction. Finite projectivity
of the ambient representative is not asserted. -/
lemma locallyPerfect_exists_bounded_module_open_representative (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {E : Complex W.toScheme} (hE : locallyPerfect W.toScheme E) :
    ∃ (P : ModuleComplex R) (a c : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE c ∧
      Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ≅
        (toDerived W.toScheme).obj E) := by
  let : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  obtain ⟨a, b, hab⟩ := locallyPerfect_homology_bounded hE
  have ha : E.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro n hn
    exact (exactAt_iff_isZero_homology _ _).mpr (hab n (Or.inl hn))
  have hb : E.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro n hn
    exact (exactAt_iff_isZero_homology _ _).mpr (hab n (Or.inr hn))
  obtain ⟨P, c, hPa, hPc, he⟩ := exists_bounded_module_open_representative R W hW E a b
    (locallyPerfect_quasicoherent_homology hE)
  exact ⟨P, a, c, hPa, hPc, he⟩

end Quillen.PerfectComplexes.Affine
