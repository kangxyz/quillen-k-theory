/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SourceSupportDenominators
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenDerivedRoofs

/-! # Actual qc-open geometric roofs retain original source support

The genuine module/open adjunction and source-support-preserving finite
principal denominators produce actual global numerators with the same
original derived restriction equation. The target is a cohomologically
lower-bounded module complex. Every extra principal acyclicity condition on
the source passes to the constructed finite-projective denominator.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] standardDerivedModules standardDerivedSheaves

/-- The actual injective model and original adjunction produce a geometric roof preserving source
  support. -/
lemma exists_open_module_roof_preserving_source_support_from_injective_model (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P B : ModuleComplex R} (hP : moduleStrictPerfect R P) (I : Complex W.toScheme)
    (a : ℤ) (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent)
    (q : (restrict W.ι).obj ((associatedComplex R).obj B) ⟶ I) [QuasiIso q]
    (α : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ⟶
      (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj B))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t : P' ⟶ P) (g : P' ⟶ B),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ α =
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) ∧
      ∀ r : R, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P)) →
        IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P')) := by
  let η := openModuleChainAdjoint R W.ι q
  have hη := quasiIso_restrict_associated_openModuleChainAdjoint R W hW a hbound hinj hqc q
  obtain ⟨s, hs⟩ := exists_finite_principal_cover R W hW
  have hsr (r : R) (hr : r ∈ s) : PrimeSpectrum.basicOpen r ≤ W := by
    rw [← hs]
    exact Quillen.SheafCohomology.basicOpen_le_principalUnion R hr
  have hηs (r : R) (hr : r ∈ s) : QuasiIso ((localize r (.up ℤ)).map η) :=
    quasiIso_localize_of_restrict_associated R W η r (hsr r hr)
  obtain ⟨f, hf⟩ := exists_openModuleChainAdjoint R W.ι P I a hbound hinj
    (α ≫ (toDerived W.toScheme).map q)
  obtain ⟨P', hP', t, g, ⟨H⟩, ht, hsource⟩ :=
    exists_finite_principal_chain_roof_preserving_source_support R s hP η hηs f
  refine ⟨P', hP', t, g, quasiIso_restrict_associated_of_principalUnion R W s hs t ht, ?_, hsource⟩
  have heq := DerivedCategory.Q_map_eq_of_homotopy _
    (((tilde.functor R) ⋙ Scheme.Modules.restrictFunctor W.ι).mapHomotopy H)
  change (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map (g ≫ η))) =
    (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map (t ≫ f))) at heq
  rw [(associatedComplex R).map_comp, (associatedComplex R).map_comp,
    (restrict W.ι).map_comp, (restrict W.ι).map_comp,
    (toDerived W.toScheme).map_comp, (toDerived W.toScheme).map_comp] at heq
  have hηc : (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map η)) ≫
      (toDerived W.toScheme).map (openModuleComplexCounit R W.ι I) =
        (toDerived W.toScheme).map q := by
    rw [← (toDerived W.toScheme).map_comp]
    exact congrArg ((toDerived W.toScheme).map) (openModuleChainAdjoint_counit R W.ι q)
  apply (cancel_mono ((toDerived W.toScheme).map q)).mp
  calc
    ((toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ α) ≫
        (toDerived W.toScheme).map q =
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫
        ((toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map f)) ≫
          (toDerived W.toScheme).map (openModuleComplexCounit R W.ι I)) := by
            rw [Category.assoc, hf]
    _ = ((toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) ≫
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map η))) ≫
          (toDerived W.toScheme).map (openModuleComplexCounit R W.ι I) := by
            rw [← Category.assoc, heq]
    _ = (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) ≫
        (toDerived W.toScheme).map q := by rw [Category.assoc, hηc]

/-- Original qc-open derived arrows between associated module complexes have
genuine finite-projective denominator roofs. Only the target's lower
cohomological bound is required, and no injective model is supplied. -/
lemma exists_quasiCompact_open_module_roof_preserving_source_support (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P B : ModuleComplex R} (hP : moduleStrictPerfect R P) (b : ℤ) [B.IsGE b]
    (α : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ⟶
      (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj B))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t : P' ⟶ P) (g : P' ⟶ B),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ α =
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) ∧
      ∀ r : R, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P)) →
        IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P')) := by
  let E := (restrict W.ι).obj ((associatedComplex R).obj B)
  have hEb : E.IsGE b := by
    rw [CochainComplex.isGE_iff]
    intro n hn
    exact ((B.exactAt_of_isGE b n hn).map (tilde.functor R)).map
      (Scheme.Modules.restrictFunctor W.ι)
  have hEqc (n : ℤ) : (E.homology n).IsQuasicoherent := by
    apply CoherentScheme.quasicoherent_homology E
    intro m
    change ((Scheme.Modules.restrictFunctor W.ι).obj ((tilde.functor R).obj (B.X
      m))).IsQuasicoherent
    infer_instance
  have : QuasiIso (E.πTruncGE b) := (E.quasiIso_πTruncGE_iff b).mpr hEb
  obtain ⟨I, s, hs, hI, hIb⟩ :=
    _root_.CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective (E.truncGE b) b
  have := hs
  let q : E ⟶ I := E.πTruncGE b ≫ s
  have : QuasiIso q := inferInstance
  have hqcI (n : ℤ) : (I.homology n).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      (isoOfQuasiIsoAt q n) (hEqc n)
  exact exists_open_module_roof_preserving_source_support_from_injective_model R W hW hP I b
    (fun n hn => (CochainComplex.isStrictlyGE_iff I b).mp hIb n hn) hI hqcI q α

/-- In particular, both original global finite-projective models have the
exact qc-open numerator/denominator roof, with no auxiliary bound premise. -/
lemma exists_quasiCompact_open_strict_roof_preserving_source_support (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P B : ModuleComplex R} (hP : moduleStrictPerfect R P) (hB : moduleStrictPerfect R B)
    (α : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ⟶
      (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj B))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t : P' ⟶ P) (g : P' ⟶ B),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ α =
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) ∧
      ∀ r : R, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P)) →
        IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P')) := by
  obtain ⟨a, b, hb⟩ := hB.1
  have : B.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff B a).mpr
    (fun n hn => hb n (Or.inl hn))
  exact exists_quasiCompact_open_module_roof_preserving_source_support R W hW hP a α

end Quillen.PerfectComplexes.Affine
