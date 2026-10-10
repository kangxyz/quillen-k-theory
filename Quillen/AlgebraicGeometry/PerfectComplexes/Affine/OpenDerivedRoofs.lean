/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenModuleAdjunction
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalRestrictionQuasiIso
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FinitePrincipalRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PerfectOpenApproximation

/-!
# Genuine geometric roofs and equality denominators on qc affine opens

Every original derived morphism between the restrictions of a global bounded
finite-projective module complex and a cohomologically lower-bounded module
complex has a genuine finite-projective source denominator and an actual global
chain numerator. The denominator is weak after the original restriction, and
the displayed square is an equality in the original sheaf derived category.
Equality of original restricted chain maps similarly admits an actual global
homotopy after such a denominator. Finite-projective targets need no separately
supplied cohomological bound.

The proof constructs the target's genuine lower-bounded injective model, uses
the actual module/open adjunction and its proved qc-open counit, and applies
supported module denominators on a genuine finite principal cover. No supplied
geometric roof, global-sections exactness, or all-sheaf projectivity is assumed.
The ambient target is an actual module complex; arbitrary non-quasicoherent
all-sheaf targets are outside this theorem's scope.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] standardDerivedModules standardDerivedSheaves

lemma exists_open_module_roof_from_injective_model (R : CommRingCat.{u})
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
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) := by
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
  obtain ⟨P', hP', t, g, ⟨H⟩, ht⟩ := exists_finite_principal_chain_roof R s hP η hηs f
  refine ⟨P', hP', t, g, quasiIso_restrict_associated_of_principalUnion R W s hs t ht, ?_⟩
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
lemma exists_quasiCompact_open_derived_module_roof (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P B : ModuleComplex R} (hP : moduleStrictPerfect R P) (b : ℤ) [B.IsGE b]
    (α : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ⟶
      (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj B))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t : P' ⟶ P) (g : P' ⟶ B),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ α =
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) := by
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
  exact exists_open_module_roof_from_injective_model R W hW hP I b
    (fun n hn => (CochainComplex.isStrictlyGE_iff I b).mp hIb n hn) hI hqcI q α

/-- In particular, both original global finite-projective models have the
exact qc-open numerator/denominator roof, with no auxiliary bound premise. -/
lemma exists_quasiCompact_open_strict_module_roof (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P B : ModuleComplex R} (hP : moduleStrictPerfect R P) (hB : moduleStrictPerfect R B)
    (α : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ⟶
      (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj B))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t : P' ⟶ P) (g : P' ⟶ B),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ α =
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) := by
  obtain ⟨a, b, hb⟩ := hB.1
  have : B.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff B a).mpr
    (fun n hn => hb n (Or.inl hn))
  exact exists_quasiCompact_open_derived_module_roof R W hW hP a α

/-- Equality of original open derived chain maps is witnessed by a genuine
homotopy after a finite-projective denominator weak on the chosen qc open. -/
lemma exists_open_module_equality_from_injective_model (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P B : ModuleComplex R} (hP : moduleStrictPerfect R P) (I : Complex W.toScheme)
    (a : ℤ) (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent)
    (q : (restrict W.ι).obj ((associatedComplex R).obj B) ⟶ I) [QuasiIso q]
    (f g : P ⟶ B)
    (hfg : (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map f)) =
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t : P' ⟶ P),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      Nonempty (Homotopy (t ≫ f) (t ≫ g)) := by
  let η := openModuleChainAdjoint R W.ι q
  have hη := quasiIso_restrict_associated_openModuleChainAdjoint R W hW a hbound hinj hqc q
  obtain ⟨s, hs⟩ := exists_finite_principal_cover R W hW
  have hηs (r : R) (hr : r ∈ s) : QuasiIso ((localize r (.up ℤ)).map η) := by
    apply quasiIso_localize_of_restrict_associated R W η r
    rw [← hs]
    exact Quillen.SheafCohomology.basicOpen_le_principalUnion R hr
  have H := homotopy_comp_openModuleChainAdjoint_of_derived_eq R W.ι I a hbound hinj q f g hfg
  obtain ⟨P', hP', t, ht, hlocal⟩ := exists_finite_principal_chain_equality R s hP η hηs f g
    (DerivedCategory.Q_map_eq_of_homotopy _ H)
  exact ⟨P', hP', t, quasiIso_restrict_associated_of_principalUnion R W s hs t hlocal, ht⟩

/-- The original open derived equality requires only a lower cohomological
bound on the global module target. The output is an actual global homotopy. -/
lemma exists_quasiCompact_open_module_equality (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P B : ModuleComplex R} (hP : moduleStrictPerfect R P) (b : ℤ) [B.IsGE b]
    (f g : P ⟶ B)
    (hfg : (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map f)) =
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t : P' ⟶ P),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      Nonempty (Homotopy (t ≫ f) (t ≫ g)) := by
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
  exact exists_open_module_equality_from_injective_model R W hW hP I b
    (fun n hn => (CochainComplex.isStrictlyGE_iff I b).mp hIb n hn) hI hqcI q f g hfg

/-- Finite-projective global targets need no separately chosen lower bound. -/
lemma exists_quasiCompact_open_strict_module_equality (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P B : ModuleComplex R} (hP : moduleStrictPerfect R P) (hB : moduleStrictPerfect R B)
    (f g : P ⟶ B)
    (hfg : (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map f)) =
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t : P' ⟶ P),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      Nonempty (Homotopy (t ≫ f) (t ≫ g)) := by
  obtain ⟨a, b, hb⟩ := hB.1
  have : B.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff B a).mpr
    (fun n hn => hb n (Or.inl hn))
  exact exists_quasiCompact_open_module_equality R W hW hP a f g hfg

end Quillen.PerfectComplexes.Affine
