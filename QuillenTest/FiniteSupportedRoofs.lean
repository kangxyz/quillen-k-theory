/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.FiniteSupportedRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.FiniteSupportedEquality

/-!
# Finite families of source-supported roofs

Regression statements use one source-supported perfect denominator for a finite
family of local derived isomorphisms or chain-map equalities. They retain the
inverse roof equations and global homotopies, and include an empty target family.
-/

@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u v
namespace QuillenTest.FiniteSupportedRoofs
open Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] Affine.standardDerivedSheaves

/-- Every original local isomorphism in a finite family has an actual weak
numerator over the same source-supported global denominator, retaining each inverse equation. -/
theorem original_finite_isomorphism_roofs {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A : Complex X} (hA : locallyPerfect X A) {ι : Type v} [Fintype ι]
    (B : ι → Complex X) (hB : ∀ i, locallyPerfect X (B i))
    (hzA : IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj A)))
    (e : ∀ i, (toDerived U).obj ((restrict j).obj A) ≅ (toDerived U).obj ((restrict j).obj (B i))) :
    ∃ (M : Complex X) (q : M ⟶ A) (g : ∀ i, M ⟶ B i), locallyPerfect X M ∧
      QuasiIso ((restrict j).map q) ∧ IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj M)) ∧
      ∀ i, QuasiIso ((restrict j).map (g i)) ∧
        (toDerived U).map ((restrict j).map (g i)) ≫ (e i).inv =
          (toDerived U).map ((restrict j).map q) := by
  obtain ⟨M,q,g,hM,hq,hzM,hg⟩ := exists_source_supported_finite_roof j T hT hA
    Finset.univ B hB hzA (fun i => (e i).hom)
  refine ⟨M,q,(fun i => g i (Finset.mem_univ i)),hM,hq,hzM,?_⟩
  intro i
  have hi : IsIso ((toDerived U).map ((restrict j).map (g i (Finset.mem_univ i)))) := by
    rw [← hg i (Finset.mem_univ i)]
    infer_instance
  refine ⟨(DerivedCategory.isIso_Q_map_iff_quasiIso U.Modules _).mp hi,?_⟩
  rw [← hg i (Finset.mem_univ i),Category.assoc,Iso.hom_inv_id,Category.comp_id]

/-- Original chain equalities on the open are represented simultaneously by
genuine global homotopies, with one actual source-supported perfect denominator. -/
theorem original_finite_chain_homotopies {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A : Complex X} (hA : locallyPerfect X A) {ι : Type v} [Fintype ι]
    (B : ι → Complex X) (b : ι → ℤ) [∀ i, (B i).IsGE (b i)]
    (hB : ∀ i n, ((B i).homology n).IsQuasicoherent)
    (hzA : IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj A)))
    (f g : ∀ i, A ⟶ B i)
    (heq : ∀ i, (toDerived U).map ((restrict j).map (f i)) =
      (toDerived U).map ((restrict j).map (g i))) :
    ∃ (M : Complex X) (q : M ⟶ A), locallyPerfect X M ∧ QuasiIso ((restrict j).map q) ∧
      IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj M)) ∧
      ∀ i, Nonempty (Homotopy (q ≫ f i) (q ≫ g i)) := by
  obtain ⟨M,q,hM,hq,hzM,H⟩ := exists_source_supported_finite_homotopies j T hT hA
    Finset.univ B b hB hzA f g (fun i _ => heq i)
  exact ⟨M,q,hM,hq,hzM,fun i => H i (Finset.mem_univ i)⟩

/-- Empty families over an empty target index type still produce a genuine
supported denominator, without choosing any target complex. -/
theorem empty_family_supported_source {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A : Complex X} (hA : locallyPerfect X A)
    (hzA : IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj A))) :
    ∃ (M : Complex X) (q : M ⟶ A), locallyPerfect X M ∧ QuasiIso ((restrict j).map q) ∧
      IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj M)) := by
  obtain ⟨M,q,g,hM,hq,hzM,hg⟩ := exists_source_supported_finite_roof j T hT hA
    (∅ : Finset Empty) (fun i => i.elim) (fun i => i.elim) hzA (fun i => i.elim)
  exact ⟨M,q,hM,hq,hzM⟩

end QuillenTest.FiniteSupportedRoofs
