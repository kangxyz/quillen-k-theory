/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.InjectiveComplex
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.AffineCechCover

/-! Consumers of the original two-open section sequence: gluing compatible
sections without flasqueness, and a genuine injective resolution on the
projective line's polynomial chart cover. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.TwoOpen AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace QuillenTest.TwoOpenCohomology


lemma glue_compatible_sections {X : Scheme.{u}} (M : X.Modules)
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (a : Γ(M, U)) (b : Γ(M, V))
    (hab : res M inf_le_left a = res M inf_le_right b) :
    ∃! t : Γ(M, ⊤), augmentation M U V t = (a, b) := by
  obtain ⟨t, ht⟩ := (ShortComplex.ab_exact_iff _).mp (sectionSequence_exact M U V hUV)
    (a, b) (sub_eq_zero.mpr hab)
  exact ⟨t, ht, fun t' ht' => augmentation_injective M U V hUV (ht'.trans ht.symm)⟩

lemma projectiveLine_injectiveResolution_sequence (R : CommRingCat.{u})
    (M : (twoChartLine R).Modules) (I : InjectiveResolution M) :
    (cochainSequence (chartOpen R true) (chartOpen R false) I.cocomplex).ShortExact :=
  injectiveResolution_cochainSequence_shortExact _ _ (chart_ranges_cover R) M I

end QuillenTest.TwoOpenCohomology
