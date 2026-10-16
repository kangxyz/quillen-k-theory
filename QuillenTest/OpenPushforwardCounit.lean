/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenPushforwardCounit
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Consumers of the original qc-open injective pushforward counit -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Quillen.PerfectComplexes.Affine
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace QuillenTest.OpenPushforwardCounit

variable {R : CommRingCat.{u}} (W : (Spec R).Opens)
  (hW : IsCompact (W : Set (Spec R))) (I : CochainComplex W.toScheme.Modules ℤ) (a : ℤ)
  (hb : ∀ n, n < a → IsZero (I.X n)) (hi : ∀ n, Injective (I.X n))
  (hq : ∀ n, (I.homology n).IsQuasicoherent)

include hW hb hi hq in
/-- Every unchanged original counit homology map has a two-sided inverse. -/
theorem original_counit_homology_inverse (n : ℤ) :
    ∃ t, HomologicalComplex.homologyMap
        (associatedSectionsCounit R ((pushforwardComplex W.ι).obj I)) n ≫ t = 𝟙 _ ∧
      t ≫ HomologicalComplex.homologyMap
        (associatedSectionsCounit R ((pushforwardComplex W.ι).obj I)) n = 𝟙 _ := by
  let := quasiIso_openPushforward_associatedSectionsCounit W hW I a hb hi hq
  have : IsIso (HomologicalComplex.homologyMap
      (associatedSectionsCounit R ((pushforwardComplex W.ι).obj I)) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  exact ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

include hW hb hi hq in
/-- Restricting reconstruction and applying the actual open counit recovers I weakly. -/
theorem original_open_reconstruction :
    QuasiIso ((restrict W.ι).map
        (associatedSectionsCounit R ((pushforwardComplex W.ι).obj I)) ≫
      ((pushforwardComplexRestrictIso W.ι).app I).hom) := by
  let := quasiIso_openPushforward_associatedSectionsCounit W hW I a hb hi hq
  infer_instance

include hW hb hi hq in
/-- The actual original derived reconstruction has QC target homology, with no upper bound. -/
theorem original_derived_reconstruction_and_qc :
    IsIso ((DerivedCategory.Q (C := (Spec R).Modules)).map
        (associatedSectionsCounit R ((pushforwardComplex W.ι).obj I))) ∧
      ∀ n : ℤ, (((pushforwardComplex W.ι).obj I).homology n).IsQuasicoherent := by
  let := quasiIso_openPushforward_associatedSectionsCounit W hW I a hb hi hq
  exact ⟨inferInstance, openPushforward_quasicoherent_homology W hW I a hb hi hq⟩

/-- Reconstruction retains naturality for the literal direct image of every chain map. -/
theorem original_counit_naturality {I J : CochainComplex W.toScheme.Modules ℤ} (f : I ⟶ J) :
    (associatedComplex R).map ((sectionsComplex R).map ((pushforwardComplex W.ι).map f)) ≫
        associatedSectionsCounit R ((pushforwardComplex W.ι).obj J) =
      associatedSectionsCounit R ((pushforwardComplex W.ι).obj I) ≫
        (pushforwardComplex W.ι).map f :=
  associatedSectionsCounit_naturality R _

/-- The original top-to-open restriction is genuinely invertible on direct-image complexes. -/
theorem original_top_restriction_inverse :
    ∃ t, affineSectionsComplexRestriction R (le_top : W ≤ ⊤)
        ((pushforwardComplex W.ι).obj I) ≫ t = 𝟙 _ ∧
      t ≫ affineSectionsComplexRestriction R (le_top : W ≤ ⊤)
        ((pushforwardComplex W.ι).obj I) = 𝟙 _ := by
  have := isIso_affineSectionsComplexRestriction_pushforward W.ι I (le_top : W ≤ ⊤) (by
    simp)
  exact ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

end QuillenTest.OpenPushforwardCounit
