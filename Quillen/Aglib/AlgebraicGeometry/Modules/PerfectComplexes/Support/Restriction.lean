/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Extension
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Strict
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Perfect
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.RestrictionVanishing
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic

/-!
# Exact restriction with a prescribed support

Derived vanishing is actual acyclicity. Literal open restriction preserves the support on the original inverse-image open and the inherited short exact sequences.
-/
@[expose] public section

open Quillen.Waldhausen


open AlgebraicGeometry.Scheme.Modules.Complex


open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes
open Waldhausen
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts

/-- Original derived vanishing is precisely actual acyclicity of the complex. -/
lemma isZero_toDerived_iff_acyclic {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) :
    IsZero ((DerivedCategory.Q (C := X.Modules)).obj K) ↔ K.Acyclic := by
  constructor
  · intro h n
    rw [exactAt_iff_isZero_homology]
    exact ((DerivedCategory.homologyFunctor X.Modules n).map_isZero h).of_iso
      ((DerivedCategory.homologyFunctorFactors X.Modules n).app K).symm
  · intro h
    have : QuasiIso (0 : K ⟶ K) := by
      rw [quasiIso_iff]
      intro n
      exact (quasiIsoAt_iff_exactAt (0 : K ⟶ K) n (h n)).mpr (h n)
    have hi : IsIso ((DerivedCategory.Q (C := X.Modules)).map (0 : K ⟶ K)) := inferInstance
    rw [(DerivedCategory.Q (C := X.Modules)).map_zero] at hi
    exact (isIsoZero_iff_source_target_isZero _ _).mp hi |>.1

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- Original termwise restriction preserves the prescribed actual support. -/
lemma perfectSupported_restrict {P : CochainComplex X.Modules ℤ} (hP : perfectSupported T.ι P) :
    perfectSupported (j ⁻¹ᵁ T).ι ((restrict j).obj P) := by
  refine ⟨locallyPerfect_restrict j hP.1, ?_⟩
  rw [← isZero_toDerived_iff_acyclic]
  exact isZero_restrict_preimage_of_isZero j T P
    ((isZero_toDerived_iff_acyclic _).mpr hP.2)

/-- Actual restriction between the existing supported perfect categories. -/
def perfectSupportedRestrict : (perfectSupported T.ι).FullSubcategory ⥤
    (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory :=
  (perfectSupported (j ⁻¹ᵁ T).ι).lift ((perfectSupported T.ι).ι ⋙ restrict j)
    (fun P => perfectSupported_restrict j T P.property)

instance perfectSupportedRestrict_additive : (perfectSupportedRestrict j T).Additive := by
  unfold perfectSupportedRestrict
  infer_instance

/-- The original supported restriction preserves genuine short exact sequences. -/
def perfectSupportedExactRestrict : CategoryTheory.ExactCategory.ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (perfectSupported T.ι))
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex U.Modules ℤ))
      (perfectSupported (j ⁻¹ᵁ T).ι)) where
  toFunctor := perfectSupportedRestrict j T
  map_conflation S hS := by
    change ((S.map (perfectSupported T.ι).ι).map (restrict j)).ShortExact
    exact hS.map_of_exact _

end Quillen.PerfectComplexes

end

end
