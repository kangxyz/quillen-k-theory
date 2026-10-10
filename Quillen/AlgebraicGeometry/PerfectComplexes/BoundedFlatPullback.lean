/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedMinusPullbackComposition
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.StalkFlat
public import Quillen.AlgebraicGeometry.PerfectComplexes.PullbackNaturality

/-!
# Arbitrary pullback of bounded-above flat locally perfect complexes

The actual ambient derived pullback transports the original local derived
strict-model isomorphisms. Genuine flat-input comparisons identify both sides
with their termwise geometric pullbacks. Thus arbitrary pullback preserves
original local perfectness on bounded-above degreewise-flat inputs; the actual
flat model supplies such a representative for any bounded-above locally
perfect complex. No uniform bound for all perfect complexes on a non-quasi-compact
scheme, or Waldhausen K-equivalence, is asserted.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.CochainComplex Quillen.SchemeSheaf
attribute [local instance] HasDerivedCategory.standard
namespace Quillen.PerfectComplexes

/-- An actual derived isomorphism between bounded-above flat complexes survives
arbitrary termwise pullback. This uses the proved ambient derived functor. -/
def boundedFlatPullbackDerivedIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : BoundedAboveComplex Y.Modules)
    (hK : ∀ n, stalkwiseFlat Y (K.obj.X n))
    (hL : ∀ n, stalkwiseFlat Y (L.obj.X n))
    (e : (toDerived Y).obj K.obj ≅ (toDerived Y).obj L.obj) :
    (toDerived X).obj ((pullbackComplex f).obj K.obj) ≅
      (toDerived X).obj ((pullbackComplex f).obj L.obj) := by
  let e' : (boundedAboveQMinus Y.Modules).obj K ≅ (boundedAboveQMinus Y.Modules).obj L :=
    ObjectProperty.isoMk _ e
  exact (derivedPullbackMinusFlatObjectIso f K hK).symm ≪≫
    (DerivedCategory.Minus.ι).mapIso ((derivedPullbackMinus f).mapIso e') ≪≫
    derivedPullbackMinusFlatObjectIso f L hL

/-- Actual open restriction preserves strict upper support. -/
theorem boundedAbove_restrict {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {K : Complex Y} (hK : boundedAbove Y.Modules K) :
    boundedAbove X.Modules ((restrict j).obj K) := by
  obtain ⟨b, hb⟩ := hK
  refine ⟨b, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩
  intro n hn
  exact (Scheme.Modules.restrictFunctor j).map_isZero (K.isZero_of_isStrictlyLE b n hn)

/-- Strict complexes supply bounded-above flat inputs without a global projectivity assumption. -/
theorem strictPerfect_boundedAbove_stalkwiseFlat {X : Scheme.{u}} {K : Complex X}
    (hK : strictPerfect X K) :
    boundedAbove X.Modules K ∧ ∀ n, stalkwiseFlat X (K.X n) := by
  obtain ⟨⟨a, b, hbound⟩, hflat⟩ := hK
  refine ⟨⟨b, (CochainComplex.isStrictlyLE_iff _ _).mpr (fun n hn => hbound n (Or.inr hn))⟩, ?_⟩
  intro n
  let := hflat n
  exact stalkwiseFlat_of_finiteLocallyFree (K.X n)

/-- Arbitrary termwise pullback preserves the original genuinely local strict-model
predicate on bounded-above flat inputs. No uniform bound on all locally perfect objects is asserted.
-/
theorem locallyPerfect_pullback_of_boundedAbove_stalkwiseFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Complex Y} (hK : locallyPerfect Y K) (hbound : boundedAbove Y.Modules K)
    (hflat : ∀ n, stalkwiseFlat Y (K.X n)) :
    locallyPerfect X ((pullbackComplex f).obj K) := by
  intro x
  obtain ⟨U, hx, P, ⟨eP⟩⟩ := hK (f x)
  have hP := strictPerfect_boundedAbove_stalkwiseFlat P.property
  let KU : BoundedAboveComplex U.toScheme.Modules :=
    ⟨(restrict U.ι).obj K, boundedAbove_restrict U.ι hbound⟩
  let PU : BoundedAboveComplex U.toScheme.Modules := ⟨P.obj, hP.1⟩
  have hKU (n : ℤ) : stalkwiseFlat U.toScheme (KU.obj.X n) :=
    stalkwiseFlat_restrict U.ι (hflat n)
  refine ⟨f ⁻¹ᵁ U, hx, ⟨(pullbackComplex (f ∣_ U)).obj P.obj,
    strictPerfect_pullback (f ∣_ U) P.property⟩, ?_⟩
  exact ⟨(toDerived (f ⁻¹ᵁ U).toScheme).mapIso ((pullbackComplexRestrictIso f U).app K) ≪≫
    boundedFlatPullbackDerivedIso (f ∣_ U) KU PU hKU hP.2 eP⟩

/-- The actual flat replacement of a bounded-above locally perfect input is locally perfect. -/
theorem locallyPerfect_flatModel {X : Scheme.{u}} (K : BoundedAboveComplex X.Modules)
    (hK : locallyPerfect X K.obj) : locallyPerfect X (flatModel X K) :=
  (locallyPerfect_iff_of_quasiIso (flatModelπ X K)).mpr hK

/-- The constructed geometric flat model gives a locally perfect representative of the
actual ambient derived pullback whenever the original input is genuinely bounded above. -/
theorem locallyPerfect_pullback_flatModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : BoundedAboveComplex Y.Modules) (hK : locallyPerfect Y K.obj) :
    locallyPerfect X ((pullbackComplex f).obj (flatModel Y K)) :=
  locallyPerfect_pullback_of_boundedAbove_stalkwiseFlat f (locallyPerfect_flatModel K hK)
    (flatModelBounded Y K).property (flatModel_flat Y K)

end Quillen.PerfectComplexes
