/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Minus.PullbackComposition
public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.StalkFlat
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Pullback
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.Algebra.Homology.CochainComplex.BoundedAbove.Basic
public import Aglib.AlgebraicGeometry.Modules.Complex.Flat.Models
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Minus.Pullback
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



open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] HasDerivedCategory.standard
namespace Quillen.PerfectComplexes

/-- An actual derived isomorphism between bounded-above flat complexes survives
arbitrary termwise pullback. This uses the proved ambient derived functor. -/
def boundedFlatPullbackDerivedIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : _root_.CochainComplex.BoundedAboveComplex Y.Modules)
    (hK : ∀ n, stalkwiseFlat Y (K.obj.X n))
    (hL : ∀ n, stalkwiseFlat Y (L.obj.X n))
    (e : (DerivedCategory.Q (C := Y.Modules)).obj K.obj ≅
      (DerivedCategory.Q (C := Y.Modules)).obj L.obj) :
    (DerivedCategory.Q (C := X.Modules)).obj ((AlgebraicGeometry.Scheme.Modules.Complex.pullback
      f).obj K.obj) ≅
      (DerivedCategory.Q (C := X.Modules)).obj ((AlgebraicGeometry.Scheme.Modules.Complex.pullback
        f).obj L.obj) := by
  let e' : (_root_.CochainComplex.boundedAboveQMinus Y.Modules).obj K ≅
    (_root_.CochainComplex.boundedAboveQMinus Y.Modules).obj L :=
    ObjectProperty.isoMk _ e
  exact (derivedPullbackMinusFlatObjectIso f K hK).symm ≪≫
    (DerivedCategory.Minus.ι).mapIso ((derivedPullbackMinus f).mapIso e') ≪≫
    derivedPullbackMinusFlatObjectIso f L hL

/-- Actual open restriction preserves strict upper support. -/
theorem boundedAbove_restrict {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {K : CochainComplex Y.Modules ℤ} (hK : _root_.CochainComplex.boundedAbove Y.Modules K) :
    _root_.CochainComplex.boundedAbove X.Modules ((restrict j).obj K) := by
  obtain ⟨b, hb⟩ := hK
  refine ⟨b, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩
  intro n hn
  exact (Scheme.Modules.restrictFunctor j).map_isZero (K.isZero_of_isStrictlyLE b n hn)

/-- Strict complexes supply bounded-above flat inputs without a global projectivity assumption. -/
theorem strictPerfect_boundedAbove_stalkwiseFlat {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}
    (hK : strictPerfect X K) :
    _root_.CochainComplex.boundedAbove X.Modules K ∧ ∀ n, stalkwiseFlat X (K.X n) := by
  obtain ⟨⟨a, b, hbound⟩, hflat⟩ := hK
  refine ⟨⟨b, (CochainComplex.isStrictlyLE_iff _ _).mpr (fun n hn => hbound n (Or.inr hn))⟩, ?_⟩
  intro n
  let := hflat n
  exact stalkwiseFlat_of_finiteLocallyFree (K.X n)

/-- Arbitrary termwise pullback preserves the original genuinely local strict-model
predicate on bounded-above flat inputs. No uniform bound on all locally perfect objects is asserted.
-/
theorem locallyPerfect_pullback_of_boundedAbove_stalkwiseFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : CochainComplex Y.Modules ℤ} (hK : locallyPerfect Y K) (hbound :
      _root_.CochainComplex.boundedAbove Y.Modules K)
    (hflat : ∀ n, stalkwiseFlat Y (K.X n)) :
    locallyPerfect X ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj K) := by
  intro x
  obtain ⟨U, hx, P, ⟨eP⟩⟩ := hK (f x)
  have hP := strictPerfect_boundedAbove_stalkwiseFlat P.property
  let KU : _root_.CochainComplex.BoundedAboveComplex U.toScheme.Modules :=
    ⟨(restrict U.ι).obj K, boundedAbove_restrict U.ι hbound⟩
  let PU : _root_.CochainComplex.BoundedAboveComplex U.toScheme.Modules := ⟨P.obj, hP.1⟩
  have hKU (n : ℤ) : stalkwiseFlat U.toScheme (KU.obj.X n) :=
    stalkwiseFlat_restrict U.ι (hflat n)
  refine ⟨f ⁻¹ᵁ U, hx, ⟨(AlgebraicGeometry.Scheme.Modules.Complex.pullback (f ∣_ U)).obj P.obj,
    strictPerfect_pullback (f ∣_ U) P.property⟩, ?_⟩
  exact ⟨(DerivedCategory.Q (C := (f ⁻¹ᵁ U).toScheme.Modules)).mapIso
    ((AlgebraicGeometry.Scheme.Modules.Complex.pullbackRestrictIso f U).app K) ≪≫
    boundedFlatPullbackDerivedIso (f ∣_ U) KU PU hKU hP.2 eP⟩

/-- The actual flat replacement of a bounded-above locally perfect input is locally perfect. -/
theorem locallyPerfect_flatModel {X : Scheme.{u}} (K : _root_.CochainComplex.BoundedAboveComplex
  X.Modules)
    (hK : locallyPerfect X K.obj) : locallyPerfect X (flatModel X K) :=
  (locallyPerfect_iff_of_quasiIso (flatModelπ X K)).mpr hK

/-- The constructed geometric flat model gives a locally perfect representative of the
actual ambient derived pullback whenever the original input is genuinely bounded above. -/
theorem locallyPerfect_pullback_flatModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : _root_.CochainComplex.BoundedAboveComplex Y.Modules) (hK : locallyPerfect Y K.obj) :
    locallyPerfect X ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj (flatModel Y K)) :=
  locallyPerfect_pullback_of_boundedAbove_stalkwiseFlat f (locallyPerfect_flatModel K hK)
    (flatModelBounded Y K).property (flatModel_flat Y K)

end Quillen.PerfectComplexes
