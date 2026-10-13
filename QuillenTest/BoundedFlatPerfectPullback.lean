/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlatPullback
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlatExtensions

/-! Semantic consumers of original local-perfect preservation under arbitrary pullback. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.CochainComplex Quillen.SchemeSheaf Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard
namespace QuillenTest.BoundedFlatPerfectPullback

open Quillen

/-- The original local-perfect predicate is preserved with an explicit arbitrary upper bound. -/
theorem actual_local_perfect_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Complex Y) (b : ℤ) [K.IsStrictlyLE b]
    (hK : locallyPerfect Y K) (hflat : ∀ n, stalkwiseFlat Y (K.X n)) :
    locallyPerfect X ((pullbackComplex f).obj K) :=
  locallyPerfect_pullback_of_boundedAbove_stalkwiseFlat f hK ⟨b, inferInstance⟩ hflat

/-- An original local-perfect input has an actual local-perfect geometric representative
of its ambient derived pullback, rather than only a new abstract object predicate. -/
theorem actual_derived_perfect_representative {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : BoundedAboveComplex Y.Modules) (hK : locallyPerfect Y K.obj) :
    ∃ P : Perfect X, Nonempty
      (((derivedPullbackMinus f).obj ((boundedAboveQMinus Y.Modules).obj K)).obj ≅
        (toDerived X).obj P.obj) :=
  ⟨⟨(pullbackComplex f).obj (flatModel Y K), locallyPerfect_pullback_flatModel f K hK⟩,
    ⟨derivedPullbackMinusObjectIso f K⟩⟩

/-- On original strict-perfect complexes the local-flat criterion recovers actual
geometric local perfectness with no global projectivity or flat-map premise. -/
theorem strict_input_local_perfect_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : StrictPerfect Y) : locallyPerfect X ((pullbackComplex f).obj P.obj) :=
  locallyPerfect_pullback_of_boundedAbove_stalkwiseFlat f
    (locallyPerfect_of_strictPerfect P.property)
    (strictPerfect_boundedAbove_stalkwiseFlat P.property).1
    (strictPerfect_boundedAbove_stalkwiseFlat P.property).2

/-- The original derived inverse to an isomorphism of flat bounded inputs also
pulls back to an actual two-sided inverse in the original localization. -/
theorem actual_pulled_back_inverse {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : BoundedAboveComplex Y.Modules)
    (hK : ∀ n, stalkwiseFlat Y (K.obj.X n))
    (hL : ∀ n, stalkwiseFlat Y (L.obj.X n))
    (e : (toDerived Y).obj K.obj ≅ (toDerived Y).obj L.obj) :
    ∃ a : (toDerived X).obj ((pullbackComplex f).obj K.obj) ⟶
        (toDerived X).obj ((pullbackComplex f).obj L.obj), IsIso a :=
  ⟨(boundedFlatPullbackDerivedIso f K L hK hL e).hom, inferInstance⟩

/-- An actual possibly nonsplit extension of flat sheaves stays flat, and its
original short exact sequence remains exact after every scheme pullback. -/
theorem actual_flat_extension_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {S : ShortComplex Y.Modules} (hS : S.ShortExact)
    (h₁ : stalkwiseFlat Y S.X₁) (h₃ : stalkwiseFlat Y S.X₃) :
    stalkwiseFlat X ((Scheme.Modules.pullback f).obj S.X₂) ∧
      (S.map (Scheme.Modules.pullback f)).ShortExact :=
  ⟨stalkwiseFlat_pullback f (stalkwiseFlat_middle_of_shortExact hS h₁ h₃),
    shortExact_pullback_of_stalkwiseFlat_quotient f hS h₃⟩

end QuillenTest.BoundedFlatPerfectPullback
