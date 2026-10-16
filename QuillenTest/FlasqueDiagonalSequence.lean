/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueDiagonalSequence

/-! # Literal original flasque diagonal sequence consumers

The original incidence and quotient are monic and epic. Their exact extension
functor preserves the four actual maps of an inherited admissible pushout.
-/
@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes AlgebraicGeometry.Scheme.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal

namespace FlasqueDiagonalSequenceConsumers

/-- The literal pushed-total incidence is monic over every original base ring. -/
theorem original_incidence_mono (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    Mono ((rawIncidence R).app K) :=
  (rawSequence_shortExact R K).mono_f

/-- The literal pushed-total quotient is epic over every original base ring. -/
theorem original_quotient_epi (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    Epi ((rawQuotient R).app K) :=
  (rawSequence_shortExact R K).epi_g

/-- The actual original extension retains all four maps of an admissible pushout. -/
theorem original_extension_pushout (R : CommRingCat.{u})
    {A B D T : FlasqueBoundedBelow.Obj (twoChartLine R)}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ T} {j : D ⟶ T}
    (hi : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof i)
    (h : IsPushout i f g j) :
    IsPushout ((extensionFunctor R).map i) ((extensionFunctor R).map f)
      ((extensionFunctor R).map g) ((extensionFunctor R).map j) :=
  (extension_exact R).pushout hi h

end FlasqueDiagonalSequenceConsumers
