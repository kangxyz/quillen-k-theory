/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Algebra.Homology.HomotopyPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenFibration

/-!
# Strict and locally perfect homotopy pullbacks

The literal mapping-cocone construction preserves strict perfection and local
perfection on arbitrary schemes. The proof uses the established closure under
finite biproducts, actual cones, and shifts, without affine or uniform-bound
hypotheses.
-/
@[expose] public section

open Quillen.CochainComplex


open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

/-- The literal mapping-cocone homotopy pullback of strict-perfect complexes
is strict perfect, on an arbitrary scheme. -/
lemma strictPerfect_homotopyPullback {X : Scheme.{u}} {A B T : Complex X}
    (hA : strictPerfect X A) (hB : strictPerfect X B) (hT : strictPerfect X T)
    (f : A ⟶ T) (g : B ⟶ T) : strictPerfect X (homotopyPullback f g) := by
  have hAB : strictPerfect X (A ⊞ B) :=
    (abelianExactStructure (Complex X)).prop_biprod (strictPerfect X) hA hB
  exact strictPerfect_shift (strictPerfect_mappingCone hAB hT (biprod.desc f (-g))) (-1)

/-- The literal mapping-cocone homotopy pullback preserves local perfection
without quasi-compactness, affine, termwise-QC or uniform-bound hypotheses. -/
lemma locallyPerfect_homotopyPullback {X : Scheme.{u}} {A B T : Complex X}
    (hA : locallyPerfect X A) (hB : locallyPerfect X B) (hT : locallyPerfect X T)
    (f : A ⟶ T) (g : B ⟶ T) : locallyPerfect X (homotopyPullback f g) := by
  have hAB : locallyPerfect X (A ⊞ B) :=
    (abelianExactStructure (Complex X)).prop_biprod (locallyPerfect X) hA hB
  exact locallyPerfect_shift (locallyPerfect_mappingCone hAB hT (biprod.desc f (-g))) (-1)

end Quillen.PerfectComplexes
