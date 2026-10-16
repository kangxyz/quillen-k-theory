/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Extension
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure
public import Quillen.Aglib.Algebra.Homology.CochainComplex.QuasiIsoGluing

/-!
# Actual perfect stabilization

The original sum with the degree-one shift and its block-diagonal chain map preserve actual quasi-isomorphisms.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.OpenWeakImage

/-- The actual original shifted sum, as a locally perfect complex. -/
def shiftSum {X : Scheme.{u}} (P : Perfect X) : Perfect X :=
  ⟨P.obj ⊞ P.obj⟦(1 : ℤ)⟧,
    (abelianExactStructure _).prop_biprod _ P.property (locallyPerfect_shift P.property 1)⟩

/-- The original block-diagonal map, with the literal shift of the original map. -/
def shiftSumMap {X : Scheme.{u}} {P Q : Perfect X} (f : P ⟶ Q) : shiftSum P ⟶ shiftSum Q :=
  ObjectProperty.homMk (biprod.map f.hom (f.hom⟦(1 : ℤ)⟧'))

/-- Actual weak strict comparisons remain weak after the original stabilization. -/
theorem shiftSumMap_weak {X : Scheme.{u}} {P Q : Perfect X} (f : P ⟶ Q)
    (hf : QuasiIso f.hom) : QuasiIso (shiftSumMap f).hom := by
  let : QuasiIso f.hom := hf
  exact Waldhausen.quasiIso_biprod_map f.hom (f.hom⟦(1 : ℤ)⟧')

end Quillen.PerfectComplexes.OpenWeakImage

end

end
