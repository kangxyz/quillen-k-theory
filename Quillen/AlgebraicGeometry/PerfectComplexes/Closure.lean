/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Strict
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Strict-perfect closure under shifts and cones

These are actual operations on cochain complexes of module sheaves. The cone
terms are finite biproducts, so the proof uses local vector-bundle extension
closure and genuine termwise bounds, with no global projectivity assumption.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
variable {X : Scheme.{u}} {P Q : Complex X}

/-- Every integer shift of a strict-perfect complex is strict perfect. -/
theorem strictPerfect_shift (hP : strictPerfect X P) (n : ℤ) :
    strictPerfect X ((shiftFunctor (Complex X) n).obj P) := by
  obtain ⟨⟨a, b, hb⟩, hv⟩ := hP
  constructor
  · refine ⟨a - n, b - n, fun j hj => ?_⟩
    change IsZero (P.X (j + n))
    exact hb (j + n) (by omega)
  · intro j
    exact hv (j + n)

/-- The actual mapping cone of a map between strict-perfect complexes is
strict perfect, regardless of whether the map is a cofibration. -/
theorem strictPerfect_mappingCone (hP : strictPerfect X P) (hQ : strictPerfect X Q)
    (f : P ⟶ Q) : strictPerfect X (CochainComplex.mappingCone f) := by
  obtain ⟨⟨a, b, hbP⟩, hvP⟩ := hP
  obtain ⟨⟨c, d, hbQ⟩, hvQ⟩ := hQ
  constructor
  · refine ⟨min (a - 1) c, max (b - 1) d, fun j hj => ?_⟩
    apply (CochainComplex.mappingCone.isZero_X_iff f j).2
    exact ⟨hbP (j + 1) (by omega), hbQ j (by omega)⟩
  · intro j
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod f j (j + 1) rfl
    apply (SchemeSheaf.finiteLocallyFree_iff_of_iso e).2
    exact (SchemeSheaf.sheafExactStructure X).prop_biprod
      (SchemeSheaf.finiteLocallyFree X) (hvP (j + 1)) (hvQ j)
end Quillen.PerfectComplexes
