/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Closure
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Strict
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Perfect
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# Supported bounded-flat perfect complexes

Support is actual restricted acyclicity. The original zero, isomorphism, extension, finite-product, shift and cone closure and literal supported inclusion are unchanged.
-/
@[expose] public section

attribute [local instance] AlgebraicGeometry.Scheme.Modules.Complex.restrictCommShift

open AlgebraicGeometry.Scheme.Modules.Complex


open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The property of bounded-above, stalkwise-flat locally perfect complexes on `X` whose
restriction along `j` is acyclic. -/
def boundedFlatPerfectSupported : ObjectProperty (CochainComplex X.Modules ℤ) := fun K =>
  boundedFlatPerfect X K ∧ ((restrict j).obj K).Acyclic

instance boundedFlatPerfectSupported_containsZero : (boundedFlatPerfectSupported j).ContainsZero
  where
  exists_zero := ⟨0, isZero_zero _, boundedFlatPerfect_of_isZero (isZero_zero _),
    HomologicalComplex.acyclic_of_isZero _ ((restrict j).map_isZero (isZero_zero _))⟩

instance boundedFlatPerfectSupported_closedUnderIsomorphisms :
    (boundedFlatPerfectSupported j).IsClosedUnderIsomorphisms where
  of_iso e hK := ⟨boundedFlatPerfect_of_iso e hK.1,
    fun n => (hK.2 n).of_iso ((restrict j).mapIso e)⟩

instance boundedFlatPerfectSupported_extensionClosed :
    (abelianExactStructure (CochainComplex X.Modules ℤ)).IsExtensionClosed
      (boundedFlatPerfectSupported j) where
  prop_middle {_S} hS h₁ h₃ :=
    ⟨boundedFlatPerfect_of_shortExact hS h₁.1 h₃.1,
      (hS.map_of_exact (restrict j)).acyclic_X₂ h₁.2 h₃.2⟩

instance boundedFlatPerfectSupported_closedUnderFiniteProducts :
    (boundedFlatPerfectSupported j).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex X.Modules ℤ)).extensionClosed_finiteProducts
    (boundedFlatPerfectSupported j)

theorem boundedFlatPerfectSupported_shift {K : CochainComplex X.Modules ℤ}
    (hK : boundedFlatPerfectSupported j K) (n : ℤ) :
    boundedFlatPerfectSupported j ((shiftFunctor (CochainComplex X.Modules ℤ) n).obj K) := by
  refine ⟨boundedFlatPerfect_shift hK.1 n, ?_⟩
  intro i
  have hi : (((restrict j).obj K)⟦n⟧).ExactAt i := by
    rw [exactAt_iff_isZero_homology]
    exact ((exactAt_iff_isZero_homology _ _).mp (hK.2 (n+i))).of_iso
      ((CochainComplex.ShiftSequence.shiftIso U.Modules n i (n+i) rfl).app
        ((restrict j).obj K))
  exact hi.of_iso (((restrict j).commShiftIso n).app K).symm

theorem boundedFlatPerfectSupported_mappingCone {K L : CochainComplex X.Modules ℤ}
    (hK : boundedFlatPerfectSupported j K) (hL : boundedFlatPerfectSupported j L) (f : K ⟶ L) :
    boundedFlatPerfectSupported j (CochainComplex.mappingCone f) := by
  refine ⟨boundedFlatPerfect_mappingCone hK.1 hL.1 f, ?_⟩
  have : QuasiIso ((restrict j).map f) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_exactAt _ n (hK.2 n)).mpr (hL.2 n)
  have hc := CochainComplex.mappingCone_acyclic_of_quasiIso ((restrict j).map f)
  intro n
  exact (hc n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (Scheme.Modules.restrictFunctor j)).symm

/-- The full-subcategory inclusion from supported bounded-flat perfect complexes into supported
locally perfect complexes. -/
def boundedFlatPerfectSupportedInclusion :
    (boundedFlatPerfectSupported j).FullSubcategory ⥤ (perfectSupported j).FullSubcategory :=
  ObjectProperty.ιOfLE (fun _ h => ⟨h.1.1, h.2⟩)

end Quillen.PerfectComplexes

end

end
