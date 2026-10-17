/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure
public import Aglib.AlgebraicGeometry.Modules.Complex.Homology
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
/-! # Actual supported cocones and shifts

The genuine derived mapping-cocone triangle and exact original restriction
prove that its first projection is locally weak when its target is zero there.
Perfection, quasicoherent homology and derived support retain their actual
complexes under the displayed cone and shift operations.
-/
@[expose] public section

attribute [local instance] AlgebraicGeometry.Scheme.Modules.Complex.restrictCommShift

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes
/-- The standard derived model used for the supported cocone comparisons. -/
local instance supportedRoofDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- The literal mapping cocone of two locally perfect complexes remains locally perfect. -/
lemma locallyPerfect_mappingCocone {X : Scheme.{u}} {A C : CochainComplex X.Modules ℤ}
    (hA : locallyPerfect X A) (hC : locallyPerfect X C) (i : A ⟶ C) :
    locallyPerfect X (CochainComplex.mappingCocone i) :=
  locallyPerfect_shift (locallyPerfect_mappingCone hA hC i) (-1)

/-- The original cocone projection is weak on an open where its target is derived-zero. -/
lemma quasiIso_restrict_mappingCocone_fst_of_isZero {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] {A C : CochainComplex X.Modules ℤ} (i : A ⟶ C)
    (hC : IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj C))) :
    QuasiIso ((restrict j).map (CochainComplex.mappingCocone.fst i)) := by
  let T := (DerivedCategory.Q (C := X.Modules)).mapTriangle.obj
    (CochainComplex.mappingCocone.triangle i)
  let F := Scheme.Modules.derivedRestrict j
  have hT : T ∈ distTriang (DerivedCategory X.Modules)
    := DerivedCategory.mappingCocone_triangle_distinguished i
  have hz : IsZero ((F.mapTriangle.obj T).obj₃) :=
    hC.of_iso ((Scheme.Modules.derivedRestrictFactors j).app C)
  have hi := (Triangle.isZero₃_iff_isIso₁ (F.mapTriangle.obj T) (F.map_distinguished T hT)).mp hz
  change IsIso (F.map ((DerivedCategory.Q (C := X.Modules)).map
    (CochainComplex.mappingCocone.fst i))) at hi
  let e := Scheme.Modules.derivedRestrictFactors j
  have hh := e.hom.naturality (CochainComplex.mappingCocone.fst i)
  have : IsIso (((DerivedCategory.Q (C := X.Modules) ⋙ F).map (CochainComplex.mappingCocone.fst i))
    ≫ e.hom.app A) := by
    change IsIso (F.map ((DerivedCategory.Q (C := X.Modules)).map _) ≫ _)
    infer_instance
  rw [hh] at this
  have : IsIso ((restrict j ⋙ DerivedCategory.Q (C := U.Modules)).map
    (CochainComplex.mappingCocone.fst i)) :=
    IsIso.of_isIso_comp_left (e.hom.app _) _
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso U.Modules _).mp this

/-- Original quasicoherent homology is preserved by every actual integer shift. -/
lemma quasicoherent_homology_shift {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n, (K.homology n).IsQuasicoherent) (a n : ℤ) :
    ((K⟦a⟧).homology n).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((CochainComplex.ShiftSequence.shiftIso X.Modules a n (a+n) rfl).app K).symm (hK (a+n))

/-- Actual derived support survives original integer shifts. -/
lemma isZero_restrict_shift_of_isZero {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : CochainComplex X.Modules ℤ)
    (hK : IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K))) (a : ℤ) :
    IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj (K⟦a⟧))) := by
  exact ((shiftFunctor (DerivedCategory U.Modules) a).map_isZero hK).of_iso
    ((DerivedCategory.Q (C := U.Modules)).mapIso (((restrict j).commShiftIso a).app K) ≪≫
      ((DerivedCategory.Q (C := U.Modules)).commShiftIso a).app ((restrict j).obj K))

end Quillen.PerfectComplexes
