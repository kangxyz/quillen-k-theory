/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenFibration
public import Quillen.AlgebraicGeometry.PerfectComplexes.Homology

/-! # Actual supported cocones and shifts

The genuine derived mapping-cocone triangle and exact original restriction
prove that its first projection is locally weak when its target is zero there.
Perfection, quasicoherent homology and derived support retain their actual
complexes under the displayed cone and shift operations.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
local instance supportedRoofDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- The literal mapping cocone of two locally perfect complexes remains locally perfect. -/
lemma locallyPerfect_mappingCocone {X : Scheme.{u}} {A C : Complex X}
    (hA : locallyPerfect X A) (hC : locallyPerfect X C) (i : A ⟶ C) :
    locallyPerfect X (CochainComplex.mappingCocone i) :=
  locallyPerfect_shift (locallyPerfect_mappingCone hA hC i) (-1)

/-- The original cocone projection is weak on an open where its target is derived-zero. -/
lemma quasiIso_restrict_mappingCocone_fst_of_isZero {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] {A C : Complex X} (i : A ⟶ C)
    (hC : IsZero ((toDerived U).obj ((restrict j).obj C))) :
    QuasiIso ((restrict j).map (CochainComplex.mappingCocone.fst i)) := by
  let T := (toDerived X).mapTriangle.obj (CochainComplex.mappingCocone.triangle i)
  let F := exactDerivedRestrict j
  have hT : T ∈ distTriang (Derived X) := DerivedCategory.mappingCocone_triangle_distinguished i
  have hz : IsZero ((F.mapTriangle.obj T).obj₃) :=
    hC.of_iso ((exactDerivedRestrictFactors j).app C)
  have hi := (Triangle.isZero₃_iff_isIso₁ (F.mapTriangle.obj T) (F.map_distinguished T hT)).mp hz
  change IsIso (F.map ((toDerived X).map (CochainComplex.mappingCocone.fst i))) at hi
  let e := exactDerivedRestrictFactors j
  have hh := e.hom.naturality (CochainComplex.mappingCocone.fst i)
  have : IsIso (((toDerived X ⋙ F).map (CochainComplex.mappingCocone.fst i)) ≫ e.hom.app A) := by
    change IsIso (F.map ((toDerived X).map _) ≫ _)
    infer_instance
  rw [hh] at this
  have : IsIso ((restrict j ⋙ toDerived U).map (CochainComplex.mappingCocone.fst i)) :=
    IsIso.of_isIso_comp_left (e.hom.app _) _
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso U.Modules _).mp this

/-- Original quasicoherent homology is preserved by every actual integer shift. -/
lemma quasicoherent_homology_shift {X : Scheme.{u}} (K : Complex X)
    (hK : ∀ n, (K.homology n).IsQuasicoherent) (a n : ℤ) :
    ((K⟦a⟧).homology n).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((CochainComplex.ShiftSequence.shiftIso X.Modules a n (a+n) rfl).app K).symm (hK (a+n))

/-- Actual derived support survives original integer shifts. -/
lemma isZero_restrict_shift_of_isZero {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : Complex X)
    (hK : IsZero ((toDerived U).obj ((restrict j).obj K))) (a : ℤ) :
    IsZero ((toDerived U).obj ((restrict j).obj (K⟦a⟧))) := by
  exact ((shiftFunctor (Derived U) a).map_isZero hK).of_iso
    ((toDerived U).mapIso (((restrict j).commShiftIso a).app K) ≪≫
      ((toDerived U).commShiftIso a).app ((restrict j).obj K))

end Quillen.PerfectComplexes
