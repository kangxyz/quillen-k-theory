/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.OpenFibration

/-!
# Intrinsic perfect objects in the original derived category

An object of the original ambient derived category is perfect when its
original derived restrictions are locally isomorphic to actual strict
perfect complexes. This is proved equivalent to existence of an original
locally-perfect chain representative. Genuine derived fractions, literal
mapping cones, and integer shifts make this actual full subcategory
triangulated, on every scheme.

The original perfect-complex functor detects precisely actual
quasi-isomorphisms. Open restriction retains the original `derivedRestrict`,
and its comparison with the original `perfectRestrict` is the original
localization factorization. No affine hypothesis or Waldhausen K-equivalence
is assumed or inferred here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open scoped ZeroObject
namespace Quillen.PerfectComplexes
local instance standardPerfectDerivedSheaves (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

instance toDerived_essSurj (X : Scheme.{u}) : (toDerived X).EssSurj :=
  inferInstanceAs (DerivedCategory.Q (C := X.Modules)).EssSurj

/-- Intrinsic local perfectness of an object of the original ambient derived category. -/
def perfectDerivedObjects (X : Scheme.{u}) : ObjectProperty (Derived X) := fun K =>
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ P : StrictPerfect U.toScheme,
    Nonempty ((derivedRestrict U.ι).obj K ≅ (toDerived U.toScheme).obj P.obj)

instance (X : Scheme.{u}) : (perfectDerivedObjects X).IsClosedUnderIsomorphisms where
  of_iso e h x := by
    obtain ⟨U, hx, P, ⟨eP⟩⟩ := h x
    exact ⟨U, hx, P, ⟨(derivedRestrict U.ι).mapIso e.symm ≪≫ eP⟩⟩

/-- Intrinsic derived local perfection agrees with the original chain-level local-perfect predicate. -/
lemma perfectDerivedObjects_toDerived_iff (X : Scheme.{u}) (K : Complex X) :
    perfectDerivedObjects X ((toDerived X).obj K) ↔ locallyPerfect X K := by
  constructor
  · intro h x
    obtain ⟨U, hx, P, ⟨eP⟩⟩ := h x
    exact ⟨U, hx, P, ⟨((derivedRestrictFactors U.ι).app K).symm ≪≫ eP⟩⟩
  · intro h x
    obtain ⟨U, hx, P, ⟨eP⟩⟩ := h x
    exact ⟨U, hx, P, ⟨(derivedRestrictFactors U.ι).app K ≪≫ eP⟩⟩

/-- Every intrinsic perfect derived object has an original locally-perfect chain representative, and conversely. -/
lemma perfectDerivedObjects_iff_exists_representative (X : Scheme.{u}) (K : Derived X) :
    perfectDerivedObjects X K ↔
      ∃ P : Perfect X, Nonempty ((toDerived X).obj P.obj ≅ K) := by
  constructor
  · intro h
    let P := (toDerived X).objPreimage K
    let e := (toDerived X).objObjPreimageIso K
    have hP := (perfectDerivedObjects X).prop_of_iso e.symm h
    exact ⟨⟨P, (perfectDerivedObjects_toDerived_iff X P).mp hP⟩, ⟨e⟩⟩
  · rintro ⟨P, ⟨e⟩⟩
    exact (perfectDerivedObjects X).prop_of_iso e
      ((perfectDerivedObjects_toDerived_iff X P.obj).mpr P.property)

instance (X : Scheme.{u}) : (perfectDerivedObjects X).ContainsZero where
  exists_zero := ⟨(toDerived X).obj 0, (toDerived X).map_isZero (isZero_zero _),
    (perfectDerivedObjects_toDerived_iff X 0).mpr ((locallyPerfect X).prop_zero)⟩

instance (X : Scheme.{u}) : (perfectDerivedObjects X).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    intro K hK
    obtain ⟨P, ⟨eP⟩⟩ := (perfectDerivedObjects_iff_exists_representative X K).mp hK
    apply (perfectDerivedObjects_iff_exists_representative X _).mpr
    exact ⟨⟨P.obj⟦n⟧, locallyPerfect_shift P.property n⟩,
      ⟨((toDerived X).commShiftIso n).app P.obj ≪≫ (shiftFunctor _ n).mapIso eP⟩⟩⟩

instance (X : Scheme.{u}) : (perfectDerivedObjects X).IsTriangulatedClosed₃ :=
  .mk' (by
    intro T hT h₁ h₂
    obtain ⟨P, ⟨eP⟩⟩ := (perfectDerivedObjects_iff_exists_representative X _).mp h₁
    obtain ⟨L, ⟨eL⟩⟩ := (perfectDerivedObjects_iff_exists_representative X _).mp h₂
    obtain ⟨M, g, s, hs, he⟩ := toDerived_left_fraction (eP.hom ≫ T.mor₁ ≫ eL.inv)
    have hM : locallyPerfect X M := (locallyPerfect_iff_of_quasiIso s).mp L.property
    let eM : (toDerived X).obj M ≅ T.obj₂ := (asIso ((toDerived X).map s)).symm ≪≫ eL
    have hc : (toDerived X).map g ≫ eM.hom = eP.hom ≫ T.mor₁ := by
      rw [← he]
      simp [eM]
    let e := Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ T
      (mappingConeTriangle_distinguished g) hT eP eM hc)
    exact (perfectDerivedObjects_iff_exists_representative X _).mpr
      ⟨⟨CochainComplex.mappingCone g, locallyPerfect_mappingCone P.property hM g⟩, ⟨e⟩⟩)

instance (X : Scheme.{u}) : (perfectDerivedObjects X).IsTriangulatedClosed₂ :=
  .of_isTriangulatedClosed₃

instance (X : Scheme.{u}) : (perfectDerivedObjects X).IsTriangulated where

/-- The actual full triangulated subcategory of intrinsic perfect objects. -/
abbrev PerfectDerived (X : Scheme.{u}) := (perfectDerivedObjects X).FullSubcategory

/-- The original perfect-complex localization, corestricted to its intrinsic perfect target. -/
def perfectToDerived (X : Scheme.{u}) : Perfect X ⥤ PerfectDerived X :=
  (perfectDerivedObjects X).lift ((locallyPerfect X).ι ⋙ toDerived X)
    (fun P => (perfectDerivedObjects_toDerived_iff X P.obj).mpr P.property)

/-- The original perfect localization inverts exactly the original quasi-isomorphisms. -/
lemma perfectToDerived_isIso_map_iff {X : Scheme.{u}} {K L : Perfect X} (f : K ⟶ L) :
    IsIso ((perfectToDerived X).map f) ↔ QuasiIso f.hom := by
  rw [← isIso_iff_of_reflects_iso ((perfectToDerived X).map f) (perfectDerivedObjects X).ι]
  exact DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules f.hom

/-- Original geometric derived restriction preserves intrinsic perfection. -/
lemma perfectDerivedObjects_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K : Derived X} (hK : perfectDerivedObjects X K) :
    perfectDerivedObjects U ((derivedRestrict j).obj K) := by
  obtain ⟨P, ⟨eP⟩⟩ := (perfectDerivedObjects_iff_exists_representative X K).mp hK
  apply (perfectDerivedObjects_iff_exists_representative U _).mpr
  exact ⟨⟨(restrict j).obj P.obj, locallyPerfect_restrict j P.property⟩,
    ⟨((derivedRestrictFactors j).app P.obj).symm ≪≫ (derivedRestrict j).mapIso eP⟩⟩

/-- Open restriction on actual perfect derived objects, retaining the original derived functor. -/
def perfectDerivedRestrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PerfectDerived X ⥤ PerfectDerived U :=
  (perfectDerivedObjects U).lift ((perfectDerivedObjects X).ι ⋙ derivedRestrict j)
    (fun K => perfectDerivedObjects_restrict j K.property)

/-- Forgetting membership proofs recovers the original derived restriction map. -/
@[simp]
lemma perfectDerivedRestrict_map {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K L : PerfectDerived X} (f : K ⟶ L) :
    ((perfectDerivedRestrict j).map f).hom = (derivedRestrict j).map f.hom := rfl

/-- The original perfect restriction and original derived restriction commute through the specified localization factorization. -/
def perfectDerivedRestrictFactors {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    perfectToDerived X ⋙ perfectDerivedRestrict j ≅ perfectRestrict j ⋙ perfectToDerived U :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _ ((derivedRestrictFactors j).app K.obj))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact (derivedRestrictFactors j).hom.naturality f.hom)

end Quillen.PerfectComplexes
