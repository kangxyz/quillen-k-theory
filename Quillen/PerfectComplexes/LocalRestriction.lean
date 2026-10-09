import Quillen.PerfectComplexes.Local

/-!
# Open restriction of locally perfect complexes

The local quasi-isomorphism localization is functorial under exact geometric
restriction. Pulling a neighborhood back along an open immersion and using
the actual restriction-composition isomorphism proves local perfectness is
preserved, without assuming a global strict representative.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Quillen.PerfectComplexes

variable {V U X : Scheme.{u}}

/-- Equality of open immersions gives equality of their restriction functors. -/
theorem restrict_congr {f g : U ⟶ X} [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) : restrict f = restrict g := by
  subst g
  rfl

/-- Cochain restriction respects composition up to the actual sheaf
restriction isomorphism. -/
def restrictCompIso (f : V ⟶ U) (g : U ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] :
    restrict g ⋙ restrict f ≅ restrict (f ≫ g) :=
  Functor.mapHomologicalComplexCompIso (Scheme.Modules.restrictFunctorComp f g).symm _

variable (j : U ⟶ X) [IsOpenImmersion j]

/-- Open restriction followed by localization inverts quasi-isomorphisms. -/
theorem restrict_toDerived_inverts :
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)).IsInvertedBy
      (restrict j ⋙ toDerived U) := by
  intro K L f hf
  let : QuasiIso f := hf
  exact toDerived_map_isIso ((restrict j).map f)

/-- The actual functor induced on the quasi-isomorphism localization. -/
def derivedRestrict : Derived X ⥤ Derived U :=
  Localization.Construction.lift (restrict j ⋙ toDerived U) (restrict_toDerived_inverts j)

/-- The localization factorization holds for the constructed functor. -/
theorem toDerived_derivedRestrict :
    toDerived X ⋙ derivedRestrict j = restrict j ⋙ toDerived U :=
  Localization.Construction.fac _ _

/-- The localization factorization as a natural isomorphism. -/
def derivedRestrictFactors :
    toDerived X ⋙ derivedRestrict j ≅ restrict j ⋙ toDerived U :=
  eqToIso (toDerived_derivedRestrict j)

/-- Restrict an actual isomorphism in the quasi-isomorphism localization. -/
def restrictDerivedIso {K L : Complex X}
    (e : (toDerived X).obj K ≅ (toDerived X).obj L) :
    (toDerived U).obj ((restrict j).obj K) ≅ (toDerived U).obj ((restrict j).obj L) :=
  ((derivedRestrictFactors j).app K).symm ≪≫
    (derivedRestrict j).mapIso e ≪≫ (derivedRestrictFactors j).app L

/-- Local perfectness depends only on the isomorphism class in the actual
quasi-isomorphism localization. -/
theorem locallyPerfect_iff_of_derivedIso {K L : Complex X}
    (e : (toDerived X).obj K ≅ (toDerived X).obj L) :
    locallyPerfect X K ↔ locallyPerfect X L := by
  constructor
  · intro hK x
    obtain ⟨O, hx, P, ⟨eP⟩⟩ := hK x
    exact ⟨O, hx, P, ⟨(restrictDerivedIso O.ι e).symm ≪≫ eP⟩⟩
  · intro hL x
    obtain ⟨O, hx, P, ⟨eP⟩⟩ := hL x
    exact ⟨O, hx, P, ⟨restrictDerivedIso O.ι e ≪≫ eP⟩⟩

/-- Local perfectness is preserved by open restriction. -/
theorem locallyPerfect_restrict {K : Complex X} (hK : locallyPerfect X K) :
    locallyPerfect U ((restrict j).obj K) := by
  intro x
  obtain ⟨O, hx, P, ⟨eP⟩⟩ := hK (j x)
  let T : U.Opens := j ⁻¹ᵁ O
  let k : T.toScheme ⟶ O.toScheme := j ∣_ O
  have hk : IsOpenImmersion k := inferInstanceAs (IsOpenImmersion (j ∣_ O))
  let e : restrict j ⋙ restrict T.ι ≅ restrict O.ι ⋙ restrict k :=
    restrictCompIso T.ι j ≪≫
      eqToIso (restrict_congr (show T.ι ≫ j = k ≫ O.ι from (morphismRestrict_ι j O).symm)) ≪≫
      (restrictCompIso k O.ι).symm
  refine ⟨T, hx, ⟨(restrict k).obj P.obj, strictPerfect_restrict k P.property⟩, ?_⟩
  exact ⟨(toDerived T.toScheme).mapIso (e.app K) ≪≫ restrictDerivedIso k eP⟩

/-- Actual open restriction on the full category of locally perfect complexes. -/
def perfectRestrict : Perfect X ⥤ Perfect U :=
  (locallyPerfect U).lift ((locallyPerfect X).ι ⋙ restrict j)
    (fun K ↦ locallyPerfect_restrict j K.property)

end Quillen.PerfectComplexes
