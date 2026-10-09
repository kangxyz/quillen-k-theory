import Quillen.Scheme.Coherent.Basic
import Quillen.Scheme.Coherent.Affine.Presentation

/-!
# Actual finite local presentations of global coherent sheaves

The affine-chart coherent condition produces finite presentations on the
actual cover by affine opens. These are transported to the over-site by the
proved scheme sheaf equivalences. Thus the global category consists of actual
finitely presented sheaves, and in particular actual quasicoherent sheaves.
The converse comparison is not asserted here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Quillen.CoherentScheme

/-- A finite module over a noetherian ring has an actual finite global
presentation after applying tilde. -/
theorem exists_finite_presentation_tilde (R : CommRingCat.{u}) [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ P : (tilde M).Presentation, P.IsFinite := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  let f : ((s : Set M) →₀ R) →ₗ[R] M := Finsupp.linearCombination R (fun x : (s : Set M) => x.1)
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (LinearMap.ker f)
  let P := presentationTilde M (s : Set M) hs (t : Set ((s : Set M) →₀ R)) ht
  exact ⟨P, { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set M))⟩
              isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set ((s : Set M) →₀ R)))⟩ }⟩

/-- The actual affine finite-quasicoherent property supplies a finite global
presentation of the given sheaf. -/
theorem affineFiniteSheaf_exists_presentation (R : CommRingCat.{u}) [IsNoetherianRing R]
    {M : (Spec R).Modules} (hM : affineFiniteSheaf R M) :
    ∃ P : M.Presentation, P.IsFinite := by
  have : M.IsQuasicoherent := hM.1
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := hM.2
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  obtain ⟨P, hP⟩ := exists_finite_presentation_tilde R (moduleSpecΓFunctor.obj M)
  exact ⟨P.ofIsIso M.fromTildeΓ, inferInstance⟩

/-- Transfer a presentation on an affine chart to the actual over-site of
that affine open in the original scheme. -/
def affinePresentationToOver {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (P : (M.restrict U.2.fromSpec).Presentation) : (M.over U.1).Presentation := by
  let e := U.2.isoSpec
  let P' := Scheme.Modules.presentationRestrict e.hom P
  let i : (M.restrict U.2.fromSpec).restrict e.hom ≅ M.restrict U.1.ι :=
    ((Scheme.Modules.restrictFunctorComp e.hom U.2.fromSpec).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr U.2.isoSpec_hom_fromSpec).app M
  let Q := P'.ofIsIso i.hom
  let E := Scheme.Modules.overEquiv U.1
  let e' : E.inverse.obj (M.restrict U.1.ι) ≅ M.over U.1 :=
    (E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U.1).app M)).symm ≪≫
      (E.unitIso.app (M.over U.1)).symm
  exact (Q.map E.inverse
    (U.1.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).ofIsIso e'.hom

instance affinePresentationToOver_isFinite {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (P : (M.restrict U.2.fromSpec).Presentation) [P.IsFinite] :
    (affinePresentationToOver M U P).IsFinite := by
  dsimp [affinePresentationToOver, Scheme.Modules.presentationRestrict]
  infer_instance

/-- Every globally coherent object has a genuine finite local presentation
in the upstream sheaf-theoretic sense. -/
theorem coherent_finitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M : X.Modules} (hM : coherent X M) : M.IsFinitePresentation := by
  classical
  have h (U : X.affineOpens) : ∃ P : (M.restrict U.2.fromSpec).Presentation, P.IsFinite := by
    let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    exact affineFiniteSheaf_exists_presentation Γ(X, U.1) (hM _ U.2.fromSpec)
  choose P hP using h
  let q : M.QuasicoherentData :=
    { I := X.affineOpens
      X := fun U => U.1
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover]
        exact iSup_affineOpens_eq_top X
      presentation U := affinePresentationToOver M U (P U) }
  refine SheafOfModules.IsFinitePresentation.mk (M := M) ⟨q, ?_⟩
  constructor
  intro U
  have := hP U
  exact affinePresentationToOver_isFinite M U (P U)

instance coherent_obj_finitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : Coherent X) : M.obj.IsFinitePresentation := coherent_finitePresentation M.property

instance coherent_obj_quasicoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : Coherent X) : M.obj.IsQuasicoherent := by
  have := coherent_obj_finitePresentation M
  infer_instance

/-- The actual inclusion of global coherent sheaves into finitely presented
sheaves. The proof above supplies its required object property. -/
def coherentToFinitePresentation (X : Scheme.{u}) [IsLocallyNoetherian X] :
    Coherent X ⥤ SchemeSheaf.FinitePresentation X :=
  (SchemeSheaf.finitePresentation X).lift (coherentToSheaves X)
    (fun M => coherent_finitePresentation M.property)

end Quillen.CoherentScheme
