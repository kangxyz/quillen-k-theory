/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.Homology
import Quillen.Scheme.Coherent.Homology
import Quillen.Scheme.Coherent.Restriction

/-!
# Coherent homology of the original locally perfect complexes

Local strict models give coherent homology on locally noetherian schemes,
without assuming coherent terms or a global representative. Quasi-compactness
adds uniform cohomological bounds. The actual coherent-valued homology functor
inverts quasi-isomorphisms and commutes with the original open restrictions.
Homology is not asserted to be exact; these results alone do not define a
perfect-to-G K-theory map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace Quillen.PerfectComplexes

/-- Actual locally perfect complexes have coherent homology on locally
noetherian schemes, without termwise coherence or a global strict model. -/
theorem locallyPerfect_coherent_homology {X : Scheme.{u}} [IsLocallyNoetherian X]
    {K : Complex X} (hK : locallyPerfect X K) (i : ℤ) :
    CoherentScheme.coherent X (K.homology i) := by
  apply CoherentScheme.coherent_of_openNeighborhoods
  intro x
  obtain ⟨U, hx, P, ⟨e⟩⟩ := hK x
  let : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have hP : CoherentScheme.coherent U.toScheme (P.obj.homology i) :=
    CoherentScheme.coherent_homology P.obj (fun n => by
      let := P.property.2 n
      exact CoherentScheme.coherent_of_finitePresentation (P.obj.X n)) i
  exact ⟨U, hx, (CoherentScheme.coherent U.toScheme).prop_of_iso
    ((homologyIsoOfDerivedIso e i).symm ≪≫ restrictHomologyIso U.ι K i) hP⟩

/-- The original actual homology functor on perfect objects takes values in
coherent sheaves. It is not asserted to be an exact functor. -/
def coherentHomology (X : Scheme.{u}) [IsLocallyNoetherian X] (i : ℤ) :
    Perfect X ⥤ CoherentScheme.Coherent X :=
  (CoherentScheme.coherent X).lift
    ((locallyPerfect X).ι ⋙ HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) i)
    (fun K => locallyPerfect_coherent_homology K.property i)

/-- The coherent-valued homology has literally the original homology sheaf. -/
theorem coherentHomology_obj (X : Scheme.{u}) [IsLocallyNoetherian X]
    (i : ℤ) (K : Perfect X) : ((coherentHomology X i).obj K).obj = K.obj.homology i := rfl

/-- Quasi-isomorphisms induce genuine isomorphisms of coherent homology. -/
theorem coherentHomology_map_isIso {X : Scheme.{u}} [IsLocallyNoetherian X]
    (i : ℤ) {K L : Perfect X} (f : K ⟶ L) [QuasiIso f.hom] :
    IsIso ((coherentHomology X i).map f) := by
  let : IsIso ((CoherentScheme.coherentToSheaves X).map ((coherentHomology X i).map f)) := by
    change IsIso (HomologicalComplex.homologyMap f.hom i)
    infer_instance
  exact isIso_of_reflects_iso _ (CoherentScheme.coherentToSheaves X)

/-- Coherent-valued homology commutes naturally with the original perfect
open restriction and the original coherent open restriction. -/
def coherentHomologyRestrictIso {U X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (i : ℤ) :
    perfectRestrict j ⋙ coherentHomology U i ≅
      coherentHomology X i ⋙ CoherentScheme.coherentRestriction j :=
  NatIso.ofComponents
    (fun K => (CoherentScheme.coherent U).isoMk (restrictHomologyIso j K.obj i))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor X.Modules (ComplexShape.up ℤ) i).map f.hom)
        (Scheme.Modules.restrictFunctor j))

/-- Quasi-compactness supplies genuine finite homological support, while
locally noetherianity supplies coherence in every degree. -/
theorem locallyPerfect_bounded_coherent_homology {X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] {K : Complex X} (hK : locallyPerfect X K) :
    (∀ i : ℤ, CoherentScheme.coherent X (K.homology i)) ∧
      ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.homology i) :=
  ⟨locallyPerfect_coherent_homology hK, locallyPerfect_homology_bounded hK⟩

end Quillen.PerfectComplexes
