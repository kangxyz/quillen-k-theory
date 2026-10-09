import Quillen.Scheme.Coherent.Localization.GluingSubobjects
import Quillen.Scheme.Coherent.Localization.GluingLocality
import Quillen.Scheme.Coherent.Restriction

/-!
# Binary gluing of coherent subsheaves

The module-sheaf kernel construction supplies the global object. Coherence
is then proved by actual local finite presentations on the covering pair.
In particular the ambient sheaf need not be coherent or even quasicoherent.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Quillen.CoherentScheme

/-- Coherence along an open immersion is equivalent to coherence on its
actual open range. -/
theorem coherent_restrict_opensRange
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (h : coherent U (M.restrict j)) :
    coherent j.opensRange.toScheme (M.restrict j.opensRange.ι) := by
  let e : (M.restrict j).restrict j.isoOpensRange.inv ≅
      M.restrict j.opensRange.ι :=
    ((Scheme.Modules.restrictFunctorComp j.isoOpensRange.inv j).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr j.isoOpensRange_inv_comp).app M
  exact (coherent j.opensRange.toScheme).prop_of_iso e
    (coherent_restrict j.isoOpensRange.inv h)

/-- Coherence is local for a binary covering family of arbitrary open
immersions, not only literal inclusions of opens. -/
theorem coherent_of_binary_openImmersionCover
    {U V X : Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) (a : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion a]
    (hcover : j.opensRange ⊔ a.opensRange = ⊤) (M : X.Modules)
    (hU : coherent U (M.restrict j)) (hV : coherent V (M.restrict a)) :
    coherent X M :=
  coherent_of_binary_openCover M j.opensRange a.opensRange hcover
    (coherent_restrict_opensRange j M hU) (coherent_restrict_opensRange a M hV)

/-- Coherent subsheaves glue along a binary covering family of arbitrary
open immersions. This version applies directly to the two maps into a union. -/
theorem exists_coherent_glued_subobject_of_openImmersionCover
    {U V X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    (j : U ⟶ X) (a : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion a]
    (hcover : j.opensRange ⊔ a.opensRange = ⊤) (M : X.Modules)
    (A : Coherent U) (B : Coherent V)
    (i : A.obj ⟶ M.restrict j) (k : B.obj ⟶ M.restrict a)
    [Mono i] [Mono k]
    (e : A.obj.restrict (pullback.fst j a) ≅ B.obj.restrict (pullback.snd j a))
    (he : (Scheme.Modules.restrictFunctor (pullback.fst j a)).map i ≫
        (overlapRestrictIso j a).hom.app M =
      e.hom ≫ (Scheme.Modules.restrictFunctor (pullback.snd j a)).map k) :
    ∃ (N : Coherent X) (s : N.obj ⟶ M), Mono s ∧
      ∃ (eU : N.obj.restrict j ≅ A.obj) (eV : N.obj.restrict a ≅ B.obj),
        (Scheme.Modules.restrictFunctor j).map s = eU.hom ≫ i ∧
        (Scheme.Modules.restrictFunctor a).map s = eV.hom ≫ k := by
  obtain ⟨N, s, hs, eU, eV, hU, hV⟩ := exists_glued_subobject j a i k e he
  have hN : coherent X N := coherent_of_binary_openImmersionCover j a hcover N
    ((coherent U).prop_of_iso eU.symm A.property)
    ((coherent V).prop_of_iso eV.symm B.property)
  exact ⟨⟨N, hN⟩, s, hs, eU, eV, hU, hV⟩

/-- Two coherent subobjects of the restrictions of an arbitrary ambient
module sheaf glue whenever their actual overlap subobjects agree. Both
comparison isomorphisms commute with the given inclusions. -/
theorem exists_coherent_glued_subobject
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (W V : X.Opens) (hWV : W ⊔ V = ⊤) (M : X.Modules)
    (A : Coherent W.toScheme) (B : Coherent V.toScheme)
    (i : A.obj ⟶ M.restrict W.ι) (k : B.obj ⟶ M.restrict V.ι)
    [Mono i] [Mono k]
    (e : A.obj.restrict (pullback.fst W.ι V.ι) ≅
      B.obj.restrict (pullback.snd W.ι V.ι))
    (he : (Scheme.Modules.restrictFunctor (pullback.fst W.ι V.ι)).map i ≫
        (overlapRestrictIso W.ι V.ι).hom.app M =
      e.hom ≫ (Scheme.Modules.restrictFunctor (pullback.snd W.ι V.ι)).map k) :
    ∃ (N : Coherent X) (s : N.obj ⟶ M), Mono s ∧
      ∃ (eW : N.obj.restrict W.ι ≅ A.obj) (eV : N.obj.restrict V.ι ≅ B.obj),
        (Scheme.Modules.restrictFunctor W.ι).map s = eW.hom ≫ i ∧
        (Scheme.Modules.restrictFunctor V.ι).map s = eV.hom ≫ k := by
  obtain ⟨N, s, hs, eW, eV, hW, hV⟩ := exists_glued_subobject W.ι V.ι i k e he
  have hN : coherent X N := coherent_of_binary_openCover N W V hWV
    ((coherent W.toScheme).prop_of_iso eW.symm A.property)
    ((coherent V.toScheme).prop_of_iso eV.symm B.property)
  exact ⟨⟨N, hN⟩, s, hs, eW, eV, hW, hV⟩

end Quillen.CoherentScheme
