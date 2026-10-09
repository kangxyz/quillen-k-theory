import Quillen.Scheme.Coherent.Localization.ObjectExtensionInduction
import Quillen.Scheme.Coherent.Localization.AffineEnlargement

/-!
# Coherent extension on noetherian schemes

A finite affine cover extends a coherent open subsheaf inside its actual
quasicoherent ambient sheaf. Applying this to the actual open pushforward
proves essential surjectivity of geometric coherent restriction. All object
extension assertions here are conclusions of the gluing construction, not
additional hypotheses.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Quillen.CoherentScheme

open Scheme.Modules

/-- A quasicoherent sheaf coherent on an open of a noetherian scheme has an
actual coherent subsheaf whose restriction to that open is unchanged. -/
theorem exists_coherent_subsheaf_restrict_isIso_noetherian
    {X : Scheme.{u}} [IsNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent]
    (W : X.Opens) (hW : coherent W.toScheme (M.restrict W.ι)) :
    ∃ (N : Coherent X) (s : N.obj ⟶ M), Mono s ∧
      IsIso ((restrictFunctor W.ι).map s) :=
  coherent_subobject_extension_of_affine_enlargement
    (fun N _ W hW R _ a _ => coherent_affine_enlargement N W hW R a) M W hW

/-- A coherent open subsheaf extends inside any actual quasicoherent
ambient sheaf on a noetherian scheme. The restriction isomorphism commutes
with the given inclusion. -/
theorem coherent_subobject_extension_noetherian
    {U X : Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) [M.IsQuasicoherent]
    (A : Coherent U) (i : A.obj ⟶ M.restrict j) [Mono i] :
    ∃ (B : Coherent X) (b : B.obj ⟶ M), Mono b ∧
      ∃ (e : B.obj.restrict j ≅ A.obj),
        (restrictFunctor j).map b = e.hom ≫ i := by
  obtain ⟨K, s, hK, hs, e, he⟩ := quasicoherent_subobject_preimage j M A i
  have : K.IsQuasicoherent := hK
  have : Mono s := hs
  have hKj : coherent U (K.restrict j) := (coherent U).prop_of_iso e.symm A.property
  obtain ⟨B, t, ht, htW⟩ := exists_coherent_subsheaf_restrict_isIso_noetherian
    K j.opensRange (coherent_restrict_opensRange j K hKj)
  have : Mono t := ht
  have : IsIso ((restrictFunctor j.opensRange.ι).map t) := htW
  have : IsIso ((restrictFunctor j).map t) := isIso_restrict_map_of_opensRange j t
  let e' : B.obj.restrict j ≅ A.obj := asIso ((restrictFunctor j).map t) ≪≫ e
  refine ⟨B, t ≫ s, inferInstance, e', ?_⟩
  rw [Functor.map_comp, he]
  rfl

/-- Every coherent sheaf on an open subscheme of a noetherian scheme is
the actual restriction of a coherent sheaf on that scheme. -/
theorem coherent_extension
    {U X : Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (A : Coherent U) :
    ∃ B : Coherent X, Nonempty ((coherentRestriction j).obj B ≅ A) := by
  let M := (pushforward j).obj A.obj
  have : M.IsQuasicoherent := quasicoherent_pushforward_open_of_locallyNoetherian j A.obj
  let e : M.restrict j ≅ A.obj := (restrictFunctorAdjCounitIso j).app A.obj
  obtain ⟨B, b, hb, eB, hB⟩ := coherent_subobject_extension_noetherian j M A e.inv
  exact ⟨B, ⟨(coherent U).fullyFaithfulι.preimageIso eB⟩⟩

/-- Actual coherent restriction along every open immersion into a
noetherian scheme is essentially surjective. -/
instance coherentRestriction_essSurj
    {U X : Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] : (coherentRestriction j).EssSurj where
  mem_essImage A := coherent_extension j A

end Quillen.CoherentScheme
