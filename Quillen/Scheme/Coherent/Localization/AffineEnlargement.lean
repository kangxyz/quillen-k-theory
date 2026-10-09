import Quillen.Scheme.Coherent.Localization.AffineExtension
import Quillen.Scheme.Coherent.Localization.Gluing
import Quillen.Scheme.Coherent.Localization.GluingQuasicoherent

/-!
# Enlarging the coherent locus by one affine chart

These are the geometric induction steps for finite affine-cover extension.
The ambient quasicoherent sheaf remains on the original scheme throughout.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Quillen.CoherentScheme

/-- A sheaf coherent on two opens is coherent on their union, with the
actual restriction-composition identifications. -/
theorem coherent_restrict_sup
    {X : Scheme.{u}} [IsLocallyNoetherian X] (M : X.Modules) (W V : X.Opens)
    (hW : coherent W.toScheme (M.restrict W.ι))
    (hV : coherent V.toScheme (M.restrict V.ι)) :
    coherent (W ⊔ V).toScheme (M.restrict (W ⊔ V).ι) := by
  let T : X.Opens := W ⊔ V
  let j : W.toScheme ⟶ T.toScheme := X.homOfLE (show W ≤ T from le_sup_left)
  let a : V.toScheme ⟶ T.toScheme := X.homOfLE (show V ≤ T from le_sup_right)
  have hc : j.opensRange ⊔ a.opensRange = ⊤ := by
    dsimp [j, a]
    rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE,
      ← Scheme.Hom.preimage_sup]
    exact T.ι_preimage_self
  let eW : (M.restrict T.ι).restrict j ≅ M.restrict W.ι :=
    ((Scheme.Modules.restrictFunctorComp j T.ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι _)).app M
  let eV : (M.restrict T.ι).restrict a ≅ M.restrict V.ι :=
    ((Scheme.Modules.restrictFunctorComp a T.ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι _)).app M
  exact coherent_of_binary_openImmersionCover j a hc (M.restrict T.ι)
    ((coherent W.toScheme).prop_of_iso eW.symm hW)
    ((coherent V.toScheme).prop_of_iso eV.symm hV)

/-- A global quasicoherent sheaf coherent on `W` has a quasicoherent
subsheaf equal to it on `W` and coherent on the union of `W` with one affine
chart. This is the actual finite-cover induction step. -/
theorem coherent_affine_enlargement
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (N : X.Modules) [N.IsQuasicoherent] (W : X.Opens)
    (hW : coherent W.toScheme (N.restrict W.ι))
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (a : Spec R ⟶ X) [IsOpenImmersion a] :
    ∃ (N' : X.Modules) (s : N' ⟶ N), N'.IsQuasicoherent ∧ Mono s ∧
      IsIso ((Scheme.Modules.restrictFunctor W.ι).map s) ∧
      coherent (W ⊔ a.opensRange).toScheme (N'.restrict (W ⊔ a.opensRange).ι) := by
  let p := pullback.fst W.ι a
  let q := pullback.snd W.ι a
  let A : Coherent W.toScheme := ⟨N.restrict W.ι, hW⟩
  let Ap : Coherent (pullback W.ι a) := (coherentRestriction p).obj A
  let E := overlapRestrictIso W.ι a
  let i : Ap.obj ⟶ (N.restrict a).restrict q := (E.app N).hom
  have : Mono i := by dsimp only [i]; infer_instance
  obtain ⟨B, b, hb, eB, heB⟩ := coherent_subobject_extension_affine R q (N.restrict a) Ap i
  have : Mono b := hb
  have he : (Scheme.Modules.restrictFunctor p).map (𝟙 (N.restrict W.ι)) ≫
      E.hom.app N = eB.inv ≫ (Scheme.Modules.restrictFunctor q).map b := by
    rw [heB]
    simp [i]
  obtain ⟨N', s, hN', hs, eW, ea, hsW, hsa⟩ :=
    exists_quasicoherent_glued_subobject W.ι a (𝟙 (N.restrict W.ι)) b eB.symm he
  have hN'W : coherent W.toScheme (N'.restrict W.ι) :=
    (coherent W.toScheme).prop_of_iso eW.symm hW
  have hN'a : coherent (Spec R) (N'.restrict a) :=
    (coherent (Spec R)).prop_of_iso ea.symm B.property
  refine ⟨N', s, hN', hs, ?_, ?_⟩
  · rw [hsW, Category.comp_id]
    infer_instance
  · exact coherent_restrict_sup N' W a.opensRange hN'W
      (coherent_restrict_opensRange a N' hN'a)

end Quillen.CoherentScheme
