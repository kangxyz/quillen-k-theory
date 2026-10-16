/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.LowerModels
public import Quillen.Aglib.AlgebraicGeometry.Modules.Restriction.UnitSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteGenerators

/-!
# Finite-free lifts over an affine scheme

The given epimorphism of quasicoherent sheaves onto a target with finite global sections admits the original finite-free source map surjective after composition.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
namespace Quillen.PerfectComplexes.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
/-- A sheaf epimorphism onto a finite quasicoherent affine target admits
finitely many actual unit-sheaf lifts jointly generating that target. -/
theorem exists_finite_free_lift_of_affine_epi (R : CommRingCat.{u})
    {M H : (Spec R).Modules} [M.IsQuasicoherent] [H.IsQuasicoherent]
    (q : M ⟶ H) [Epi q] [Module.Finite R (moduleSpecΓFunctor.obj H)] :
    ∃ I : Type u, Finite I ∧
      ∃ l : SheafOfModules.free (R := (Spec R).ringCatSheaf) I ⟶ M, Epi (l ≫ q) := by
  obtain ⟨G, hG⟩ :=
    AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineFiniteSheaf_exists_generatingSections R
    (M := H) ⟨inferInstance, inferInstance⟩
  have : G.IsFiniteType := hG
  have : Epi (moduleSpecΓFunctor.map q) := epi_globalSections_of_quasicoherent R q
  have hsurj := (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map q)).mp inferInstance
  have hlift (i : G.I) : ∃ t : Γ(M, ⊤),
      Scheme.Modules.Hom.app q ⊤ t = Scheme.Modules.Hom.app
        (SheafOfModules.ιFree i ≫ G.π) ⊤ (1 : Γ(Spec R, ⊤)) := by
    exact hsurj (Scheme.Modules.Hom.app
      (SheafOfModules.ιFree i ≫ G.π) ⊤ (1 : Γ(Spec R, ⊤)))
  choose t ht using hlift
  let u (i : G.I) := unitMapOfTopSection M (t i)
  have hu (i : G.I) : u i ≫ q = SheafOfModules.ιFree i ≫ G.π := by
    apply unit_hom_ext_top
    change Scheme.Modules.Hom.app q ⊤
      (Scheme.Modules.Hom.app (unitMapOfTopSection M (t i)) ⊤ (1 : Γ(Spec R, ⊤))) = _
    have hx : Scheme.Modules.Hom.app (unitMapOfTopSection M (t i)) ⊤
        (1 : Γ(Spec R, ⊤)) = t i := by simp [unitMapOfTopSection_app]
    rw [hx]
    exact ht i
  let l : SheafOfModules.free (R := (Spec R).ringCatSheaf) G.I ⟶ M := Sigma.desc u
  have he : l ≫ q = G.π := by
    apply Sigma.hom_ext
    intro i
    simpa [l, SheafOfModules.ιFree] using hu i
  exact ⟨G.I, inferInstance, l, by rw [he]; exact G.epi⟩


end Quillen.PerfectComplexes.ProjectiveLine
end
end
