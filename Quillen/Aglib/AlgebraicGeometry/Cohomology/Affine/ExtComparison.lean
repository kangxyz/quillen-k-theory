/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.InjectiveResolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# The original affine Ext comparison

`tilde_mapExt_bijective` proves that the existing map
`(tilde.functor R).mapExtAddHom X Y n` is bijective for every pair of modules
and every natural degree, with independent chosen Ext universes. The target
is Ext in the ambient category of all module sheaves on Spec R.

The proof computes actual Ext classes using an ambient injective resolution.
The proved Γ-resolution comparison gives higher Ext vanishing from tilde of
an arbitrary projective module into a quasicoherent sheaf. Dimension shifting
along actual module projective presentations and the original Ext-map
naturality then proves bijectivity for all source modules.

No finite generation, noetherianity, domain, or nontrivial-ring hypothesis
is needed. The associated sheaf of a projective module is not assumed to be
projective in all module sheaves.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w w' u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.AffineDerived

/-- Actual positive Ext classes from tilde of a projective module into a QC
sheaf vanish, without ambient projectivity of that associated sheaf. -/
lemma ext_tilde_projective_eq_zero {R : CommRingCat.{u}}
    [HasExt.{w} (Spec R).Modules] (P : ModuleCat.{u} R) [Projective P]
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ)
    (α : Ext ((tilde.functor R).obj P) M (n + 1)) : α = 0 := by
  let I := injectiveResolution M
  let J := globalSectionsInjectiveResolution (M := M) I
  let adj := tilde.adjunction (R := R)
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective α (n + 2) rfl
  rw [I.extMk_eq_zero_iff _ _ _ _ n rfl]
  have hz : adj.homEquiv P _ f ≫ moduleSpecΓFunctor.map (I.cocomplex.d (n + 1) (n + 2)) = 0 := by
    rw [← adj.homEquiv_naturality_right, hf]
    exact (adj.homAddEquiv P _).map_zero
  let g := (J.exact_succ n).liftFromProjective (adj.homEquiv P _ f) hz
  have hg : g ≫ moduleSpecΓFunctor.map (I.cocomplex.d n (n + 1)) = adj.homEquiv P _ f :=
    (J.exact_succ n).liftFromProjective_comp _ hz
  refine ⟨(adj.homEquiv P _).symm g, ?_⟩
  apply (adj.homEquiv P _).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact hg

lemma ext_tilde_projective_subsingleton {R : CommRingCat.{u}}
    [HasExt.{w} (Spec R).Modules] (P : ModuleCat.{u} R) [Projective P]
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (Ext ((tilde.functor R).obj P) M (n + 1)) :=
  subsingleton_of_forall_eq 0 (ext_tilde_projective_eq_zero P M n)

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀ Ext.mapExactFunctor_extClass

/-- The original exact-functor Ext map is bijective in every degree. -/
lemma tilde_mapExt_bijective {R : CommRingCat.{u}}
    [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{w'} (Spec R).Modules]
    (X Y : ModuleCat.{u} R) (n : ℕ) :
    Function.Bijective ((tilde.functor R).mapExtAddHom X Y n) := by
  let F := tilde.functor R
  induction n generalizing X with
  | zero =>
    change Function.Bijective (Ext.mapExactFunctor F (X := X) (Y := Y) (n := 0))
    rw [Ext.mapExactFunctor₀]
    exact Ext.homEquiv₀.symm.bijective.comp
      ((show Function.Bijective (F.map : (X ⟶ Y) → _) from
        ⟨F.map_injective, F.map_surjective⟩).comp Ext.homEquiv₀.bijective)
  | succ n hn =>
    let P : ProjectivePresentation X := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (kernel.condition P.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel P.f }
    let hsrc : Subsingleton (Ext S.X₂ Y (n + 1)) := Ext.subsingleton_of_projective _ _ n
    let htgt : Subsingleton (Ext (S.map F).X₂ (F.obj Y) (n + 1)) :=
      ext_tilde_projective_subsingleton P.p (F.obj Y) n
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (F.mapExtAddHom S.X₂ Y n) (F.mapExtAddHom S.X₁ Y n) (F.mapExtAddHom S.X₃ Y (n + 1))
      (by
        ext e
        change (Ext.mk₀ (F.map S.f)).comp (e.mapExactFunctor F) (zero_add n) =
          ((Ext.mk₀ S.f).comp e (zero_add n)).mapExactFunctor F
        simp)
      (by
        ext e
        change (hS.map F).extClass.comp (e.mapExactFunctor F) (add_comm 1 n) =
          (hS.extClass.comp e (add_comm 1 n)).mapExactFunctor F
        simp)
      ((ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.contravariant_sequence_exact₁' hS Y n (n + 1) (add_comm 1 n)))
      ((ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.contravariant_sequence_exact₁' (hS.map F) (F.obj Y) n (n + 1) (add_comm 1 n)))
      (hn _).surjective (hn _)
      (fun x₃ ↦ Ext.contravariant_sequence_exact₃ hS _ x₃ (by subsingleton) (add_comm 1 n))
      (fun y₃ ↦ Ext.contravariant_sequence_exact₃ (hS.map F) _ y₃ (by subsingleton) (add_comm 1 n))

end AlgebraicGeometry.Scheme.Modules.AffineDerived
