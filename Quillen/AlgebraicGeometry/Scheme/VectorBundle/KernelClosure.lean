/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.AffineProjective
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Locality
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.QuasicoherentClosure
public import Quillen.Resolution.Finite

/-! # Ambient kernels and admissible epimorphisms of vector bundles

These statements hold on arbitrary schemes. The proof uses actual affine
quasicoherent equivalences and finite projective modules locally. It never
asserts projectivity of vector bundles in the global sheaf category.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen
open Quillen.SchemeSheaf


open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- A kernel of an ambient epi between affine vector bundles is a vector bundle,
over an arbitrary commutative ring. -/
theorem finiteLocallyFree_kernel_of_shortExact_affine (R : CommRingCat.{u})
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [IsFiniteLocallyFree (Spec R) S.X₂] [IsFiniteLocallyFree (Spec R) S.X₃] :
    IsFiniteLocallyFree (Spec R) S.X₁ := by
  let Q := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  have h₁ : Q S.X₁ := Q.prop_of_isLimit hS.fIsKernel (by
    rintro (_ | _)
    · exact inferInstanceAs S.X₂.IsQuasicoherent
    · exact inferInstanceAs S.X₃.IsQuasicoherent)
  have : S.X₁.IsQuasicoherent := h₁
  let T : ShortComplex (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineQuasicoherent R) :=
    ShortComplex.mk
      (Q.homMk S.f : (⟨S.X₁, h₁⟩ :
        AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineQuasicoherent R) ⟶ ⟨S.X₂,
        inferInstance⟩)
      (Q.homMk S.g : (⟨S.X₂, inferInstance⟩ :
        AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineQuasicoherent R) ⟶
        ⟨S.X₃, inferInstance⟩) (ObjectProperty.hom_ext _ S.zero)
  have hT : T.ShortExact := {
    exact := Functor.reflects_exact_of_faithful Q.ι T hS.exact
    mono_f := Functor.mono_of_mono_map Q.ι hS.mono_f
    epi_g := Functor.epi_of_epi_map Q.ι hS.epi_g }
  let G := (tildeEquiv (R := R)).inverse
  have : G.Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryProducts G
    exact Functor.additive_of_preservesBinaryBiproducts G
  let N := T.map G
  have hN : N.ShortExact := hT.map_of_exact G
  have : Module.Finite R N.X₂ := finite_globalSections_of_finiteLocallyFree R S.X₂
  have : Module.Projective R N.X₂ := projective_globalSections_of_finiteLocallyFree R S.X₂
  have : Module.Projective R N.X₃ := projective_globalSections_of_finiteLocallyFree R S.X₃
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.g.hom (LinearMap.id : N.X₃ →ₗ[R] N.X₃)
    hN.moduleCat_surjective_g
  let sectionMap : N.X₃ ⟶ N.X₂ := { hom' := s }
  let split := ShortComplex.Splitting.ofExactOfSection N hN.exact sectionMap
    (ModuleCat.hom_ext hs) hN.mono_f
  have hsplit : split.r.hom.comp N.f.hom = LinearMap.id :=
    congrArg (fun f : N.X₁ ⟶ N.X₁ ↦ f.hom) split.f_r
  have : Module.Projective R N.X₁ := Module.Projective.of_split N.f.hom split.r.hom hsplit
  have hr : Function.Surjective split.r.hom := fun x ↦
    ⟨N.f.hom x, DFunLike.congr_fun hsplit x⟩
  have : Module.Finite R N.X₁ := Module.Finite.of_surjective split.r.hom hr
  have : IsFiniteLocallyFree (Spec R) (tilde N.X₁) :=
    finiteLocallyFree_tilde_of_finite_projective R N.X₁
  exact @finiteLocallyFree_of_iso _ _ _ (asIso S.X₁.fromTildeΓ) this

/-- Kernels of ambient epimorphisms between vector bundles are vector bundles
on every scheme, with no noetherianity or quasi-compactness hypothesis. -/
theorem finiteLocallyFree_kernel_of_shortExact {X : Scheme.{u}}
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [IsFiniteLocallyFree X S.X₂] [IsFiniteLocallyFree X S.X₃] :
    IsFiniteLocallyFree X S.X₁ := by
  let U := X.affineOpenCover
  apply finiteLocallyFree_of_affineCharts S.X₁ U.X U.f
    (fun x ↦ ⟨U.idx x, U.covers x⟩)
  intro i
  let T := S.map (Scheme.Modules.restrictFunctor (U.f i))
  have hT : T.ShortExact := hS.map_of_exact _
  have : IsFiniteLocallyFree (Spec (U.X i)) T.X₂ := finiteLocallyFree_restrict (U.f i) S.X₂
  have : IsFiniteLocallyFree (Spec (U.X i)) T.X₃ := finiteLocallyFree_restrict (U.f i) S.X₃
  exact finiteLocallyFree_kernel_of_shortExact_affine (U.X i) hT

/-- The actual vector-bundle property is kernel-closed in the ambient
abelian category of all module sheaves on any scheme. -/
instance finiteLocallyFree_kernelClosed (X : Scheme.{u}) :
    (sheafExactStructure X).IsKernelClosed (finiteLocallyFree X) where
  prop_kernel {S} hS h₂ h₃ :=
    @finiteLocallyFree_kernel_of_shortExact X S hS h₂ h₃

/-- The actual categorical kernel of an ambient epi between vector bundles
is finite locally free. -/
theorem finiteLocallyFree_kernel {X : Scheme.{u}} {M N : X.Modules}
    [IsFiniteLocallyFree X M] [IsFiniteLocallyFree X N] (p : M ⟶ N) [Epi p] :
    IsFiniteLocallyFree X (kernel p) := by
  let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hS : S.ShortExact := {
    exact := S.exact_of_f_is_kernel (kernelIsKernel p)
    mono_f := inferInstance
    epi_g := inferInstance }
  exact finiteLocallyFree_kernel_of_shortExact hS

/-- Every morphism of vector bundles which is epi in ambient module sheaves
is an actual admissible epimorphism in their inherited exact structure. -/
theorem vectorBundle_deflation_of_ambient_epi {X : Scheme.{u}}
    {M N : FiniteLocallyFree X} (p : M ⟶ N) [Epi p.hom] :
    (vectorBundleExactStructure X).deflation p := by
  apply (ExactSubcategory.deflation_iff (sheafExactStructure X) (finiteLocallyFree X) p).2
  refine ⟨kernel p.hom, finiteLocallyFree_kernel p.hom, kernel.ι p.hom, kernel.condition p.hom, ?_⟩
  exact {
    exact := (ShortComplex.mk (kernel.ι p.hom) p.hom (kernel.condition p.hom)).exact_of_f_is_kernel
      (kernelIsKernel p.hom)
    mono_f := inferInstance
    epi_g := inferInstance }

end AlgebraicGeometry.Scheme.Modules
