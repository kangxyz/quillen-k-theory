import Quillen.Scheme.Regular.AffineResolution
import Quillen.Scheme.VectorBundle.Locality
import Quillen.Scheme.Coherent.Restriction

/-!
# Kernel closure of genuine coherent vector bundles

An ambient short exact sequence of coherent sheaves restricts to an ambient
short exact sequence on each affine chart. Finite projective modules give
kernel closure there; locality of finite local freeness gives kernel closure
on the original scheme. No vector bundle is assumed globally projective in
the sheaf category.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.SchemeSheaf

/-- Kernels of admissible epimorphisms between coherent vector bundles are
actual finite locally free sheaves on any locally noetherian scheme. -/
instance coherentVectorBundle_kernelClosed (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (CoherentScheme.coherentExactStructure X).IsKernelClosed
      (coherentVectorBundle X) where
  prop_kernel {S} hS h₂ h₃ := by
    have : IsFiniteLocallyFree X S.X₂.obj := h₂
    have : IsFiniteLocallyFree X S.X₃.obj := h₃
    let U := X.affineOpenCover
    apply finiteLocallyFree_of_affineCharts S.X₁.obj U.X U.f
      (fun x => ⟨U.idx x, U.covers x⟩)
    intro i
    have : IsLocallyNoetherian (Spec (U.X i)) :=
      isLocallyNoetherian_of_isOpenImmersion (U.f i)
    have : IsNoetherianRing (U.X i) := isLocallyNoetherian_Spec.mp inferInstance
    let F := CoherentScheme.coherentRestriction (U.f i)
    let T := S.map F
    have hT : T.ShortExact := hS.map_of_exact F
    have h₂' : coherentVectorBundle (Spec (U.X i)) T.X₂ :=
      finiteLocallyFree_restrict (U.f i) S.X₂.obj
    have h₃' : coherentVectorBundle (Spec (U.X i)) T.X₃ :=
      finiteLocallyFree_restrict (U.f i) S.X₃.obj
    exact ExactStructure.IsKernelClosed.prop_kernel
      (E := CoherentScheme.coherentExactStructure (Spec (U.X i))) hT h₂' h₃'

end Quillen.SchemeSheaf
