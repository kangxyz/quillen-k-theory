import Quillen.Scheme.Coherent.Localization.GluingSubobjects
import Quillen.Scheme.Coherent.Localization.AffineSectionsGlobal

/-!
# Quasicoherent gluing inside a fixed ambient sheaf

The binary gluing kernel remains quasicoherent even when the two opens do
not cover the target. This permits finite-cover induction while keeping a
global quasicoherent subobject throughout the construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.CoherentScheme
open Scheme.Modules

/-- A binary product of actual quasicoherent sheaves is quasicoherent. -/
theorem quasicoherent_prod {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (M ⨯ N).IsQuasicoherent := by
  apply (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit (prodIsProd M N)
  rintro (_ | _) <;> assumption

/-- Compatible quasicoherent subobjects glue to a global quasicoherent
subobject. The open immersions need not cover the target. Local noetherianity
is used only for quasicoherence of the actual direct images. -/
theorem exists_quasicoherent_glued_subobject
    {U V X : Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) (a : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion a]
    {M : X.Modules} {A : U.Modules} {B : V.Modules}
    [M.IsQuasicoherent] [A.IsQuasicoherent] [B.IsQuasicoherent]
    (i : A ⟶ M.restrict j) (k : B ⟶ M.restrict a) [Mono i] [Mono k]
    (e : A.restrict (pullback.fst j a) ≅ B.restrict (pullback.snd j a))
    (he : (restrictFunctor (pullback.fst j a)).map i ≫
        (overlapRestrictIso j a).hom.app M =
      e.hom ≫ (restrictFunctor (pullback.snd j a)).map k) :
    ∃ (N : X.Modules) (s : N ⟶ M), N.IsQuasicoherent ∧ Mono s ∧
      ∃ (eU : N.restrict j ≅ A) (eV : N.restrict a ≅ B),
        (restrictFunctor j).map s = eU.hom ≫ i ∧
        (restrictFunctor a).map s = eV.hom ≫ k := by
  let f := subobjectObstruction j i
  let g := subobjectObstruction a k
  let l := prod.lift f g
  have : (cokernel i).IsQuasicoherent := quasicoherent_cokernel i
  have : (cokernel k).IsQuasicoherent := quasicoherent_cokernel k
  have : ((pushforward j).obj (cokernel i)).IsQuasicoherent :=
    quasicoherent_pushforward_open_of_locallyNoetherian j (cokernel i)
  have : ((pushforward a).obj (cokernel k)).IsQuasicoherent :=
    quasicoherent_pushforward_open_of_locallyNoetherian a (cokernel k)
  have : (((pushforward j).obj (cokernel i)) ⨯
      ((pushforward a).obj (cokernel k))).IsQuasicoherent := quasicoherent_prod _ _
  have hN : (kernel l).IsQuasicoherent := quasicoherent_kernel l
  obtain ⟨hij, hka⟩ := overlapCompatible_obstruction_zero j a i k e he
  have hU : i ≫ (restrictFunctor j).map l = 0 :=
    map_prod_lift_comp_eq_zero (restrictFunctor j) i f g
      (subobjectObstruction_local_zero j i) hij
  have hV : k ≫ (restrictFunctor a).map l = 0 :=
    map_prod_lift_comp_eq_zero (restrictFunctor a) k f g
      hka (subobjectObstruction_local_zero a k)
  let hUl := isKernelOfComp ((restrictFunctor j).map prod.fst)
    ((restrictFunctor j).map f) (isKernel_subobjectObstruction j i) hU
    (by rw [← Functor.map_comp, prod.lift_fst])
  let hVl := isKernelOfComp ((restrictFunctor a).map prod.snd)
    ((restrictFunctor a).map g) (isKernel_subobjectObstruction a k) hV
    (by rw [← Functor.map_comp, prod.lift_snd])
  let hU₀ := KernelFork.mapIsLimit _ (kernelIsKernel l) (restrictFunctor j)
  let hV₀ := KernelFork.mapIsLimit _ (kernelIsKernel l) (restrictFunctor a)
  let eU := hU₀.conePointUniqueUpToIso hUl
  let eV := hV₀.conePointUniqueUpToIso hVl
  refine ⟨kernel l, kernel.ι l, hN, inferInstance, eU, eV, ?_, ?_⟩
  · exact (hU₀.conePointUniqueUpToIso_hom_comp hUl WalkingParallelPair.zero).symm
  · exact (hV₀.conePointUniqueUpToIso_hom_comp hVl WalkingParallelPair.zero).symm

end Quillen.CoherentScheme
