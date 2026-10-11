/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Category.ModuleCat.Sheaf.TensorExact

/-!
# Consumers of finite-projective coefficient tensor exactness

The tests retain the actual finite-free inclusions, coefficient retraction maps,
and original tensor images of the kernel and cokernel arrows.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits SheafOfModulesOfCommRing

namespace Quillen.Tests.SheafTensorExact

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Every actual free generator is transported through the original unit comparison. -/
theorem original_free_generator (I : Type u) [Finite I] (i : I)
    (M : SheafOfModulesOfCommRing R) :
    ((tensorFunctor R).map (SheafOfModules.ιFree
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) i)).app M ≫
        (tensorFiniteFreeIso R I).hom.app M =
      (tensorLeftUnitIso R).hom.app M ≫
        (Sigma.ι (fun (_ : I) => 𝟭 (SheafOfModulesOfCommRing R)) i).app M :=
  congrArg (fun α => α.app M) (tensorFiniteFreeIso_ι R I i)

/-- Addition in the coefficient arrow is retained by the original tensor map. -/
theorem original_coefficient_add {M N : SheafOfModulesOfCommRing R}
    (f g : M ⟶ N) (P : SheafOfModulesOfCommRing R) :
    ((tensorFunctor R).map (f + g)).app P =
      ((tensorFunctor R).map f).app P + ((tensorFunctor R).map g).app P :=
  congrArg (fun α => α.app P) ((tensorFunctor R).map_add (f := f) (g := g))

/-- Addition in the original sequence arrow is retained by its actual tensor image. -/
theorem original_sequence_add (M : SheafOfModulesOfCommRing R)
    {N P : SheafOfModulesOfCommRing R} (f g : N ⟶ P) :
    (tensorLeftFunctor R M).map (f + g) =
      (tensorLeftFunctor R M).map f + (tensorLeftFunctor R M).map g :=
  (tensorLeftFunctor R M).map_add

/-- The short-complex inclusion is literally the original coefficient inclusion tensor map. -/
theorem original_retract_inclusion (S : ShortComplex (SheafOfModulesOfCommRing R))
    {M N : SheafOfModulesOfCommRing R} (h : Retract M N) :
    (tensorShortComplexRetract R S h).i.τ₂ = ((tensorFunctor R).map h.i).app S.X₂ := rfl

/-- The short-complex retraction is literally the original coefficient retraction tensor map. -/
theorem original_retract_projection (S : ShortComplex (SheafOfModulesOfCommRing R))
    {M N : SheafOfModulesOfCommRing R} (h : Retract M N) :
    (tensorShortComplexRetract R S h).r.τ₂ = ((tensorFunctor R).map h.r).app S.X₂ := rfl

/-- The original two coefficient maps still compose to the identity after tensoring. -/
theorem original_retract_identity (S : ShortComplex (SheafOfModulesOfCommRing R))
    {M N : SheafOfModulesOfCommRing R} (h : Retract M N) :
    ((tensorFunctor R).map h.i).app S.X₂ ≫ ((tensorFunctor R).map h.r).app S.X₂ = 𝟙 _ :=
  congrArg (fun f => f.τ₂) (tensorShortComplexRetract R S h).retract

/-- Tensoring with the actual free sheaf on an empty index type gives a zero object. -/
theorem original_empty_free_tensor (M : SheafOfModulesOfCommRing R) :
    IsZero ((tensorLeftFunctor R (SheafOfModules.free
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      PEmpty.{u + 1})).obj M) := by
  have hz : IsZero (∐ (fun (_ : PEmpty.{u + 1}) => 𝟭 (SheafOfModulesOfCommRing R))) := by
    rw [IsZero.iff_id_eq_zero]
    apply Sigma.hom_ext
    intro i
    exact i.elim
  exact ((evaluation (SheafOfModulesOfCommRing R)
    (SheafOfModulesOfCommRing R)).obj M).map_isZero
      (hz.of_iso (tensorFiniteFreeIso R PEmpty.{u + 1}))

/-- The actual tensor of the quotient arrow has the cokernel universal property. -/
theorem original_tensor_quotient_factorization
    (S : ShortComplex (SheafOfModulesOfCommRing R)) (hS : S.ShortExact)
    {M : SheafOfModulesOfCommRing R} (I : Type u) [Finite I]
    (r : Retract M (SheafOfModules.free
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) I))
    {N : SheafOfModulesOfCommRing R} (f : (tensorLeftFunctor R M).obj S.X₂ ⟶ N)
    (hf : (tensorLeftFunctor R M).map S.f ≫ f = 0) :
    ∃! g : (tensorLeftFunctor R M).obj S.X₃ ⟶ N,
      (tensorLeftFunctor R M).map S.g ≫ g = f := by
  have h := tensor_shortExact_of_retract_finiteFree R S hS I r
  have := h.epi_g
  let hc := h.exact.gIsCokernel
  let c := CokernelCofork.ofπ f hf
  refine ⟨hc.desc c, ?_, ?_⟩
  · exact Cofork.IsColimit.π_desc hc (t := c)
  · intro g hg
    apply Cofork.IsColimit.hom_ext hc
    exact hg.trans (Cofork.IsColimit.π_desc hc (t := c)).symm

/-- The actual tensor of the inclusion arrow has the kernel universal property. -/
theorem original_tensor_kernel_lift
    (S : ShortComplex (SheafOfModulesOfCommRing R)) (hS : S.ShortExact)
    {M : SheafOfModulesOfCommRing R} (I : Type u) [Finite I]
    (r : Retract M (SheafOfModules.free
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) I))
    {N : SheafOfModulesOfCommRing R} (f : N ⟶ (tensorLeftFunctor R M).obj S.X₂)
    (hf : f ≫ (tensorLeftFunctor R M).map S.g = 0) :
    ∃! g : N ⟶ (tensorLeftFunctor R M).obj S.X₁,
      g ≫ (tensorLeftFunctor R M).map S.f = f := by
  have h := tensor_shortExact_of_retract_finiteFree R S hS I r
  have := h.mono_f
  let hc := h.exact.fIsKernel
  let c := KernelFork.ofι f hf
  refine ⟨hc.lift c, ?_, ?_⟩
  · exact Fork.IsLimit.lift_ι hc (t := c)
  · intro g hg
    apply Fork.IsLimit.hom_ext hc
    exact hg.trans (Fork.IsLimit.lift_ι hc (t := c)).symm

end Quillen.Tests.SheafTensorExact
