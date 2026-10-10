/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.AffineSectionsBaseChange
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Gluing actual module-sheaf subobjects

Compatible subobjects on two opens are glued by the kernel of the paired
adjoints of their cokernel maps. The comparison maps are obtained from
kernel universal properties, rather than from assumed descent data.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Quillen.CoherentScheme

open Scheme.Modules

/-- The symmetry-oriented base-change unit uses the same actual pullback,
so both restrictions in the gluing condition refer to one overlap. -/
lemma isIso_openBaseChangeUnit_snd
    {U V X : Scheme.{u}} (j : U ⟶ X) (a : V ⟶ X) [IsOpenImmersion j] :
    IsIso (Functor.whiskerRight (restrictAdjunction (pullback.snd j a)).unit
      (pushforward a ⋙ restrictFunctor j)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  change IsIso (M.presheaf.map (homOfLE
    ((pullback.snd j a).image_preimage_le (a ⁻¹ᵁ (j ''ᵁ W)))).op)
  have heq : (pullback.snd j a) ''ᵁ
      ((pullback.snd j a) ⁻¹ᵁ (a ⁻¹ᵁ (j ''ᵁ W))) = a ⁻¹ᵁ (j ''ᵁ W) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.opensRange_pullbackSnd]
    exact inf_eq_right.mpr (a.preimage_mono (j.image_le_opensRange W))
  have : IsIso (homOfLE ((pullback.snd j a).image_preimage_le
      (a ⁻¹ᵁ (j ''ᵁ W)))) := by
    convert (inferInstance : IsIso (eqToHom heq)) using 1
    exact Subsingleton.elim _ _
  infer_instance

/-- Open base change in the opposite orientation of the same overlap. -/
def openBaseChangeSndIso
    {U V X : Scheme.{u}} (j : U ⟶ X) (a : V ⟶ X) [IsOpenImmersion j] :
    pushforward a ⋙ restrictFunctor j ≅
      restrictFunctor (pullback.snd j a) ⋙ pushforward (pullback.fst j a) := by
  let p := pullback.snd j a
  let q := pullback.fst j a
  letI := isIso_openBaseChangeUnit_snd j a
  exact
    (Functor.leftUnitor _).symm ≪≫
    asIso (Functor.whiskerRight (restrictAdjunction p).unit
      (pushforward a ⋙ restrictFunctor j)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (restrictFunctor p)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pushforwardComp p a) (restrictFunctor j) ≪≫
        Functor.isoWhiskerRight (pushforwardCongr (pullback.condition (f := j) (g := a)).symm)
          (restrictFunctor j) ≪≫
        Functor.isoWhiskerRight (pushforwardComp q j).symm (restrictFunctor j) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (pushforward q) (restrictFunctorAdjCounitIso j) ≪≫
        Functor.rightUnitor _)

/-- The canonical identification of the two restrictions of an ambient
module to the actual overlap. -/
def overlapRestrictIso
    {U V X : Scheme.{u}} (j : U ⟶ X) (a : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion a] :
    restrictFunctor j ⋙ restrictFunctor (pullback.fst j a) ≅
      restrictFunctor a ⋙ restrictFunctor (pullback.snd j a) :=
  (restrictFunctorComp (pullback.fst j a) j).symm ≪≫
    restrictFunctorCongr (pullback.condition (f := j) (g := a)) ≪≫
    restrictFunctorComp (pullback.snd j a) a

/-- Restriction to an open detects zero morphisms whose target comes by
direct image from that open. -/
lemma eq_zero_of_restrict_map_eq_zero
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N)
    (hN : ∃ P : U.Modules, Nonempty (N ≅ (pushforward j).obj P))
    (hf : (restrictFunctor j).map f = 0) : f = 0 := by
  obtain ⟨P, ⟨e⟩⟩ := hN
  have := (restrictAdjunction j).isIso_unit_app_of_iso e
  apply (cancel_mono ((restrictAdjunction j).unit.app N)).mp
  rw [HasZeroMorphisms.zero_comp]
  simpa [hf] using (restrictAdjunction j).unit.naturality f

/-- The global map whose kernel extends a given open subobject. -/
def subobjectObstruction
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} {A : U.Modules} (i : A ⟶ M.restrict j) :
    M ⟶ (pushforward j).obj (cokernel i) :=
  (restrictAdjunction j).homEquiv M (cokernel i) (cokernel.π i)

@[reassoc (attr := simp)]
lemma subobjectObstruction_counit
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} {A : U.Modules} (i : A ⟶ M.restrict j) :
    (restrictFunctor j).map (subobjectObstruction j i) ≫
        (restrictAdjunction j).counit.app (cokernel i) = cokernel.π i := by
  simpa only [subobjectObstruction, Adjunction.homEquiv_counit] using
    ((restrictAdjunction j).homEquiv M (cokernel i)).symm_apply_apply (cokernel.π i)

@[reassoc (attr := simp)]
lemma subobjectObstruction_local_zero
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} {A : U.Modules} (i : A ⟶ M.restrict j) :
    i ≫ (restrictFunctor j).map (subobjectObstruction j i) = 0 := by
  apply (cancel_mono ((restrictAdjunction j).counit.app (cokernel i))).mp
  simp

/-- The given local subobject is the kernel of its restricted global
obstruction map. -/
def subobjectObstructionKernelIsLimit
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} {A : U.Modules} (i : A ⟶ M.restrict j) [Mono i] :
    IsLimit (KernelFork.ofι i (subobjectObstruction_local_zero j i)) := by
  let h := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel i)
  apply KernelFork.IsLimit.ofι'
  intro T k hk
  exact KernelFork.IsLimit.lift' h k (by
    change k ≫ cokernel.π i = 0
    rw [← subobjectObstruction_counit j i, ← Category.assoc, hk]
    simp)

/-- A morphism into a binary product is zero if both components vanish,
and the same holds after applying a product-preserving functor. -/
lemma map_prod_lift_comp_eq_zero
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D)
    {T Y Z : C} [HasBinaryProduct Y Z] [PreservesLimit (pair Y Z) F]
    {A : D} (i : A ⟶ F.obj T) (f : T ⟶ Y) (g : T ⟶ Z)
    (hf : i ≫ F.map f = 0) (hg : i ≫ F.map g = 0) :
    i ≫ F.map (prod.lift f g) = 0 := by
  apply (isLimitOfPreserves F (prodIsProd Y Z)).hom_ext
  rintro (_ | _)
  · change (i ≫ F.map (prod.lift f g)) ≫ F.map prod.fst = 0 ≫ F.map prod.fst
    simp only [Category.assoc, ← F.map_comp, prod.lift_fst, hf, zero_comp]
  · change (i ≫ F.map (prod.lift f g)) ≫ F.map prod.snd = 0 ≫ F.map prod.snd
    simp only [Category.assoc, ← F.map_comp, prod.lift_snd, hg, zero_comp]

/-- Matching overlap subobjects kill each other's global obstruction maps.
This is the geometric compatibility needed by the paired-kernel construction. -/
theorem overlapCompatible_obstruction_zero
    {U V X : Scheme.{u}} (j : U ⟶ X) (a : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion a]
    {M : X.Modules} {A : U.Modules} {B : V.Modules}
    (i : A ⟶ M.restrict j) (k : B ⟶ M.restrict a)
    (e : A.restrict (pullback.fst j a) ≅ B.restrict (pullback.snd j a))
    (he : (restrictFunctor (pullback.fst j a)).map i ≫
        (overlapRestrictIso j a).hom.app M =
      e.hom ≫ (restrictFunctor (pullback.snd j a)).map k) :
    (i ≫ (restrictFunctor j).map (subobjectObstruction a k) = 0) ∧
      (k ≫ (restrictFunctor a).map (subobjectObstruction j i) = 0) := by
  let p := pullback.fst j a
  let q := pullback.snd j a
  let E := overlapRestrictIso j a
  constructor
  · apply eq_zero_of_restrict_map_eq_zero p _
      ⟨(cokernel k).restrict q, ⟨(openBaseChangeSndIso j a).app (cokernel k)⟩⟩
    apply (cancel_mono (E.hom.app ((pushforward a).obj (cokernel k)))).mp
    change ((restrictFunctor p).map i ≫
        (restrictFunctor j ⋙ restrictFunctor p).map (subobjectObstruction a k)) ≫ _ = 0 ≫ _
    rw [Category.assoc, E.hom.naturality, ← Category.assoc, he]
    simp only [p, Category.assoc, Functor.comp_map, ← Functor.map_comp,
      subobjectObstruction_local_zero, Functor.map_zero, comp_zero, zero_comp]
  · have he' : (restrictFunctor q).map k ≫ E.inv.app M =
        e.inv ≫ (restrictFunctor p).map i := by
      apply (cancel_mono (E.hom.app M)).mp
      simp only [Category.assoc, Iso.inv_hom_id_app]
      rw [he, Iso.inv_hom_id_assoc]
      simp [q]
    apply eq_zero_of_restrict_map_eq_zero q _
      ⟨(cokernel i).restrict p, ⟨(openBaseChange j a).app (cokernel i)⟩⟩
    apply (cancel_mono (E.inv.app ((pushforward j).obj (cokernel i)))).mp
    change ((restrictFunctor q).map k ≫
        (restrictFunctor a ⋙ restrictFunctor q).map (subobjectObstruction j i)) ≫ _ = 0 ≫ _
    rw [Category.assoc, E.inv.naturality, ← Category.assoc, he']
    simp only [p, q, Category.assoc, Functor.comp_map, ← Functor.map_comp,
      subobjectObstruction_local_zero, Functor.map_zero, comp_zero, zero_comp]

/-- The actual glued subobject, with comparison isomorphisms commuting
with the two given inclusions. This assertion is valid for arbitrary module
sheaves; coherence follows separately from locality on a covering pair. -/
theorem exists_glued_subobject
    {U V X : Scheme.{u}} (j : U ⟶ X) (a : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion a]
    {M : X.Modules} {A : U.Modules} {B : V.Modules}
    (i : A ⟶ M.restrict j) (k : B ⟶ M.restrict a) [Mono i] [Mono k]
    (e : A.restrict (pullback.fst j a) ≅ B.restrict (pullback.snd j a))
    (he : (restrictFunctor (pullback.fst j a)).map i ≫
        (overlapRestrictIso j a).hom.app M =
      e.hom ≫ (restrictFunctor (pullback.snd j a)).map k) :
    ∃ (N : X.Modules) (s : N ⟶ M), Mono s ∧
      ∃ (eU : N.restrict j ≅ A) (eV : N.restrict a ≅ B),
        (restrictFunctor j).map s = eU.hom ≫ i ∧
        (restrictFunctor a).map s = eV.hom ≫ k := by
  let f := subobjectObstruction j i
  let g := subobjectObstruction a k
  let l := prod.lift f g
  obtain ⟨hij, hka⟩ := overlapCompatible_obstruction_zero j a i k e he
  have hU : i ≫ (restrictFunctor j).map l = 0 :=
    map_prod_lift_comp_eq_zero (restrictFunctor j) i f g
      (subobjectObstruction_local_zero j i) hij
  have hV : k ≫ (restrictFunctor a).map l = 0 :=
    map_prod_lift_comp_eq_zero (restrictFunctor a) k f g
      hka (subobjectObstruction_local_zero a k)
  let hUl := isKernelOfComp ((restrictFunctor j).map prod.fst)
    ((restrictFunctor j).map f) (subobjectObstructionKernelIsLimit j i) hU
    (by rw [← Functor.map_comp, prod.lift_fst])
  let hVl := isKernelOfComp ((restrictFunctor a).map prod.snd)
    ((restrictFunctor a).map g) (subobjectObstructionKernelIsLimit a k) hV
    (by rw [← Functor.map_comp, prod.lift_snd])
  let hU₀ := KernelFork.mapIsLimit _ (kernelIsKernel l) (restrictFunctor j)
  let hV₀ := KernelFork.mapIsLimit _ (kernelIsKernel l) (restrictFunctor a)
  let eU := hU₀.conePointUniqueUpToIso hUl
  let eV := hV₀.conePointUniqueUpToIso hVl
  refine ⟨kernel l, kernel.ι l, inferInstance, eU, eV, ?_, ?_⟩
  · exact (hU₀.conePointUniqueUpToIso_hom_comp hUl WalkingParallelPair.zero).symm
  · exact (hV₀.conePointUniqueUpToIso_hom_comp hVl WalkingParallelPair.zero).symm

end Quillen.CoherentScheme
