/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenSourceSupportRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.StabilizedExtension
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedRetractComplement

/-! # Stabilized projector cones preserve the original source support -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] standardDerivedModules standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The original complement projector has a genuine global numerator cone retaining every
  source-support condition, the exact projector square, and its original inclusion equation. -/
lemma exists_stabilized_extension_cone_preserving_source_support (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P : ModuleComplex R} (hP : moduleStrictPerfect R P) (C E : Complex W.toScheme)
    (e : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ≅
      (toDerived W.toScheme).obj (C ⊞ E)) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t g : P' ⟶ P),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) ≫ e.hom =
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ e.hom ≫
          (toDerived W.toScheme).map (biprod.map (𝟙 C) (0 : E ⟶ E)) ∧
      moduleStrictPerfect R (CochainComplex.mappingCone g) ∧
      (∀ r : R, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P)) →
        IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj (CochainComplex.mappingCone g)))) ∧
      ∃ eCone : (toDerived W.toScheme).obj
        ((restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone g))) ≅
          (toDerived W.toScheme).obj (E ⊞ E⟦(1 : ℤ)⟧),
        (toDerived W.toScheme).map ((restrict W.ι).map
          ((associatedComplex R).map (CochainComplex.mappingCone.inr g))) ≫ eCone.hom =
            e.hom ≫ (toDerived W.toScheme).map
              ((biprod.snd : C ⊞ E ⟶ E) ≫ (biprod.inl : E ⟶ E ⊞ E⟦(1 : ℤ)⟧)) := by
  let p : C ⊞ E ⟶ C ⊞ E := biprod.map (𝟙 C) (0 : E ⟶ E)
  let α := e.hom ≫ (toDerived W.toScheme).map p ≫ e.inv
  obtain ⟨P', hP', t, g, ht, hsq, hsource⟩ :=
    exists_quasiCompact_open_strict_roof_preserving_source_support R W hW hP hP α
  have heq : (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) ≫ e.hom =
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ e.hom ≫
        (toDerived W.toScheme).map p := by
    rw [← hsq]
    simp [α, Category.assoc]
  refine ⟨P', hP', t, g, ht, heq, moduleStrictPerfect_mappingCone R hP' hP g,
    (fun r hr => isZero_localized_mappingCone_of_isZero R r g (hsource r hr) hr), ?_⟩
  let T := (toDerived W.toScheme).mapTriangle.obj (CochainComplex.mappingCone.triangle
    ((restrict W.ι).map ((associatedComplex R).map g)))
  let T' := (toDerived W.toScheme).mapTriangle.obj (CochainComplex.mappingCone.triangle p)
  let et := isoTriangleOfIso₁₂ T T'
    (DerivedCategory.mappingCone_triangle_distinguished _)
      (DerivedCategory.mappingCone_triangle_distinguished _)
    (asIso ((toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t))) ≪≫ e) e
      (by
      change (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) ≫ e.hom =
        ((toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ e.hom) ≫
          (toDerived W.toScheme).map p
      simpa only [Category.assoc] using heq)
  let ec := (toDerived W.toScheme).mapIso (openAssociatedConeIso R W.ι g) ≪≫
    Triangle.π₃.mapIso et ≪≫ Quillen.CochainComplex.projectorConeDerivedIso C E
  refine ⟨ec, ?_⟩
  have hcomm := et.hom.comm₂
  change (toDerived W.toScheme).map (CochainComplex.mappingCone.inr
      ((restrict W.ι).map ((associatedComplex R).map g))) ≫ (Triangle.π₃.mapIso et).hom =
        e.hom ≫ (toDerived W.toScheme).map (CochainComplex.mappingCone.inr p) at hcomm
  dsimp only [ec, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← (toDerived W.toScheme).map_comp,
    openAssociatedConeIso_inr]
  erw [hcomm]
  rw [Category.assoc]
  exact congrArg (fun z => e.hom ≫ z) (Quillen.CochainComplex.projectorConeDerivedIso_inr C E)

/-- An actual local derived retract has a stabilized global strict extension
with every principal support condition of the original global source retained. -/
lemma exists_stabilized_extension_preserving_support_of_retract (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E)
    (r : Retract ((toDerived W.toScheme).obj E)
      ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)))) :
    ∃ (Q : ModuleComplex R), moduleStrictPerfect R Q ∧
      Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj Q)) ≅
        (toDerived W.toScheme).obj (E ⊞ E⟦(1 : ℤ)⟧)) ∧
      ∀ z : R, IsZero (DerivedCategory.Q.obj ((localize z (.up ℤ)).obj P)) →
        IsZero (DerivedCategory.Q.obj ((localize z (.up ℤ)).obj Q)) := by
  obtain ⟨C, hC, e, he⟩ := exists_actual_perfect_complement_of_derived_retract hE
    (locallyPerfect_restrict W.ι (locallyPerfect_of_strictPerfect (strictPerfect_associated R hP)))
      r
  let e' := e ≪≫ (toDerived W.toScheme).mapIso (biprod.braiding E C)
  obtain ⟨P', hP', t, g, ht, hsquare, hg, hsupport, eCone, hCone⟩ :=
    exists_stabilized_extension_cone_preserving_source_support R W hW hP C E e'
  exact ⟨CochainComplex.mappingCone g, hg, ⟨eCone⟩, hsupport⟩

end Quillen.PerfectComplexes.Affine
