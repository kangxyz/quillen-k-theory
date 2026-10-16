/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.StabilizedExtensionTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.ImmersionDerivedRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Roofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.DerivedTarget
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-! # Extending original derived morphisms across an affine chart

The overlap numerator is supplied by an actual derived roof and then glued by
original derived-target gluing. The resulting global map retains its prescribed
local target morphism; a stabilization provides an explicit local summand.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- A local derived morphism to a globally perfect target extends after an
actual overlap roof, without changing the prescribed local derived source. -/
lemma exists_perfect_target_glue_of_overlap_roof {X : Scheme.{u}}
    (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (hroof : OpenDerivedImage.HasDerivedRoofs (pullback.snd U.ι V.ι))
    {A : CochainComplex U.toScheme.Modules ℤ} {B : CochainComplex V.toScheme.Modules ℤ}
      {L : CochainComplex X.Modules ℤ}
    (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
    (hL : locallyPerfect X L)
    (e : (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).obj
      ((restrict (pullback.fst U.ι V.ι)).obj A) ≅
      (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).obj
        ((restrict (pullback.snd U.ι V.ι)).obj B))
    (φ : (DerivedCategory.Q (C := U.toScheme.Modules)).obj A ⟶
      (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj L)) :
    ∃ (P : CochainComplex X.Modules ℤ), locallyPerfect X P ∧
      ∃ (u : (DerivedCategory.Q (C := U.toScheme.Modules)).obj A ≅
          (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P)) (d : P ⟶ L),
        u.hom ≫ (DerivedCategory.Q (C := U.toScheme.Modules)).map ((restrict U.ι).map d) = φ := by
  let a := pullback.fst U.ι V.ι
  let b := pullback.snd U.ι V.ι
  let Q := DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)
  let c := openSquareRestrictIso b a V.ι U.ι pullback.condition.symm
  let γ := e.inv ≫ restrictDerivedHom a φ ≫ Q.map (c.inv.app L)
  obtain ⟨B', q, p, hB', hq, hp⟩ :=
    hroof B ((restrict V.ι).obj L) hB (locallyPerfect_restrict V.ι hL) γ
  change Q.map ((restrict b).map q) ≫ γ = Q.map ((restrict b).map p) at hp
  let e' := e ≪≫ (asIso (Q.map ((restrict b).map q))).symm
  have he' : restrictDerivedHom a φ =
      e'.hom ≫ restrictDerivedHom b ((DerivedCategory.Q (C := V.toScheme.Modules)).map p) ≫
        Q.map (c.hom.app L) := by
    rw [restrictDerivedHom_map]
    change _ = (e.hom ≫ inv (Q.map ((restrict b).map q))) ≫ _ ≫ _
    rw [← hp]
    simp only [γ, Category.assoc, IsIso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    rw [← Q.map_comp, c.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  obtain ⟨P, hP, u, v, d, hu, hv, he⟩ :=
    OpenHomotopyGluing.exists_perfect_glue_of_derived_target U V hUV hA hB'
      e' φ ((DerivedCategory.Q (C := V.toScheme.Modules)).map p) he'
  exact ⟨P, hP, u, d, hu⟩

/-- A stabilized source extends over an affine attachment together with its
original derived map to a globally perfect target. The local equation retains
the original projection onto the unshifted summand. -/
lemma exists_stabilized_target_extension_across_affine_chart {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (U V : X.Opens) (hU : IsCompact (U : Set X))
    (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    {E : CochainComplex U.toScheme.Modules ℤ} {L : CochainComplex X.Modules ℤ}
    (hE : locallyPerfect U.toScheme E) (hL : locallyPerfect X L)
    (φ : (DerivedCategory.Q (C := U.toScheme.Modules)).obj E ⟶
      (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj L)) :
    ∃ (P : CochainComplex X.Modules ℤ), locallyPerfect X P ∧
      ∃ (u : (DerivedCategory.Q (C := U.toScheme.Modules)).obj (E ⊞ E⟦(1 : ℤ)⟧) ≅
          (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P)) (d : P ⟶ L),
        u.hom ≫ (DerivedCategory.Q (C := U.toScheme.Modules)).map ((restrict U.ι).map d) =
          (DerivedCategory.Q (C := U.toScheme.Modules)).map (biprod.fst : E ⊞ E⟦(1 : ℤ)⟧ ⟶ E)
            ≫ φ := by
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  let : IsAffine V.toScheme := hV
  let a := pullback.fst U.ι V.ι
  let b := pullback.snd U.ι V.ι
  obtain ⟨B, hB, ⟨eB⟩⟩ := exists_strict_stabilized_extension_into_affine b
    ((restrict a).obj E) (locallyPerfect_restrict a hE)
  have hA : locallyPerfect U.toScheme (E ⊞ E⟦(1 : ℤ)⟧) :=
    (abelianExactStructure (CochainComplex U.toScheme.Modules ℤ)).prop_biprod
      (locallyPerfect U.toScheme)
      hE (locallyPerfect_shift hE 1)
  let e := (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).mapIso
    (restrictStabilizationIso a E) ≪≫ eB.symm
  exact exists_perfect_target_glue_of_overlap_roof U V hUV
    (OpenDerivedImage.affine_hasDerivedRoofs_of_compact b) hA
    (locallyPerfect_of_strictPerfect hB) hL e
    ((DerivedCategory.Q (C := U.toScheme.Modules)).map biprod.fst ≫ φ)

/-- The original local derived source is an explicit summand of the extended
source, and the global chain map restricts to the prescribed original morphism
on that same summand. -/
lemma exists_retract_target_extension_across_affine_chart {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (U V : X.Opens) (hU : IsCompact (U : Set X))
    (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    {E : CochainComplex U.toScheme.Modules ℤ} {L : CochainComplex X.Modules ℤ}
    (hE : locallyPerfect U.toScheme E) (hL : locallyPerfect X L)
    (φ : (DerivedCategory.Q (C := U.toScheme.Modules)).obj E ⟶
      (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj L)) :
    ∃ (P : CochainComplex X.Modules ℤ), locallyPerfect X P ∧
      ∃ (r : Retract ((DerivedCategory.Q (C := U.toScheme.Modules)).obj E)
          ((DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P))) (d : P ⟶ L),
        r.i ≫ (DerivedCategory.Q (C := U.toScheme.Modules)).map ((restrict U.ι).map d) = φ := by
  obtain ⟨P, hP, u, d, hu⟩ :=
    exists_stabilized_target_extension_across_affine_chart U V hU hV hUV hE hL φ
  let Q := DerivedCategory.Q (C := U.toScheme.Modules)
  let r : Retract (Q.obj E) (Q.obj ((restrict U.ι).obj P)) :=
    { i := Q.map biprod.inl ≫ u.hom
      r := u.inv ≫ Q.map biprod.fst
      retract := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        rw [← Q.map_comp, biprod.inl_fst, Q.map_id] }
  refine ⟨P, hP, r, d, ?_⟩
  change (Q.map biprod.inl ≫ u.hom) ≫ _ = _
  rw [Category.assoc, hu, ← Category.assoc, ← Q.map_comp, biprod.inl_fst,
    Q.map_id, Category.id_comp]

end Quillen.PerfectComplexes
