/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Algebra.Homology.DerivedPreEqualityDenominators
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.OverlapCompatibility
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedMorphisms

/-! # Actual perfect gluing from the original derived overlap isomorphism -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
open scoped ZeroObject
namespace Quillen.PerfectComplexes.OpenHomotopyGluing
variable {X : Scheme.{u}} (U V : X.Opens)
  {A : Complex U.toScheme} {B : Complex V.toScheme} {L : Complex X}

/-- A specified original derived overlap isomorphism, compatible with arbitrary
original local target maps, glues to actual local quasi-isomorphisms and strict
target triangles. Those local comparisons realize precisely the original isomorphism. -/
theorem exists_perfect_glue_of_derived_overlap
    (hUV : U ⊔ V = ⊤) (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
    (e : (toDerived (pullback U.ι V.ι)).obj ((restrict (pullback.fst U.ι V.ι)).obj A) ≅
      (toDerived (pullback U.ι V.ι)).obj ((restrict (pullback.snd U.ι V.ι)).obj B))
    (p : A ⟶ (restrict U.ι).obj L) (q : B ⟶ (restrict V.ι).obj L)
    (he : (toDerived (pullback U.ι V.ι)).map ((restrict (pullback.fst U.ι V.ι)).map p) =
      e.hom ≫ (toDerived (pullback U.ι V.ι)).map
        ((restrict (pullback.snd U.ι V.ι)).map q ≫
          (openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
            V.ι U.ι pullback.condition.symm).hom.app L)) :
    ∃ P : Complex X, locallyPerfect X P ∧
      ∃ (u : A ⟶ (restrict U.ι).obj P) (v : B ⟶ (restrict V.ι).obj P) (d : P ⟶ L),
        QuasiIso u ∧ QuasiIso v ∧
        u ≫ (restrict U.ι).map d = p ∧ v ≫ (restrict V.ι).map d = q ∧
        (toDerived (pullback U.ι V.ι)).map ((restrict (pullback.fst U.ι V.ι)).map u) =
          e.hom ≫ (toDerived (pullback U.ι V.ι)).map
            ((restrict (pullback.snd U.ι V.ι)).map v ≫
              (openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
                V.ι U.ι pullback.condition.symm).hom.app P) := by
  let W := pullback U.ι V.ι
  let a := pullback.fst U.ι V.ι
  let b := pullback.snd U.ι V.ι
  let : HasDerivedCategory.{u+1} W.Modules := HasDerivedCategory.standard _
  obtain ⟨K, α, β, hα, hβ, hfac, ⟨H⟩⟩ :=
    Quillen.CochainComplex.exists_weak_span_homotopy_of_derived_iso e
      ((restrict a).map p) ((restrict b).map q ≫
        (openSquareRestrictIso b a V.ι U.ι pullback.condition.symm).hom.app L) he
  have H' : Homotopy (α ≫ (restrict a).map p)
      (β ≫ (restrict b).map q ≫
        (openSquareRestrictIso b a V.ι U.ι pullback.condition.symm).hom.app L) := by
    simpa only [Category.assoc] using H
  refine ⟨binary U V α β, locallyPerfect_binary U V α β hUV hA hB,
    binaryFirst U V α β, binarySecond U V α β, binaryDesc U V α β p q H',
    binaryFirst_quasiIso U V α β, binarySecond_quasiIso U V α β,
    binaryFirst_desc U V α β p q H', binarySecond_desc U V α β p q H', ?_⟩
  apply (cancel_epi ((toDerived W).map α)).mp
  rw [← Category.assoc]
  change (toDerived W).map α ≫ (toDerived W).map ((restrict a).map (binaryFirst U V α β)) =
    ((toDerived W).map α ≫ e.hom) ≫ (toDerived W).map
      ((restrict b).map (binarySecond U V α β) ≫
        (openSquareRestrictIso b a V.ι U.ι pullback.condition.symm).hom.app (binary U V α β))
  change (toDerived W).map α ≫ e.hom = (toDerived W).map β at hfac
  rw [hfac]
  simpa only [W, a, b, binary, binaryFirst, binarySecond, Functor.map_comp, Category.assoc] using
    toDerived_map_eq_of_homotopy (overlapHomotopy a b U.ι V.ι pullback.condition α β)

/-- Every original derived overlap isomorphism of local perfect complexes admits
a genuine global perfect model realizing that same isomorphism. -/
theorem exists_perfect_glue_of_derived_iso
    (hUV : U ⊔ V = ⊤) (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
    (e : (toDerived (pullback U.ι V.ι)).obj ((restrict (pullback.fst U.ι V.ι)).obj A) ≅
      (toDerived (pullback U.ι V.ι)).obj ((restrict (pullback.snd U.ι V.ι)).obj B)) :
    ∃ P : Complex X, locallyPerfect X P ∧
      ∃ (u : A ⟶ (restrict U.ι).obj P) (v : B ⟶ (restrict V.ι).obj P),
        QuasiIso u ∧ QuasiIso v ∧
        (toDerived (pullback U.ι V.ι)).map ((restrict (pullback.fst U.ι V.ι)).map u) =
          e.hom ≫ (toDerived (pullback U.ι V.ι)).map
            ((restrict (pullback.snd U.ι V.ι)).map v ≫
              (openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
                V.ι U.ι pullback.condition.symm).hom.app P) := by
  obtain ⟨P, hP, u, v, d, hu, hv, _, _, he⟩ :=
    exists_perfect_glue_of_derived_overlap U V hUV hA hB e
      (0 : A ⟶ (restrict U.ι).obj (0 : Complex X))
      (0 : B ⟶ (restrict V.ι).obj (0 : Complex X)) (by simp)
  exact ⟨P, hP, u, v, hu, hv, he⟩

end Quillen.PerfectComplexes.OpenHomotopyGluing
