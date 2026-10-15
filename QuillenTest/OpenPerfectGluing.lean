/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.BinaryDescent

/-! # Actual two-open perfect gluing and target-map consumers -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.PerfectComplexes.OpenHomotopyGluing
universe u
namespace QuillenTest.OpenPerfectGluing

/-- The complex adjunction unit is exactly the original module-sheaf unit degreewise. -/
theorem original_unit_degree {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Complex U) (n : ℤ) :
    ((extensionByZeroAdjunction j).unit.app K).f n =
      (AlgebraicGeometry.Scheme.Modules.extensionByZeroRestrictAdjunction j).unit.app (K.X n) := rfl

/-- The actual adjoint of a local map restricts to that original map, without a QC premise. -/
theorem original_adjoint_restriction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K : Complex U} {L : Complex X} (f : K ⟶ (restrict j).obj L) :
    (extensionByZeroAdjunction j).unit.app K ≫ (restrict j).map (extensionByZeroMap j f) = f :=
  extensionByZeroMap_restrict j f

section Binary
variable {X : Scheme.{u}} (U V : X.Opens)
  {K : Complex (pullback U.ι V.ι)} {A : Complex U.toScheme} {B : Complex V.toScheme}
  {L : Complex X}
  (α : K ⟶ (restrict (pullback.fst U.ι V.ι)).obj A)
  (β : K ⟶ (restrict (pullback.snd U.ι V.ι)).obj B)

/-- Actual local models hold even before assuming that the two opens cover. -/
theorem actual_local_models [QuasiIso α] [QuasiIso β] :
    QuasiIso (binaryFirst U V α β) ∧ QuasiIso (binarySecond U V α β) :=
  ⟨binaryFirst_quasiIso U V α β, binarySecond_quasiIso U V α β⟩

/-- The actual global cone is locally perfect from the given covering local models. -/
theorem actual_cone_perfect (hUV : U ⊔ V = ⊤)
    (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
    [QuasiIso α] [QuasiIso β] : locallyPerfect X (binary U V α β) :=
  locallyPerfect_binary U V α β hUV hA hB

/-- The local derived comparison is induced by the original constructed chain map. -/
def actual_first_derived_iso [QuasiIso β] :
    (toDerived U.toScheme).obj A ≅
      (toDerived U.toScheme).obj ((restrict U.ι).obj (binary U V α β)) := by
  let := binaryFirst_quasiIso U V α β
  exact asIso ((toDerived U.toScheme).map (binaryFirst U V α β))

@[simp] theorem actual_first_derived_iso_hom [QuasiIso β] :
    (actual_first_derived_iso U V α β).hom =
      (toDerived U.toScheme).map (binaryFirst U V α β) := rfl

variable (p : A ⟶ (restrict U.ι).obj L) (q : B ⟶ (restrict V.ι).obj L)
  (H : Homotopy (α ≫ (restrict (pullback.fst U.ι V.ι)).map p)
    (β ≫ (restrict (pullback.snd U.ι V.ι)).map q ≫
      (openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
        V.ι U.ι pullback.condition.symm).hom.app L))

/-- The constructed target map solves both original local triangles strictly. -/
theorem actual_target_triangles :
    binaryFirst U V α β ≫ (restrict U.ι).map (binaryDesc U V α β p q H) = p ∧
    binarySecond U V α β ≫ (restrict V.ι).map (binaryDesc U V α β p q H) = q :=
  ⟨binaryFirst_desc U V α β p q H, binarySecond_desc U V α β p q H⟩

include H in
/-- Arbitrary original target maps, without weak-map hypotheses, retain their exact local triangles.
  -/
theorem arbitrary_original_target_maps (hUV : U ⊔ V = ⊤)
    (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
    [QuasiIso α] [QuasiIso β] :
    ∃ P : Complex X, locallyPerfect X P ∧
      ∃ (u : A ⟶ (restrict U.ι).obj P) (v : B ⟶ (restrict V.ι).obj P) (d : P ⟶ L),
        QuasiIso u ∧ QuasiIso v ∧
        u ≫ (restrict U.ι).map d = p ∧ v ≫ (restrict V.ι).map d = q :=
  exists_perfect_glue_with_target_map U V α β p q H hUV hA hB

/-- The original global descent induces actual isomorphisms in every homology degree. -/
theorem original_target_homology_iso (hUV : U ⊔ V = ⊤)
    [QuasiIso α] [QuasiIso β] [QuasiIso p] [QuasiIso q] (n : ℤ) :
    IsIso (homologyMap (binaryDesc U V α β p q H) n) := by
  let := quasiIso_binaryDesc U V α β p q H hUV
  infer_instance

include H in
/-- The entire actual geometric gluing endpoint supplies a perfect original weak source for L. -/
theorem actual_perfect_source (hUV : U ⊔ V = ⊤)
    (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
    [QuasiIso α] [QuasiIso β] [QuasiIso p] [QuasiIso q] :
    ∃ (P : Complex X) (_ : locallyPerfect X P) (d : P ⟶ L), QuasiIso d := by
  obtain ⟨P, hP, u, v, d, hu, hv, hd, he, hf⟩ :=
    exists_perfect_glue_over_target U V α β p q H hUV hA hB
  exact ⟨P, hP, d, hd⟩

/-- One-sided local weakness gives the corresponding weak restricted target map independently. -/
theorem first_target_weak_only [QuasiIso β] [QuasiIso p] :
    QuasiIso ((restrict U.ι).map (binaryDesc U V α β p q H)) :=
  desc_restrict_first_quasiIso _ _ _ _ _ _ _ _ _ _ (by
    intro x hx
    rw [IsOpenImmersion.range_pullbackFst]
    exact hx)
end Binary
end QuillenTest.OpenPerfectGluing
