/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Structure
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Dense
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.DualFactorization
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenDerivedImageRoofs

/-! # Original image, global roof, cofiber and literal dual-lift consumers -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
universe u
namespace Tests.OpenDerivedImage
open Quillen.PerfectComplexes Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts

/-- A backward original weak arrow really preserves the saturated image. -/
theorem backward_original_weak_mem {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {A B : Complex U} (f : A ⟶ B) [QuasiIso f] (hB : complexObjects j B) :
    complexObjects j A := (complexObjects_iff_of_quasiIso j f).mpr hB

/-- Arbitrary original all-sheaf global models retain the specified open arrow. -/
theorem original_perfect_roof (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (A P : Complex (Spec R))
    (hA : locallyPerfect (Spec R) A) (hP : locallyPerfect (Spec R) P)
    (α : (toDerived W.toScheme).obj ((restrict W.ι).obj A) ⟶
      (toDerived W.toScheme).obj ((restrict W.ι).obj P)) :
    ∃ (M : Complex (Spec R)) (q : M ⟶ A) (p : M ⟶ P),
      locallyPerfect (Spec R) M ∧ QuasiIso ((restrict W.ι).map q) ∧
      (toDerived W.toScheme).map ((restrict W.ι).map q) ≫ α =
        (toDerived W.toScheme).map ((restrict W.ι).map p) :=
  affine_hasDerivedRoofs R W hW A P hA hP α

/-- An invertible prescribed arrow makes both actual roof arrows weak on W,
and recovers its original inverse without replacing either target. -/
theorem original_isomorphism_roof (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (A P : Complex (Spec R))
    (hA : locallyPerfect (Spec R) A) (hP : locallyPerfect (Spec R) P)
    (e : (toDerived W.toScheme).obj ((restrict W.ι).obj A) ≅
      (toDerived W.toScheme).obj ((restrict W.ι).obj P)) :
    ∃ (M : Complex (Spec R)) (q : M ⟶ A) (p : M ⟶ P),
      locallyPerfect (Spec R) M ∧ QuasiIso ((restrict W.ι).map q) ∧
      QuasiIso ((restrict W.ι).map p) ∧
      (toDerived W.toScheme).map ((restrict W.ι).map p) ≫ e.inv =
        (toDerived W.toScheme).map ((restrict W.ι).map q) := by
  obtain ⟨M, q, p, hM, hq, he⟩ := original_perfect_roof R W hW A P hA hP e.hom
  have hp : QuasiIso ((restrict W.ι).map p) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso W.toScheme.Modules _).mp
    change IsIso ((toDerived W.toScheme).map ((restrict W.ι).map p))
    rw [← he]
    infer_instance
  exact ⟨M, q, p, hM, hq, hp, by rw [← he]; simp⟩

/-- Both prescribed global maps retain one shared denominator and their
original postcompositions. -/
theorem shared_global_denominator {X : Scheme.{u}} {P A B T : Complex X}
    (α : (toDerived X).obj P ⟶ (toDerived X).obj A)
    (β : (toDerived X).obj P ⟶ (toDerived X).obj B)
    (a : A ⟶ T) (b : B ⟶ T) :
    ∃ (M : Complex X) (s : M ⟶ P) (f : M ⟶ A) (g : M ⟶ B),
      QuasiIso s ∧
      (toDerived X).map s ≫ α ≫ (toDerived X).map a = (toDerived X).map (f ≫ a) ∧
      (toDerived X).map s ≫ β ≫ (toDerived X).map b = (toDerived X).map (g ≫ b) := by
  obtain ⟨M, s, f, g, hs, hf, hg⟩ := common_global_right_fraction α β
  exact ⟨M, s, f, g, hs,
    by rw [← Category.assoc, hf, Functor.map_comp],
    by rw [← Category.assoc, hg, Functor.map_comp]⟩

/-- The actual three SES endpoints satisfy all three closure implications. -/
theorem original_shortExact_image (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (S : ShortComplex (Complex W.toScheme)) (hS : S.ShortExact)
      :
    (complexObjects W.ι S.X₁ → complexObjects W.ι S.X₂ → complexObjects W.ι S.X₃) ∧
    (complexObjects W.ι S.X₁ → complexObjects W.ι S.X₃ → complexObjects W.ι S.X₂) ∧
    (complexObjects W.ι S.X₂ → complexObjects W.ι S.X₃ → complexObjects W.ι S.X₁) :=
  ⟨complexObjects_quotient_of_shortExact W.ι (affine_hasDerivedRoofs R W hW) hS,
    complexObjects_of_shortExact W.ι (affine_hasDerivedRoofs R W hW) hS,
    complexObjects_kernel_of_shortExact W.ι (affine_hasDerivedRoofs R W hW) hS⟩

/-- No nonempty-open condition is hidden in actual complement density. -/
theorem empty_open_complement (R : CommRingCat.{u})
    (E : Complex (⊥ : (Spec R).Opens).toScheme)
    (hE : locallyPerfect (⊥ : (Spec R).Opens).toScheme E) :
    ∃ C : Complex (⊥ : (Spec R).Opens).toScheme,
      strictPerfect _ C ∧ complexObjects (⊥ : (Spec R).Opens).ι (C ⊞ E) :=
  exists_strict_complement R ⊥ (by simp) E hE

/-- The actual chosen categorical coproduct, including arbitrary choice of
its colimit object, has a genuine global derived-image witness. -/
theorem chosen_coproduct_complement (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) [HasBinaryCoproducts (Perfect W.toScheme)]
    (A : Perfect W.toScheme) : ∃ B : Perfect W.toScheme,
      ∃ P : Complex (Spec R), locallyPerfect (Spec R) P ∧
        Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj P) ≅
          (toDerived W.toScheme).obj (A ⨿ B).obj) :=
  affine_complement R W hW A

/-- Genuine geometric roofs give both literal incoming-factorization triangles,
actual split epis and actual source/target kernel membership. -/
theorem original_dual_factorization (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (P : Complex (Spec R))
    (hP : locallyPerfect (Spec R) P) (B B' : Complex W.toScheme)
    (hB' : complexObjects W.ι B') (w : (restrict W.ι).obj P ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (C : Complex (Spec R)) (D : Complex W.toScheme)
      (c : C ⟶ P) (d : D ⟶ B) (u : (restrict W.ι).obj C ⟶ D) (v : B' ⟶ D),
      locallyPerfect (Spec R) C ∧ complexObjects W.ι D ∧ QuasiIso u ∧ QuasiIso v ∧
      u ≫ d = (restrict W.ι).map c ≫ w ∧ v ≫ d = b ∧
      (∀ i, IsSplitEpi (c.f i)) ∧ (∀ i, IsSplitEpi (d.f i)) ∧
      locallyPerfect (Spec R) (kernel c) ∧ complexObjects W.ι (kernel d) :=
  exists_dual_factorization W.ι (affine_hasDerivedRoofs R W hW) P hP B B' hB' w b

/-- Actual ambient cofibrations are reflected with their genuine image quotient. -/
theorem original_cofibration_reflection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [Fact (HasDerivedRoofs j)] {A B : ComplexObj j} (f : A ⟶ B) :
    (perfectWaldhausen U).cof ((inclusion j).map f) ↔ (complexWaldhausen j).cof f :=
  inclusion_cof_iff j f

/-- The original restriction arrow survives the full-subcategory corestriction literally. -/
theorem original_restriction_triangle {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [Fact (HasDerivedRoofs j)] : complexCorestrict j ⋙ inclusion j = perfectRestrict j := rfl

end Tests.OpenDerivedImage
