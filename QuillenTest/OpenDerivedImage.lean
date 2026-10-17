/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Structure
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Dense
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.DualFactorization
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.OpenDerivedImageRoofs
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Original image, global roof, cofiber and literal dual-lift consumers -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace QuillenTest.OpenDerivedImage
open Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts

/-- A backward original weak arrow really preserves the saturated image. -/
theorem backward_original_weak_mem {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {A B : CochainComplex U.Modules ℤ} (f : A ⟶ B) [QuasiIso f] (hB : complexObjects j B) :
    complexObjects j A := (complexObjects_iff_of_quasiIso j f).mpr hB

/-- Arbitrary original all-sheaf global models retain the specified open arrow. -/
theorem original_perfect_roof (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (A P : CochainComplex (Spec R).Modules ℤ)
    (hA : locallyPerfect (Spec R) A) (hP : locallyPerfect (Spec R) P)
    (α : (DerivedCategory.Q (C := W.toScheme.Modules)).obj ((restrict W.ι).obj A) ⟶
      (DerivedCategory.Q (C := W.toScheme.Modules)).obj ((restrict W.ι).obj P)) :
    ∃ (M : CochainComplex (Spec R).Modules ℤ) (q : M ⟶ A) (p : M ⟶ P),
      locallyPerfect (Spec R) M ∧ QuasiIso ((restrict W.ι).map q) ∧
      (DerivedCategory.Q (C := W.toScheme.Modules)).map ((restrict W.ι).map q) ≫ α =
        (DerivedCategory.Q (C := W.toScheme.Modules)).map ((restrict W.ι).map p) :=
  affine_hasDerivedRoofs R W hW A P hA hP α

/-- An invertible prescribed arrow makes both actual roof arrows weak on W,
and recovers its original inverse without replacing either target. -/
theorem original_isomorphism_roof (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (A P : CochainComplex (Spec R).Modules ℤ)
    (hA : locallyPerfect (Spec R) A) (hP : locallyPerfect (Spec R) P)
    (e : (DerivedCategory.Q (C := W.toScheme.Modules)).obj ((restrict W.ι).obj A) ≅
      (DerivedCategory.Q (C := W.toScheme.Modules)).obj ((restrict W.ι).obj P)) :
    ∃ (M : CochainComplex (Spec R).Modules ℤ) (q : M ⟶ A) (p : M ⟶ P),
      locallyPerfect (Spec R) M ∧ QuasiIso ((restrict W.ι).map q) ∧
      QuasiIso ((restrict W.ι).map p) ∧
      (DerivedCategory.Q (C := W.toScheme.Modules)).map ((restrict W.ι).map p) ≫ e.inv =
        (DerivedCategory.Q (C := W.toScheme.Modules)).map ((restrict W.ι).map q) := by
  obtain ⟨M, q, p, hM, hq, he⟩ := original_perfect_roof R W hW A P hA hP e.hom
  have hp : QuasiIso ((restrict W.ι).map p) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso W.toScheme.Modules _).mp
    change IsIso ((DerivedCategory.Q (C := W.toScheme.Modules)).map ((restrict W.ι).map p))
    rw [← he]
    infer_instance
  exact ⟨M, q, p, hM, hq, hp, by rw [← he]; simp⟩

/-- Both prescribed global maps retain one shared denominator and their
original postcompositions. -/
theorem shared_global_denominator {X : Scheme.{u}} {P A B T : CochainComplex X.Modules ℤ}
    (α : (DerivedCategory.Q (C := X.Modules)).obj P ⟶ (DerivedCategory.Q (C := X.Modules)).obj A)
    (β : (DerivedCategory.Q (C := X.Modules)).obj P ⟶ (DerivedCategory.Q (C := X.Modules)).obj B)
    (a : A ⟶ T) (b : B ⟶ T) :
    ∃ (M : CochainComplex X.Modules ℤ) (s : M ⟶ P) (f : M ⟶ A) (g : M ⟶ B),
      QuasiIso s ∧
      (DerivedCategory.Q (C := X.Modules)).map s ≫ α ≫ (DerivedCategory.Q (C := X.Modules)).map a =
        (DerivedCategory.Q (C := X.Modules)).map (f ≫ a) ∧
      (DerivedCategory.Q (C := X.Modules)).map s ≫ β ≫ (DerivedCategory.Q (C := X.Modules)).map b =
        (DerivedCategory.Q (C := X.Modules)).map (g ≫ b) := by
  obtain ⟨M, s, f, g, hs, hf, hg⟩ := common_global_right_fraction α β
  exact ⟨M, s, f, g, hs,
    by rw [← Category.assoc, hf, Functor.map_comp],
    by rw [← Category.assoc, hg, Functor.map_comp]⟩

/-- The actual three SES endpoints satisfy all three closure implications. -/
theorem original_shortExact_image (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (S : ShortComplex (CochainComplex W.toScheme.Modules ℤ))
      (hS : S.ShortExact)
      :
    (complexObjects W.ι S.X₁ → complexObjects W.ι S.X₂ → complexObjects W.ι S.X₃) ∧
    (complexObjects W.ι S.X₁ → complexObjects W.ι S.X₃ → complexObjects W.ι S.X₂) ∧
    (complexObjects W.ι S.X₂ → complexObjects W.ι S.X₃ → complexObjects W.ι S.X₁) :=
  ⟨complexObjects_quotient_of_shortExact W.ι (affine_hasDerivedRoofs R W hW) hS,
    complexObjects_of_shortExact W.ι (affine_hasDerivedRoofs R W hW) hS,
    complexObjects_kernel_of_shortExact W.ι (affine_hasDerivedRoofs R W hW) hS⟩

/-- No nonempty-open condition is hidden in actual complement density. -/
theorem empty_open_complement (R : CommRingCat.{u})
    (E : CochainComplex (⊥ : (Spec R).Opens).toScheme.Modules ℤ)
    (hE : locallyPerfect (⊥ : (Spec R).Opens).toScheme E) :
    ∃ C : CochainComplex (⊥ : (Spec R).Opens).toScheme.Modules ℤ,
      strictPerfect _ C ∧ complexObjects (⊥ : (Spec R).Opens).ι (C ⊞ E) :=
  exists_strict_complement R ⊥ (by simp) E hE

/-- The actual chosen categorical coproduct, including arbitrary choice of
its colimit object, has a genuine global derived-image witness. -/
theorem chosen_coproduct_complement (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) [HasBinaryCoproducts (Perfect W.toScheme)]
    (A : Perfect W.toScheme) : ∃ B : Perfect W.toScheme,
      ∃ P : CochainComplex (Spec R).Modules ℤ, locallyPerfect (Spec R) P ∧
        Nonempty ((DerivedCategory.Q (C := W.toScheme.Modules)).obj ((restrict W.ι).obj P) ≅
          (DerivedCategory.Q (C := W.toScheme.Modules)).obj (A ⨿ B).obj) :=
  affine_complement R W hW A

/-- Genuine geometric roofs give both literal incoming-factorization triangles,
actual split epis and actual source/target kernel membership. -/
theorem original_dual_factorization (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (P : CochainComplex (Spec R).Modules ℤ)
    (hP : locallyPerfect (Spec R) P) (B B' : CochainComplex W.toScheme.Modules ℤ)
    (hB' : complexObjects W.ι B') (w : (restrict W.ι).obj P ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (C : CochainComplex (Spec R).Modules ℤ) (D : CochainComplex W.toScheme.Modules ℤ)
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

end QuillenTest.OpenDerivedImage
