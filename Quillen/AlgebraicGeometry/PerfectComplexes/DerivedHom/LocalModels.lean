/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedHom.FiniteCover
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Genuine finite affine strict models with one lower term bound -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard
variable {X : Scheme.{u}} {E : Complex X}

/-- A local strict model may be restricted to a genuinely affine neighborhood,
retaining an original derived isomorphism and the actual lower term bound. -/
theorem locallyPerfect_exists_affine_strict_lower_model
    (hE : locallyPerfect X E) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∃ (P : Complex U.toScheme) (b : ℤ),
      strictPerfect U.toScheme P ∧ (∀ i, i < b → IsZero (P.X i)) ∧
      Nonempty ((toDerived U.toScheme).obj ((restrict U.ι).obj E) ≅ (toDerived U.toScheme).obj P) :=
        by
  obtain ⟨V, hxV, P, ⟨eP⟩⟩ := hE x
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let j := X.homOfLE hUV
  obtain ⟨a, b, hb⟩ := P.property.1
  refine ⟨U, hU, hxU, (restrict j).obj P.obj, a,
    strictPerfect_restrict j P.property, ?_, ⟨?_⟩⟩
  · intro i hi
    exact (Scheme.Modules.restrictFunctor j).map_isZero (hb i (Or.inl hi))
  · exact ((toDerived U.toScheme).mapIso (restrictOpenInclusionIso hUV E)).symm ≪≫
      restrictDerivedIso j eP

/-- Compactness gives actual finite affine strict models with one common lower
term bound. No global strict representative is asserted. The cover can be empty. -/
theorem locallyPerfect_exists_finite_affine_strict_lower_models [CompactSpace X]
    (hE : locallyPerfect X E) :
    ∃ (s : Finset X.Opens) (b : ℤ), s.sup id = ⊤ ∧
      ∀ U ∈ s, IsAffineOpen U ∧ ∃ P : Complex U.toScheme,
        strictPerfect U.toScheme P ∧ (∀ i, i < b → IsZero (P.X i)) ∧
        Nonempty ((toDerived U.toScheme).obj ((restrict U.ι).obj E) ≅ (toDerived U.toScheme).obj P)
          := by
  classical
  choose U hU hx P b hP hb he using locallyPerfect_exists_affine_strict_lower_model hE
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  obtain ⟨a, ha⟩ := (t.finite_toSet.image b).bddBelow
  let s := t.image U
  refine ⟨s, a, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    have hle : U y ≤ s.sup id := Finset.le_sup (s := s) (f := id) (b := U y) (Finset.mem_image.mpr
      ⟨y, hyt, rfl⟩)
    exact hle hy
  · intro V hV
    change V ∈ t.image U at hV
    obtain ⟨x, hxt, rfl⟩ := Finset.mem_image.mp hV
    refine ⟨hU x, P x, hP x, ?_, he x⟩
    intro i hi
    exact hb x i (lt_of_lt_of_le hi (ha ⟨x, hxt, rfl⟩))

end Quillen.PerfectComplexes
