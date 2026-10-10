/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Homology.KProjectiveRepresentatives

/-!
# Exact representatives of derived isomorphisms between K-projective complexes

The original derived isomorphism is represented by actual chain maps in both
directions. Proven K-projectivity turns their original derived equalities into
actual inverse homotopies. The forward map represents the exact input derived
morphism, with independent category and derived-category universes.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory
namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An original derived isomorphism between actual K-projective complexes
has a chain-homotopy equivalence representing its exact original forward map. -/
theorem exists_homotopyEquiv_of_derivedIso {P Q : CochainComplex C ℤ}
    [P.IsKProjective] [Q.IsKProjective]
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) :
    ∃ h : HomotopyEquiv P Q, DerivedCategory.Q.map h.hom = e.hom := by
  obtain ⟨f, hf⟩ := exists_chain_representative_of_isKProjective e.hom
  obtain ⟨g, hg⟩ := exists_chain_representative_of_isKProjective e.inv
  refine ⟨⟨f, g, homotopyOfDerivedEqOfIsKProjective _ _ ?_,
    homotopyOfDerivedEqOfIsKProjective _ _ ?_⟩, hf⟩
  · rw [DerivedCategory.Q.map_comp, hf, hg, e.hom_inv_id, DerivedCategory.Q.map_id]
  · rw [DerivedCategory.Q.map_comp, hg, hf, e.inv_hom_id, DerivedCategory.Q.map_id]

end Quillen.CochainComplex
