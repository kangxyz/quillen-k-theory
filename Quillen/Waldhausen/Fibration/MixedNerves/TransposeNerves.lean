import Quillen.Waldhausen.Fibration.MixedNerves.Transpose
import Quillen.CategoryTheory.TheoremA.Diagonal

/-! # Exact mixed-nerve transpose isomorphisms

The explicit index switch commutes with both original ordinal restrictions
and with the literal inclusion of coarse-weak cofibration arrows. No nerve
comparison equivalence is assumed: these are isomorphisms of presentations
of the same original double diagrams.
-/
noncomputable section
open CategoryTheory Opposite
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.MixedNerves
open RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The actual coarse/fine nerve is the transpose of the original horizontal nerve. -/
def coarseTransposeIso : (coarseChainNerve N).flip ≅ horizontalNerve N :=
  NatIso.ofComponents (fun k ↦ NatIso.ofComponents
    (fun n ↦ Equiv.toIso (transposeCoarseEquiv N n.unop k.unop)) (by
      intro n m α
      ext F : 3
      apply CategoryTheory.Functor.ext (fun _ ↦ rfl))) (by
    intro k l β
    ext n F : 4
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl))

/-- The same actual index switch retains the original cofibration predicates. -/
def cofTransposeIso : (cofChainNerve N).flip ≅ horizontalCofNerve N :=
  NatIso.ofComponents (fun k ↦ NatIso.ofComponents
    (fun n ↦ Equiv.toIso (transposeCofEquiv N n.unop k.unop)) (by
      intro n m α
      ext F : 3
      apply CategoryTheory.Functor.ext (fun _ ↦ rfl))) (by
    intro k l β
    ext n F : 4
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl))

@[simp] theorem coarseTransposeIso_hom_app (n k : SimplexCategory)
    (F : ComposableArrows (FineWeakCoarseChains N n) k.len) :
    ((coarseTransposeIso N).hom.app (op k)).app (op n) F = transposeCoarse N n k F := rfl

@[simp] theorem coarseTransposeIso_inv_app (n k : SimplexCategory)
    (F : ComposableArrows (HorizontalChains N k) n.len) :
    ((coarseTransposeIso N).inv.app (op k)).app (op n) F = untransposeCoarse N n k F := rfl

@[simp] theorem cofTransposeIso_hom_app (n k : SimplexCategory)
    (F : ComposableArrows (FineWeakChains N n) k.len) :
    ((cofTransposeIso N).hom.app (op k)).app (op n) F = transposeCof N n k F := rfl

@[simp] theorem cofTransposeIso_inv_app (n k : SimplexCategory)
    (F : ComposableArrows (HorizontalCofChains N k) n.len) :
    ((cofTransposeIso N).inv.app (op k)).app (op n) F = untransposeCof N n k F := rfl

/-- Transposition intertwines the two actual inclusion maps strictly. -/
theorem transpose_inclusion :
    ((CategoryTheory.flipFunctor _ _ _).map (chainInclusion N)) ≫ (coarseTransposeIso N).hom =
      (cofTransposeIso N).hom ≫ horizontalNerveInclusion N := by
  ext k n F : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Original diagonal mixed diagrams are identified by the actual index switch. -/
def coarseDiagonalIso : TheoremA.diagonalSSet (coarseChainNerve N) ≅
    TheoremA.diagonalSSet (horizontalNerve N) :=
  (TheoremA.diagonalFlipIso (coarseChainNerve N)).symm ≪≫
    TheoremA.diagonalFunctor.mapIso (coarseTransposeIso N)

/-- The original diagonal cofibration diagrams have the same literal presentation change. -/
def cofDiagonalIso : TheoremA.diagonalSSet (cofChainNerve N) ≅
    TheoremA.diagonalSSet (horizontalCofNerve N) :=
  (TheoremA.diagonalFlipIso (cofChainNerve N)).symm ≪≫
    TheoremA.diagonalFunctor.mapIso (cofTransposeIso N)

@[simp] theorem coarseDiagonalIso_hom_app (n : SimplexCategory)
    (F : ComposableArrows (FineWeakCoarseChains N n) n.len) :
    (coarseDiagonalIso N).hom.app (op n) F = transposeCoarse N n n F := rfl

@[simp] theorem cofDiagonalIso_hom_app (n : SimplexCategory)
    (F : ComposableArrows (FineWeakChains N n) n.len) :
    (cofDiagonalIso N).hom.app (op n) F = transposeCof N n n F := rfl

/-- The diagonal presentation square uses the literal original inclusion on both sides. -/
theorem diagonal_inclusion :
    TheoremA.diagonalMap (chainInclusion N) ≫ (coarseDiagonalIso N).hom =
      (cofDiagonalIso N).hom ≫ TheoremA.diagonalMap (horizontalNerveInclusion N) := by
  ext n F : 4
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end Quillen.Waldhausen.Fibration.MixedNerves
