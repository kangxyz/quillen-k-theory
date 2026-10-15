/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.QuillenComparison.ReconstructionIndices
public import Quillen.Waldhausen.QuillenComparison.ExtendedRows
public import Quillen.Waldhausen.QuillenComparison.FlagPresentation
public import Quillen.Waldhausen.QuillenComparison.BisimplicialMap

/-! # The reconstructed edgewise row and its original central chain -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v

namespace Quillen.Waldhausen.QuillenComparison

/-- The literal two-endpoint extension has the new edgewise ordinal's size. -/
theorem reconstructionOrdinal_eq (n : ℕ) :
    Edgewise.ε.obj ⦋n + 1⦌ = ⦋(Edgewise.ε.obj ⦋n⦌).len + 1 + 1⦌ := by
  apply SimplexCategory.ext
  change (n + 1) + (n + 1) + 1 = n + n + 1 + 1 + 1
  omega

/-- The explicit ordinal cast from the new edgewise row to the literal extension. -/
def reconstructionOrdinalCast (n : ℕ) :
    Edgewise.ε.obj ⦋n + 1⦌ ⟶ ⦋(Edgewise.ε.obj ⦋n⦌).len + 1 + 1⦌ :=
  eqToHom (reconstructionOrdinal_eq n)

private theorem ordinal_eqToHom_val {n m : SimplexCategory} (h : n = m)
    (i : Fin (n.len + 1)) : ((eqToHom h).toOrderHom i).val = i.val := by
  subst m
  rfl

@[simp]
theorem reconstructionOrdinalCast_val (n : ℕ)
    (i : Fin ((Edgewise.ε.obj ⦋n + 1⦌).len + 1)) :
    ((reconstructionOrdinalCast n).toOrderHom i).val = i.val :=
  ordinal_eqToHom_val _ _

/-- The two middle embeddings agree as actual ordinal maps, including all indices. -/
theorem reconstructionMiddle_comp_cast (n : ℕ) :
    reconstructionMiddleOrdinal n ≫ reconstructionOrdinalCast n =
      flagMiddleOrdinal (Edgewise.ε.obj ⦋n⦌).len := by
  ext i : 3
  apply Fin.ext
  change ((reconstructionOrdinalCast n).toOrderHom
    ((reconstructionMiddleOrdinal n).toOrderHom i)).val = i.val + 1
  rw [reconstructionOrdinalCast_val, reconstructionMiddleOrdinal_val]

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- Composition of actual row restrictions agrees with restriction along the composite. -/
def rowReindexCompIso {l m n : SimplexCategory} (α : l ⟶ m) (β : m ⟶ n)
    (F : Row E n) :
    (rowReindex E α).obj ((rowReindex E β).obj F) ⟶
      (rowReindex E (α ≫ β)).obj F := Iso.refl _

/-- Equal ordinal maps give the displayed equality isomorphism of restricted rows. -/
def rowReindexEqIso {m n : SimplexCategory} {α β : m ⟶ n} (h : α = β)
    (F : Row E n) : (rowReindex E α).obj F ⟶ (rowReindex E β).obj F := by
  subst β
  exact Iso.refl _

variable {n : ℕ} (F : Row E (Edgewise.ε.obj ⦋n⦌))
variable {P Z : C} (p : P ⟶ (initialFlag E F).obj (Fin.last (Edgewise.ε.obj ⦋n⦌).len))
  (hp : E.deflation p) (r : P ⟶ Z) (hr : E.inflation r)

/-- The actual reconstructed exact row, with the required edgewise indexing ordinal. -/
def reconstructedRow : Row E (Edgewise.ε.obj ⦋n + 1⦌) :=
  (rowReindex E (reconstructionOrdinalCast n)).obj
    (extendedRow E (initialFlag E F) (initialFlag_inflation E F) p hp r hr)

/-- Restriction to the old middle ordinal recovers the original exact row. -/
def reconstructedMiddleIso :
    (rowReindex E (reconstructionMiddleOrdinal n)).obj (reconstructedRow E F p hp r hr) ⟶ F :=
  rowReindexCompIso E (reconstructionMiddleOrdinal n) (reconstructionOrdinalCast n) _ ≪≫
    rowReindexEqIso E (reconstructionMiddle_comp_cast n) _ ≪≫
      extendedRowMiddleIso E (initialFlag E F) (initialFlag_inflation E F) p hp r hr ≪≫
        completedInitialIso E F

/-- The initial part of the reconstructed Q-chain is canonically the original Q-chain. -/
def reconstructedInitialChainIso :
    Fin.castSuccFunctor (n + 1) ⋙
        ((rowChainComparison E ⦋n + 1⦌).obj (reconstructedRow E F p hp r hr)).of ≅
      ((rowChainComparison E ⦋n⦌).obj F).of :=
  eqToIso (by
    change Fin.castSuccFunctor (n + 1) ⋙ centralIntervalFunctor ⦋n + 1⦌ ⋙
      rowIntervalFunctor E (reconstructedRow E F p hp r hr) =
      centralIntervalFunctor ⦋n⦌ ⋙ rowIntervalFunctor E
        ((rowReindex E (reconstructionMiddleOrdinal n)).obj (reconstructedRow E F p hp r hr))
    rw [rowIntervalFunctor_reindex, ← Functor.assoc, ← reconstructionMiddle_centralFunctor]
    rfl) ≪≫
    Functor.isoWhiskerLeft (centralIntervalFunctor ⦋n⦌)
      (rowIntervalIso E (reconstructedMiddleIso E F p hp r hr))

/-- The explicit central object isomorphism, with the central-index equality first. -/
def reconstructedCentralIsoAt (i : Fin (n + 1)) :
    (reconstructedRow E F p hp r hr).diagram.obj
        (nestedToInterval (centralInterval ⦋n + 1⦌ i.castSucc)) ≅
      F.diagram.obj (nestedToInterval (centralInterval ⦋n⦌ i)) :=
  eqToIso (congrArg (fun q ↦ (reconstructedRow E F p hp r hr).diagram.obj
    (nestedToInterval q)) (reconstructionMiddleOrdinal_central n i).symm) ≪≫
      (reconstructedMiddleIso E F p hp r hr).app (nestedToInterval (centralInterval ⦋n⦌ i))

/-- The forward component is exactly the central-index cast followed by the
Q-isomorphism of the actual reconstructed middle-row isomorphism. -/
theorem reconstructedInitialChainIso_hom_app (i : Fin (n + 1)) :
    (reconstructedInitialChainIso E F p hp r hr).hom.app i =
      eqToHom (congrArg (fun q ↦ Q.of E.deflation E.inflation
        ((reconstructedRow E F p hp r hr).diagram.obj (nestedToInterval q)))
          (reconstructionMiddleOrdinal_central n i).symm) ≫
        (E.qIsoOfIso ((reconstructedMiddleIso E F p hp r hr).app
          (nestedToInterval (centralInterval ⦋n⦌ i)))).hom := by
  simp only [reconstructedInitialChainIso, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  rfl

private theorem qIsoOfIso_eqToIso {X Y : C} (h : X = Y) :
    E.qIsoOfIso (eqToIso h) = eqToIso (congrArg (Q.of E.deflation E.inflation) h) := by
  subst Y
  exact E.qIsoOfIso_refl X

/-- Equivalently, every component is induced by the displayed original-category isomorphism. -/
theorem reconstructedInitialChainIso_app (i : Fin (n + 1)) :
    (reconstructedInitialChainIso E F p hp r hr).app i =
      E.qIsoOfIso (reconstructedCentralIsoAt E F p hp r hr i) := by
  apply Iso.ext
  exact (reconstructedInitialChainIso_hom_app E F p hp r hr i).trans (by
    simp only [reconstructedCentralIsoAt,
      CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_trans, Iso.trans_hom,
      qIsoOfIso_eqToIso, eqToIso.hom])

/-- In particular the terminal component of the old subchain retains exactly
its original-category middle-row and central-index identifications. -/
theorem reconstructedInitialChainIso_app_last :
    (reconstructedInitialChainIso E F p hp r hr).app (Fin.last n) =
      E.qIsoOfIso (reconstructedCentralIsoAt E F p hp r hr (Fin.last n)) :=
  reconstructedInitialChainIso_app E F p hp r hr (Fin.last n)

end Quillen.Waldhausen.QuillenComparison
