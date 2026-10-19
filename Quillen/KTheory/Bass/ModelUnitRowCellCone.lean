/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelUnitRowCellNaturality
public import Quillen.KTheory.Bass.DiagramConeRowStrength
public import Quillen.KTheory.Bass.LoopConeTrack

/-! # Independent first-row cells through the first actual Bass cone

The four realized Model cells descend through the original square homotopy, then through the
specified inverse index map and the forward row strength. The independent construction retains
the original source null and every quotient height before comparison with the scalar action.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.FunctorIdentityAutomorphism
open scoped Topology unitInterval
universe u v w
namespace Quillen.KTheory.Bass.ModelUnitRowCellCone
open ModelDiagramRowInterchange NaturalTrack
variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L) (F : C ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (F.obj (L.obj X)) ≅ 𝟭 (F.obj (L.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (F.map (L.map g)).functor (unit X) (unit Y))

/-- The row diagram uses the actual initial Model transpose. -/
def refined := DiagramRowRefinement.diagram (F ⋙ prespectrumFunctor)
  (initial F) (initial_point F) (initial_naturality F)

/-- The unchanged original structure maps form the initial row comparison. -/
def comparison : F ⋙ prespectrumFunctor ⟶ refined F :=
  DiagramRowRefinement.comparison (F ⋙ prespectrumFunctor)
    (initial F) (initial_point F) (initial_naturality F) (initial_structure F)

/-- The actual cross-diagram coefficient arrow, before cone descent. -/
def input : F ⋙ prespectrumFunctor ⟶ L ⋙ refined F :=
  Functor.whiskerRight c (F ⋙ prespectrumFunctor) ≫ Functor.whiskerLeft L (comparison F)

/-- Four independently realized first-row cells on an arbitrary original square. -/
def squareCell (S : Arrow (Arrow C)) :=
  diagramSquareMapHomotopy (η := input L c F) (θ := input L c F)
    (initialCell L c F unit) (initialCell_naturality L c F unit hunit) S

variable (Q : C ⥤ Arrow (Arrow C))
  (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)

/-- Genuine square descent followed by the actual inverse index and forward row strength. -/
def coneCell (X : C) :=
  ((squareCell L c F unit hunit (Q.obj X)).cone).postcomp
    ((ConeTrack.indexMap Q L χ (refined F)).app X ≫
      DiagramConeRowStrength.strength Q (F ⋙ prespectrumFunctor)
        (initial F) (initial_point F) (initial_naturality F) (L.obj X))

/-- The independent descent retains the original source-null height and cell time. -/
theorem squareCell_sourceNull (S : Arrow (Arrow C)) (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (F.obj S.left.left)).space n) :
    (squareCell L c F unit hunit S).cone.level n
        (r, (StrictSquare.sourceNullHomotopy
          ((F ⋙ prespectrumFunctor).mapArrow.mapArrow.obj S)).level n (s, x)) =
      (StrictSquare.sourceNullHomotopy
        ((L ⋙ refined F).mapArrow.mapArrow.obj S)).level n
          (s, (initialCell L c F unit S.left.left).level n (r, x)) :=
  (squareCell L c F unit hunit S).sourceNull_apply n r s x

/-- The original source null passes through the index map and strength at its own height. -/
theorem coneCell_sourceNull (X : C) (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (F.obj (Q.obj X).left.left)).space n) :
    (coneCell L c F unit hunit Q χ X).level n
        (r, (StrictSquare.sourceNullHomotopy
          ((F ⋙ prespectrumFunctor).mapArrow.mapArrow.obj (Q.obj X))).level n (s, x)) =
      (DiagramConeRowStrength.strength Q (F ⋙ prespectrumFunctor)
        (initial F) (initial_point F) (initial_naturality F) (L.obj X)).map n
        ((StrictSquare.sourceNullHomotopy
          ((refined F).mapArrow.mapArrow.obj (Q.obj (L.obj X)))).level n
          (s, ((refined F).map (χ.inv.app X).left.left).map n
            ((initialCell L c F unit (Q.obj X).left.left).level n (r, x)))) := by
  have h := squareCell_sourceNull L c F unit hunit (Q.obj X) n r s x
  have hm := congrArg (fun z => ((ConeTrack.indexMap Q L χ (refined F)).app X).map n z) h
  have hi := hm.trans (StrictSquare.sourceNullHomotopy_naturality_apply
    ((refined F).mapArrow.mapArrow.map (χ.inv.app X)) n s
      ((initialCell L c F unit (Q.obj X).left.left).level n (r, x)))
  exact congrArg (fun z => (DiagramConeRowStrength.strength Q (F ⋙ prespectrumFunctor)
    (initial F) (initial_point F) (initial_naturality F) (L.obj X)).map n z) hi

end Quillen.KTheory.Bass.ModelUnitRowCellCone
