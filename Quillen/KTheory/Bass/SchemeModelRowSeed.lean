/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeRowSeed
public import Quillen.KTheory.Bass.ModelUnitRowCellIteration
public import Quillen.KTheory.Bass.ModelRowZigzagSequentialization
public import Quillen.KTheory.Bass.ModelRowBackwardNaturality
public import Quillen.KTheory.Bass.SchemeCurrentStageTelescope

/-!
# Genuine Model-unit forward seeds at every original scheme Bass stage

The forward seed is formed from the independently iterated cell and original
cone null. Its whole map equals the original current transition followed by
the proper-row backward leg, with the original successor casts retained.
-/
@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace Quillen.KTheory.Bass.SchemeModelRowSeed
open GeometricSeedCospan NaturalTrack GeometricSquareInterchange ModelDiagramRowInterchange
variable (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)) ≅ 𝟭 (M.obj (laurent.op.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).functor (unit X) (unit Y))

/-- The actual independently iterated cell at the original scheme Bass stage. -/
abbrev cell (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  iteratedCell laurent.op coefficient M unit hunit squareFunctor
    (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ))))
    (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ)))) i X

/-- The forward map is constructed from the independent cell and original whole source null. -/
def forward (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor)).obj X) ⟶
      ModelDiagramRowStabilizedTarget.target squareFunctor i M X :=
  SchemeRowSeed.seed ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor))
    (stage squareFunctor M i) (stage_point squareFunctor M i)
    (stage_naturality squareFunctor M i) (stage_structure squareFunctor M i)
    X (cell M unit hunit i X)

/-- The whole independently constructed cell has the original current-track comparison. -/
theorem cell_eq (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    cell M unit hunit i X =
      ((SchemeNaturalSeed.stageTrack
        (ofModelUnits laurent.op coefficient M unit hunit) i).homotopy X).postcomp
        ((DiagramRowRefinement.comparison
          ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor))
          (stage squareFunctor M i) (stage_point squareFunctor M i)
          (stage_naturality squareFunctor M i) (stage_structure squareFunctor M i)).app
          (laurent.op.obj X)) := by
  apply Quillen.LoopPrespectrum.Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨t, x⟩
  exact congrArg (fun f => f.map n x)
    (iteratedCell_at_eq laurent.op coefficient M unit hunit squareFunctor
      (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
        (.of (ULift.{u} ℤ))))
      (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
        (.of (ULift.{u} ℤ)))) i X t)

/-- The same forward map agrees with the original current seed through the actual row map. -/
theorem forward_eq_seed (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    forward M unit hunit i X =
      (SchemeNaturalSeed.seed
        (SchemeNaturalSeed.stageTrack (ofModelUnits laurent.op coefficient M unit hunit) i)).app X ≫
      parameterLoopingMap (ModelDiagramRowRefinement.comparison squareFunctor i M X) :=
  SchemeRowSeed.seed_eq _ _ _ _ _ _ _ _ (cell_eq M unit hunit i X)

private theorem insert_successor_transport {E B B' D : LoopPrespectrum.{w}}
    (h : B' = B) (f : E ⟶ B) (g : B ⟶ D) :
    f ≫ g = (f ≫ eqToHom h.symm) ≫ (eqToHom h ≫ g) := by
  subst B'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- The independently formed forward leg has the exact original current-transition factorization. -/
theorem forward_eq_current (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    forward M unit hunit i X =
      (SchemeNaturalSeed.currentTransition
        (ofModelUnits laurent.op coefficient M unit hunit) i).app X ≫
        ModelRowZigzagSequentialization.backward squareFunctor M X i := by
  rw [forward_eq_seed, ModelRowZigzagSequentialization.backward_eq]
  simp only [SchemeNaturalSeed.currentTransition, NatTrans.comp_app, eqToHom_app]
  exact insert_successor_transport (ModelDiagramSuspension.successor_obj squareFunctor i M X)
    ((SchemeNaturalSeed.seed
      (SchemeNaturalSeed.stageTrack (ofModelUnits laurent.op coefficient M unit hunit) i)).app X)
    (parameterLoopingMap (ModelDiagramRowRefinement.comparison squareFunctor i M X))

/-- Coefficient naturality is proved for the independent forward maps at every actual stage. -/
theorem forward_naturality (i : ℕ) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor)).map g ≫
      forward M unit hunit i Y =
    forward M unit hunit i X ≫
      (ModelDiagramRowStabilizedTarget.targetDiagram squareFunctor i M).map g := by
  let T := SchemeNaturalSeed.currentTransition
    (ofModelUnits laurent.op coefficient M unit hunit) i ≫
      ModelRowZigzagSequentialization.backwardNatTrans squareFunctor M i
  have hT (Z : Scheme.{u}ᵒᵖ) : T.app Z = forward M unit hunit i Z := by
    change (SchemeNaturalSeed.currentTransition
      (ofModelUnits laurent.op coefficient M unit hunit) i).app Z ≫
        (ModelRowZigzagSequentialization.backwardNatTrans squareFunctor M i).app Z = _
    rw [ModelRowZigzagSequentialization.backwardNatTrans_app]
    exact (forward_eq_current M unit hunit i Z).symm
  have h := T.naturality g
  rw [hT, hT] at h
  exact h

/-- The components remain the independently constructed forward cells. -/
def forwardNatTrans (i : ℕ) :
    (strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor) ⟶
      ModelDiagramRowStabilizedTarget.targetDiagram squareFunctor i M where
  app X := forward M unit hunit i X
  naturality _ _ := forward_naturality M unit hunit i

/-- This whole factorization is proved after constructing the independent forward leg. -/
def factorization (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    Quillen.LoopPrespectrum.Homotopy (forward M unit hunit i X)
      ((SchemeNaturalSeed.currentTransition
        (ofModelUnits laurent.op coefficient M unit hunit) i).app X ≫
        ModelRowZigzagSequentialization.backward squareFunctor M X i) :=
  (Quillen.LoopPrespectrum.Homotopy.refl (forward M unit hunit i X)).cast rfl
    (forward_eq_current M unit hunit i X)

/-- The proper-row presentation uses the independent forward cells and original backward legs. -/
def presentation (X : Scheme.{u}ᵒᵖ) : LoopPrespectrum.{w} :=
  Telescope.prespectrum
    (ZigzagSequentialization.stage
      (ModelRowZigzagSequentialization.vertex squareFunctor M X)
      (ModelRowZigzagSequentialization.target squareFunctor M X)
      (fun i => forward M unit hunit i X)
      (ModelRowZigzagSequentialization.backward squareFunctor M X))
    (ZigzagSequentialization.transition
      (ModelRowZigzagSequentialization.vertex squareFunctor M X)
      (ModelRowZigzagSequentialization.target squareFunctor M X)
      (fun i => forward M unit hunit i X)
      (ModelRowZigzagSequentialization.backward squareFunctor M X))

/-- The genuine original current telescope maps to the independent-cell row presentation. -/
def comparison (X : Scheme.{u}ᵒᵖ) :
    (SchemeNaturalSeed.currentTelescope
      (ofModelUnits laurent.op coefficient M unit hunit)).obj X ⟶
        presentation M unit hunit X :=
  ZigzagSequentialization.telescopeMap
      (ModelRowZigzagSequentialization.vertex squareFunctor M X)
      (ModelRowZigzagSequentialization.target squareFunctor M X)
      (fun i => forward M unit hunit i X)
      (ModelRowZigzagSequentialization.backward squareFunctor M X)
      (fun i => (SchemeNaturalSeed.currentTransition
        (ofModelUnits laurent.op coefficient M unit hunit) i).app X)
      (fun i => factorization M unit hunit i X)

/-- Actual finite growth proves the independent-cell presentation comparison stable. -/
theorem comparison_stable (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (comparison M unit hunit X) :=
  ModelRowZigzagSequentialization.telescopeMap_stable squareFunctor M X
    (fun i => forward M unit hunit i X)
    (fun i => (SchemeNaturalSeed.currentTransition
      (ofModelUnits laurent.op coefficient M unit hunit) i).app X)
    (fun i => factorization M unit hunit i X)

end Quillen.KTheory.Bass.SchemeModelRowSeed
