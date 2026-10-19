/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexWeakPrependLift
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerve
public import Quillen.Waldhausen.SConstruction.Iterated.DiagramZeroNull

/-!
# The original weak zero edge beside a finite full-reference family

The zero vertex is adjoined by the selected objectwise weak transformation. It is never a
common-reference isomorphism node. The original reference is retained separately, so the marked
edge recovers the chosen null and every old full-reference simplex is an unchanged whole face.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceWeakZero
open CommonReferenceNerve ModelSimplex
variable {V W : Model.{u}} (F : V ⟶ W) {k : ℕ} (N : Fin (k + 1) → Node F)

/-- The selected original reference is retained before every supplied full dependent node. -/
def nodes : Fin (k + 2) → Node F := Fin.cases ⟨F, Iso.refl _⟩ N

/-- The normalization chain includes the actual reference, with its identity anchor. -/
def normalizationSimplex : ModelSimplex V W (k + 1) :=
  ofIsos F (fun i ↦ (nodes F N i).1) (fun i ↦ (nodes F N i).2)

/-- The whole original full-node chain remains an exact ordered face. -/
theorem normalization_face :
    (normalizationSimplex F N).face tailFace =
      ofIsos F (fun i ↦ (N i).1) (fun i ↦ (N i).2) := by
  apply ext_diagram
  rfl

variable (η : (zeroHom V W).functor ⟶ F.functor)
  (hη : ∀ X, W.waldhausen.weq (η.app X))

/-- A directed simplex retaining the original zero-to-reference arrow. -/
def simplex : ModelSimplex V W (k + 2) :=
  prependWeak (normalizationSimplex F N) η hη

/-- The complete normalization family, with all anchors, is unchanged. -/
theorem normalization_native (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (simplex F N η hη) n
      (StdSimplex.map Fin.succ (StdSimplex.map Fin.succ z), x) =
        prespectrumFamily F N n (z, x) := by
  rw [prespectrumFamily_eq]
  change prespectrumSimplexFamily (prependWeak (normalizationSimplex F N) η hη) n
    (StdSimplex.map Fin.succ (StdSimplex.map Fin.succ z), x) = _
  rw [prependWeak_tail_native]
  change prespectrumSimplexFamily (normalizationSimplex F N) n
    (StdSimplex.map tailFace.toOrderHom z, x) = _
  rw [prespectrumSimplexFamily_face, normalization_face]

/-- The marked edge recovers every time of the selected weak transformation. -/
theorem edge_native :
    PathLift (simplex F N η hη) (edge 0 1)
      (prespectrumTransformationHomotopy η hη) :=
  prependWeak_edge_native (normalizationSimplex F N) η hη

/-- The original null is the same marked edge in the original reversed time. -/
theorem reverse_native (n : ℕ) (r : unitInterval) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (simplex F N η hη) n
      ((edge (k := k + 2) 0 1).symm r, x) =
        (prespectrumTransformationHomotopy η hη).level n (unitInterval.symm r, x) :=
  edge_native F N η hη n (unitInterval.symm r) x

/-- The actual composite null, including its endpoint transports, is retained in full. -/
theorem compositeNull_native {T : Model.{u}} (f : V ⟶ T) (g : T ⟶ W)
    (N : Fin (k + 1) → Node (f ≫ g))
    (η : (zeroHom V W).functor ⟶ (f ≫ g).functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (n : ℕ) (r : unitInterval) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (simplex (f ≫ g) N η hη) n
      ((edge (k := k + 2) 0 1).symm r, x) =
        (prespectrumCompositeZeroNullHomotopy f g η hη).level n (r, x) :=
  reverse_native (f ≫ g) N η hη n r x

end Quillen.Waldhausen.IteratedS.CommonReferenceWeakZero
