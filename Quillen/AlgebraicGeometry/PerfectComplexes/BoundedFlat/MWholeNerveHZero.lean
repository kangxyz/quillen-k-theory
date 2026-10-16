/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveParameter
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNativeCube

/-!
# The entire original H0 face of the chosen Bass composition cube in the actual nerve

The unchanged 140-node scalar cube is lifted through its actual full-node nerve characteristic
map after a specified reference transport. Its entire initial face agrees with the original
31-node H0 characteristic map. The proof uses the six original ordered 7-simplex supports;
no global monotonicity of the enclosing labels or replacement of the chosen cube is used.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve

/-- A typed proof barrier for composition of reference transports on complete dependent nodes. -/
theorem reanchor_nodes_congr {V W : Model.{u}} {F₀ F₁ F₂ : V ⟶ W} {k l : ℕ}
    (e : F₀.functor ≅ F₁.functor) (e' : F₁.functor ≅ F₂.functor)
    (N : Fin (k + 1) → CommonReferenceNerve.Node F₁)
    (M : Fin (l + 1) → CommonReferenceNerve.Node F₂) (f : Fin (l + 1) → Fin (k + 1))
    (h : ∀ i, N (f i) = ModelSimplex.reanchorNodes e' M i) (i : Fin (l + 1)) :
    ModelSimplex.reanchorNodes e N (f i) = ModelSimplex.reanchorNodes (e ≪≫ e') M i := by
  change (⟨(N (f i)).1, e ≪≫ (N (f i)).2⟩ : CommonReferenceNerve.Node F₀) = _
  rw [h i]
  simp only [ModelSimplex.reanchorNodes, Iso.trans_assoc]

/-- The identity reference transport retains the exact complete node list. -/
theorem reanchor_nodes_refl {V W : Model.{u}} {F : V ⟶ W} {k : ℕ}
    (N : Fin (k + 1) → CommonReferenceNerve.Node F) :
    ModelSimplex.reanchorNodes (Iso.refl F.functor) N = N := by
  funext i
  simp only [ModelSimplex.reanchorNodes, Iso.refl_trans]

/-- The three original full-node inclusions, without a global order assertion. -/
def h0Index : Fin 31 → Fin 140 :=
  BassMWholeOrder.oldIndex ∘ BassH1Order.oldIndex ∘ BassSupportOrder.h0Index

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Every complete original H0 node survives the three existing reference-node joins. -/
theorem h0_nodes (i : Fin 31) :
    BassMWhole.nodes P u v (h0Index i) = BassH0Merge.nodes P u v i := by
  unfold h0Index
  rw [Function.comp_apply, Function.comp_apply, BassMWhole.old_nodes,
    BassH1Merged.old_nodes, BassH0Merged.h0_nodes]

/-- The original entire scalar H0 parameter is exactly its three unchanged affine relabelings. -/
theorem h0_parameter_scalar (s t : unitInterval) :
    BassMWhole.h0Parameter (s, t) = StdSimplex.map h0Index (BassH0Diagram.parameter (s, t)) := by
  change StdSimplex.map BassMWholeOrder.oldIndex
    (StdSimplex.map BassH1Order.oldIndex
      (StdSimplex.map BassSupportOrder.h0Index (BassH0Diagram.parameter (s, t)))) = _
  rw [← StdSimplex.map_comp, ← StdSimplex.map_comp]
  rfl

variable (F : modelOf (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
    modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj c))))
  (e : F.functor ≅ (BassOverlap.commonReference P u v).functor)

/-- Lift precisely the selected original scalarCube, with its original universe and all nodes. -/
def cubeLift : C(Quillen.SimplexCubeExtension.Cube,
    |nerve (Codiscrete (CommonReferenceNerve.Node F))|) :=
  (CommonReferenceNerve.parameter F (ModelSimplex.reanchorNodes e (BassMWhole.nodes P u v))).comp
    BassMWhole.scalarCube.{u}

/-- Reanchoring preserves the full H0 node, including its specified reference transformation. -/
theorem reanchored_h0_nodes (i : Fin 31) :
    ModelSimplex.reanchorNodes e (BassMWhole.nodes P u v) (h0Index i) =
      ModelSimplex.reanchorNodes (e ≪≫ eqToIso (BassH0Merge.reference_eq P u v))
        (BassH0Diagram.nodes P (u ≫ v)) i := by
  exact reanchor_nodes_congr e (eqToIso (BassH0Merge.reference_eq P u v))
    (BassMWhole.nodes P u v) (BassH0Diagram.nodes P (u ≫ v)) h0Index
    (h0_nodes P u v) i

/-- Every point of the H0 parameter is compared on one of its six actual ordered supports. -/
theorem h0_parameter (s t : unitInterval) :
    CommonReferenceNerve.parameter F (ModelSimplex.reanchorNodes e (BassMWhole.nodes P u v))
        (StdSimplex.map h0Index (BassH0Diagram.parameter (s, t))) =
      CommonReferenceNerve.parameter F
        (ModelSimplex.reanchorNodes (e ≪≫ eqToIso (BassH0Merge.reference_eq P u v))
          (BassH0Diagram.nodes P (u ≫ v))) (BassH0Diagram.parameter (s, t)) := by
  obtain ⟨α, hα, i, z, hz⟩ := BassPrimitiveSupport.h0_support (s, t)
  change StdSimplex.map (BassPrimitiveSupport.rectangleFace i ≫ α).toOrderHom z =
    BassH0Diagram.parameter (s, t) at hz
  have hm : Monotone (h0Index ∘ (BassPrimitiveSupport.rectangleFace i ≫ α).toOrderHom) := by
    rcases Set.mem_insert_iff.mp hα with hα | hα
    · subst α
      exact BassMWholeOrder.oldH0Plus_monotone i
    · have hα := Set.mem_singleton_iff.mp hα
      subst α
      exact BassMWholeOrder.oldH0Minus_monotone i
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported F _ _ h0Index
    (reanchored_h0_nodes P u v F e) (BassPrimitiveSupport.rectangleFace i ≫ α) hm z

/-- The entire starting face of the unchanged chosen cube is the specified reanchored H0 map. -/
theorem cubeLift_zero (s t : unitInterval) :
    cubeLift P u v F e ![0, s, t] =
      CommonReferenceNerve.parameter F
        (ModelSimplex.reanchorNodes (e ≪≫ eqToIso (BassH0Merge.reference_eq P u v))
          (BassH0Diagram.nodes P (u ≫ v))) (BassH0Diagram.parameter (s, t)) := by
  change CommonReferenceNerve.parameter F
    (ModelSimplex.reanchorNodes e (BassMWhole.nodes P u v))
      (BassMWhole.scalarCube.{u} ![0, s, t]) = _
  rw [BassMWhole.cube_zero, h0_parameter_scalar]
  exact h0_parameter P u v F e s t

/-- Every reanchored finite family still evaluates to the entire original native cube. -/
theorem reanchored_native_cube (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.prespectrumFamily F
        (ModelSimplex.reanchorNodes e (BassMWhole.nodes P u v)) n
        (BassMWhole.scalarCube.{u} ![r, s, t], x) =
      (BassMWhole.interiorCube P u v).level n (r, (s, (t, x))) := by
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  change prespectrumSimplexFamily (ModelSimplex.reanchorSimplex e (BassMWhole.nodes P u v)) n
    (BassMWhole.scalarCube.{u} ![r, s, t], x) = _
  rw [ModelSimplex.reanchorSimplex_eq]
  exact (BassMWhole.interiorCube_level P u v n r s t x).symm

/-- Canonical transport back to the exact original H0 reference, with no new reference choice. -/
def h0Anchor : (BassH0Diagram.reference P (u ≫ v)).functor ≅
    (BassOverlap.commonReference P u v).functor :=
  (eqToIso (BassH0Merge.reference_eq P u v)).symm

/-- The complete initial nerve face is literally the original 31-node H0 characteristic map. -/
theorem cubeLift_original_h0 (s t : unitInterval) :
    cubeLift P u v (BassH0Diagram.reference P (u ≫ v)) (h0Anchor P u v) ![0, s, t] =
      CommonReferenceNerve.parameter (BassH0Diagram.reference P (u ≫ v))
        (BassH0Diagram.nodes P (u ≫ v)) (BassH0Diagram.parameter (s, t)) := by
  rw [cubeLift_zero]
  simp only [h0Anchor, Iso.symm_self_id, reanchor_nodes_refl]

end Quillen.PerfectComplexes.BassMWholeNerve
