/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Group.StableElementary
public import Mathlib.GroupTheory.PresentedGroup

/-!
# The stable Steinberg presentation over a field

The generators are actual finite-rank root data `(n, i, j, a)`, with distinct
`i j : Fin n`. We quotient their free group by root addition, the disjoint-root
commutator relation, the ordered chain relation, and explicit one-coordinate
stabilization. This finite-rank-labelled presentation is the definition used here;
no identification with a separate countably indexed presentation or an abstract
filtered colimit is asserted.

The canonical homomorphism sends each generator to the existing stable image of
its literal finite elementary matrix. Its corestriction is onto the actual
`StableGeneralLinear.elementary F`, using that subgroup's original closure
of all finite elementary matrices. The presented group is perfect: after actual
stabilization, a newly adjoined coordinate expresses each root generator as a
commutator. In particular, low finite ranks are handled by stabilization.

All results hold for every field, including fields with two or three elements.
This module identifies no kernel, proves no centrality or universal central
extension property, and supplies no comparison with Quillen K2.
-/
@[expose] public section

noncomputable section

universe u

namespace Quillen.StableSteinberg

open scoped commutatorElement

variable (F : Type u) [Field F]

/-- An off-diagonal root and its coefficient at an actual finite rank. -/
structure Generator where
  /-- The finite rank at which the root is represented. -/
  rank : ℕ
  /-- The row index in that finite rank. -/
  row : Fin rank
  /-- The column index in that finite rank. -/
  col : Fin rank
  /-- The root is off the diagonal. -/
  ne : row ≠ col
  /-- The field coefficient of the root. -/
  entry : F

/-- The corresponding formal generator in the free group of all finite root data. -/
def word (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) : FreeGroup (Generator F) :=
  FreeGroup.of ⟨n, i, j, hij, a⟩

/-- The finite Steinberg relators and explicit one-coordinate stabilization relators. -/
inductive Relator : FreeGroup (Generator F) → Prop
  /-- The additive root relation, written as a word equal to one. -/
  | rootAdd (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a b : F) :
      Relator (word F n i j hij a * word F n i j hij b *
        (word F n i j hij (a + b))⁻¹)
  /-- The commutator vanishes when the two roots have no interacting indices. -/
  | disjoint (n : ℕ) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
      (hjk : j ≠ k) (hli : l ≠ i) (a b : F) :
      Relator ⁅word F n i j hij a, word F n k l hkl b⁆
  /-- The ordered chain commutator has coefficient `a * b`. -/
  | chain (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (a b : F) :
      Relator (⁅word F n i j hij a, word F n j k hjk b⁆ *
        (word F n i k hik (a * b))⁻¹)
  /-- A finite root is identified with its standard next-rank stabilization. -/
  | stabilize (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
      Relator (word F n i j hij a *
        (word F (n + 1) i.castSucc j.castSucc (by simpa using hij) a)⁻¹)

/-- The actual set of words imposed as relators in the free group. -/
def relations : Set (FreeGroup (Generator F)) := {r | Relator F r}

/-- The stable Steinberg group in the finite-rank-labelled presentation. -/
abbrev Group := PresentedGroup (relations F)

/-- The root generator at an actual finite rank in the stable Steinberg group. -/
def x (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) : Group F :=
  PresentedGroup.of ⟨n, i, j, hij, a⟩

/-- Addition in one root is multiplication of its presented generators. -/
lemma x_add (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a b : F) :
    x F n i j hij a * x F n i j hij b = x F n i j hij (a + b) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relations F)
    (Relator.rootAdd (F := F) n i j hij a b)
  simpa only [word, x, PresentedGroup.of, map_mul] using h

/-- Root generators with disjoint interacting indices commute. -/
lemma x_commute (n : ℕ) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : F) :
    Commute (x F n i j hij a) (x F n k l hkl b) := by
  apply commutatorElement_eq_one_iff_commute.mp
  have h := PresentedGroup.one_of_mem (rels := relations F)
    (Relator.disjoint (F := F) n i j k l hij hkl hjk hli a b)
  simpa only [word, x, PresentedGroup.of, map_commutatorElement] using h

/-- The ordered Steinberg chain relation in the presented group. -/
lemma x_commutator (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : F) :
    ⁅x F n i j hij a, x F n j k hjk b⁆ = x F n i k hik (a * b) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relations F)
    (Relator.chain (F := F) n i j k hij hjk hik a b)
  simpa only [word, x, PresentedGroup.of, map_commutatorElement] using h

/-- A root generator agrees with its actual next-rank stabilization. -/
lemma x_stabilize (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
    x F n i j hij a = x F (n + 1) i.castSucc j.castSucc (by simpa using hij) a := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Relator.stabilize (F := F) n i j hij a)

/-- The root generator with coefficient zero is the identity. -/
lemma x_zero (n : ℕ) (i j : Fin n) (hij : i ≠ j) : x F n i j hij 0 = 1 := by
  apply mul_left_cancel (a := x F n i j hij 0)
  simpa only [zero_add, mul_one] using x_add F n i j hij 0 0

/-- Every root generator is a commutator after adjoining one actual coordinate. -/
lemma x_eq_commutator_succ (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
    x F n i j hij a =
      ⁅x F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) a,
        x F (n + 1) (Fin.last n) j.castSucc (Fin.castSucc_ne_last j).symm 1⁆ := by
  rw [x_commutator F (n + 1) i.castSucc (Fin.last n) j.castSucc
    (Fin.castSucc_ne_last i) (Fin.castSucc_ne_last j).symm (by simpa using hij), mul_one]
  exact x_stabilize F n i j hij a

/-- The stable Steinberg presentation is perfect over every field. -/
instance isPerfect : _root_.Group.IsPerfect (Group F) where
  commutator_eq_top := by
    apply top_unique
    intro g _
    apply PresentedGroup.generated_by (relations F) (commutator (Group F)) _ g
    rintro ⟨n, i, j, hij, a⟩
    change x F n i j hij a ∈ commutator (Group F)
    rw [x_eq_commutator_succ]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- A finite root datum maps to its literal elementary matrix in the actual stable GL group. -/
def matrixGenerator (g : Generator F) : StableGeneralLinear.Group F :=
  StableGeneralLinear.of F g.rank (ElementaryMatrix.unit g.row g.col g.ne g.entry)

/-- The existing elementary-matrix identities kill every defining relator. -/
lemma lift_relations (r : FreeGroup (Generator F)) (hr : r ∈ relations F) :
    FreeGroup.lift (matrixGenerator F) r = 1 := by
  cases hr with
  | rootAdd n i j hij a b =>
      simp only [map_mul, map_inv, word, FreeGroup.lift_apply_of, matrixGenerator]
      rw [← map_mul, ElementaryMatrix.unit_mul_same]
      exact mul_inv_cancel _
  | disjoint n i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, word, FreeGroup.lift_apply_of, matrixGenerator]
      rw [← map_commutatorElement]
      exact (congrArg (StableGeneralLinear.of F n)
        (commutatorElement_eq_one_iff_commute.mpr
          (ElementaryMatrix.unit_commute i j k l hij hkl hjk hli a b))).trans (map_one _)
  | chain n i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, word, FreeGroup.lift_apply_of,
        matrixGenerator]
      rw [← map_commutatorElement, ElementaryMatrix.unit_commutator]
      exact mul_inv_cancel _
  | stabilize n i j hij a =>
      simp only [map_mul, map_inv, word, FreeGroup.lift_apply_of, matrixGenerator]
      rw [StableGeneralLinear.of_unit_succ]
      exact mul_inv_cancel _


/-- The canonical homomorphism to the actual stable general linear group. -/
def toStableGeneralLinear : Group F →* StableGeneralLinear.Group F :=
  PresentedGroup.toGroup (lift_relations F)

/-- The canonical map retains the original finite elementary-matrix formula. -/
@[simp] lemma toStableGeneralLinear_x (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
    toStableGeneralLinear F (x F n i j hij a) =
      StableGeneralLinear.of F n (ElementaryMatrix.unit i j hij a) :=
  PresentedGroup.toGroup.of _

/-- The image lies in the original subgroup generated by stable elementary matrices. -/
lemma toStableGeneralLinear_mem_elementary (g : Group F) :
    toStableGeneralLinear F g ∈ StableGeneralLinear.elementary F := by
  apply PresentedGroup.generated_by (relations F)
    ((StableGeneralLinear.elementary F).comap (toStableGeneralLinear F)) _ g
  rintro ⟨n, i, j, hij, a⟩
  change toStableGeneralLinear F (x F n i j hij a) ∈ StableGeneralLinear.elementary F
  rw [toStableGeneralLinear_x]
  exact StableGeneralLinear.unit_mem_elementary F n i j hij a

/-- The canonical homomorphism into the actual stable elementary subgroup. -/
def toElementary : Group F →* StableGeneralLinear.elementary F where
  toFun g := ⟨toStableGeneralLinear F g, toStableGeneralLinear_mem_elementary F g⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

/-- The corestriction retains the same literal finite elementary matrix. -/
@[simp] lemma toElementary_x (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
    toElementary F (x F n i j hij a) =
      ⟨StableGeneralLinear.of F n (ElementaryMatrix.unit i j hij a),
        StableGeneralLinear.unit_mem_elementary F n i j hij a⟩ := by
  apply Subtype.ext
  exact toStableGeneralLinear_x F n i j hij a

/-- The presented Steinberg group maps onto the actual stable elementary subgroup. -/
lemma toElementary_surjective : Function.Surjective (toElementary F) := by
  have hle : StableGeneralLinear.elementary F ≤ (toStableGeneralLinear F).range := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨n, i, j, hij, a, rfl⟩
    exact ⟨x F n i j hij a, toStableGeneralLinear_x F n i j hij a⟩
  intro g
  obtain ⟨a, ha⟩ := hle g.property
  exact ⟨a, Subtype.ext ha⟩

end Quillen.StableSteinberg
