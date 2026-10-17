/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.ParameterizedDescent
public import Quillen.Topology.Prespectrum.ParameterLooping

/-!
# Families on the original cone of a homotopy-pushout comparison

The input consists of four typed native cell families: Laurent inputs, two polynomial
cylinders, and the overlap cylinder. Only their actual quotient attachments, based values,
and independent structure laws are required. First the original pushout is descended and
then its original reduced cone. Parameter restrictions commute strictly with both descents.
The intended application is the whole Raw1 projection pasting; no such pasting is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u v w
namespace Quillen.LoopPrespectrum

variable {T : Type v} [TopologicalSpace T]
variable {A B C L Y : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
  (c : HomotopyPushout.prespectrum f g ⟶ L)

/-- Actual cell families and exactly the attachment laws of the two original quotients.
The parameter precedes cone height, overlap time, and the actual native input. -/
structure PushoutConeFamily (T : Type v) [TopologicalSpace T]
    {A B C L : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
    (c : HomotopyPushout.prespectrum f g ⟶ L) (Y : LoopPrespectrum.{u}) where
  /-- The full Laurent summand. -/
  laurent (n : ℕ) : C(T × L.space n, Y.space n)
  /-- The positive polynomial cylinder. -/
  plus (n : ℕ) : C(T × (unitInterval × B.space n), Y.space n)
  /-- The negative polynomial cylinder. -/
  minus (n : ℕ) : C(T × (unitInterval × C.space n), Y.space n)
  /-- The entire overlap, with height before overlap time. -/
  overlap (n : ℕ) : C(T × (unitInterval × (unitInterval × A.space n)), Y.space n)
  overlap_zero (n : ℕ) (t : T) (h : unitInterval) (x : A.space n) :
    overlap n (t, (h, (0, x))) = plus n (t, (h, f.map n x))
  overlap_one (n : ℕ) (t : T) (h : unitInterval) (x : A.space n) :
    overlap n (t, (h, (1, x))) = minus n (t, (h, g.map n x))
  overlap_base (n : ℕ) (t : T) (h s : unitInterval) :
    overlap n (t, (h, (s, A.point n))) = plus n (t, (h, B.point n))
  plus_zero (n : ℕ) (t : T) (x : B.space n) :
    plus n (t, (0, x)) = laurent n (t, c.map n ((HomotopyPushout.inl f g).map n x))
  minus_zero (n : ℕ) (t : T) (x : C.space n) :
    minus n (t, (0, x)) = laurent n (t, c.map n ((HomotopyPushout.inr f g).map n x))
  overlap_height_zero (n : ℕ) (t : T) (s : unitInterval) (x : A.space n) :
    overlap n (t, (0, (s, x))) =
      laurent n (t, c.map n (HomotopyPushout.cylinder f g n (s, x)))
  plus_one (n : ℕ) (t : T) (x : B.space n) : plus n (t, (1, x)) = Y.point n
  minus_one (n : ℕ) (t : T) (x : C.space n) : minus n (t, (1, x)) = Y.point n
  overlap_height_one (n : ℕ) (t : T) (s : unitInterval) (x : A.space n) :
    overlap n (t, (1, (s, x))) = Y.point n
  laurent_point (n : ℕ) (t : T) : laurent n (t, L.point n) = Y.point n
  plus_point (n : ℕ) (t : T) (h : unitInterval) : plus n (t, (h, B.point n)) = Y.point n
  laurent_structure (n : ℕ) (t : T) (x : L.space n) (z : unitInterval) :
    laurent (n + 1) (t, L.structureMap n x z) = Y.structureMap n (laurent n (t, x)) z
  plus_structure (n : ℕ) (t : T) (h : unitInterval) (x : B.space n) (z : unitInterval) :
    plus (n + 1) (t, (h, B.structureMap n x z)) = Y.structureMap n (plus n (t, (h, x))) z
  minus_structure (n : ℕ) (t : T) (h : unitInterval) (x : C.space n) (z : unitInterval) :
    minus (n + 1) (t, (h, C.structureMap n x z)) = Y.structureMap n (minus n (t, (h, x))) z
  overlap_structure (n : ℕ) (t : T) (h s : unitInterval) (x : A.space n) (z : unitInterval) :
    overlap (n + 1) (t, (h, (s, A.structureMap n x z))) =
      Y.structureMap n (overlap n (t, (h, (s, x)))) z

namespace PushoutConeFamily
variable {f g c} (F : PushoutConeFamily T f g c Y)

/-- The second polynomial based law follows from the original overlap attachment. -/
theorem minus_point (n : ℕ) (t : T) (h : unitInterval) :
    F.minus n (t, (h, C.point n)) = Y.point n := by
  rw [← g.map_point n, ← F.overlap_one, F.overlap_base, F.plus_point]

variable [LocallyCompactSpace T]

/-- Descend the overlap at every original cone height, without identifying the parameters. -/
def inner (n : ℕ) : C(T × (unitInterval × (HomotopyPushout.prespectrum f g).space n), Y.space n) :=
  (HomotopyPushout.parameterDesc f g n
    ⟨fun z : (T × unitInterval) × B.space n ↦ F.plus n (z.1.1, (z.1.2, z.2)), by fun_prop⟩
    ⟨fun z : (T × unitInterval) × C.space n ↦ F.minus n (z.1.1, (z.1.2, z.2)), by fun_prop⟩
    ⟨fun z : (T × unitInterval) × (unitInterval × A.space n) ↦
      F.overlap n (z.1.1, (z.1.2, z.2)), by fun_prop⟩
    (fun t x ↦ F.overlap_zero n t.1 t.2 x)
    (fun t x ↦ F.overlap_one n t.1 t.2 x)
    (fun t s ↦ F.overlap_base n t.1 t.2 s)).comp
      ⟨fun z ↦ ((z.1, z.2.1), z.2.2), by fun_prop⟩

/-- The first polynomial cell survives the inner quotient. -/
@[simp] theorem inner_inl (n : ℕ) (t : T) (h : unitInterval) (x : B.space n) :
    F.inner n (t, (h, (HomotopyPushout.inl f g).map n x)) = F.plus n (t, (h, x)) := rfl

/-- The second polynomial cell survives the inner quotient. -/
@[simp] theorem inner_inr (n : ℕ) (t : T) (h : unitInterval) (x : C.space n) :
    F.inner n (t, (h, (HomotopyPushout.inr f g).map n x)) = F.minus n (t, (h, x)) := rfl

/-- All four parameters and inputs of the overlap are retained. -/
@[simp] theorem inner_cylinder (n : ℕ) (t : T) (h s : unitInterval) (x : A.space n) :
    F.inner n (t, (h, HomotopyPushout.cylinder f g n (s, x))) =
      F.overlap n (t, (h, (s, x))) := rfl

/-- The complete height-zero face is the original comparison followed by the Laurent family. -/
theorem inner_zero (n : ℕ) (t : T) (x : (HomotopyPushout.prespectrum f g).space n) :
    F.inner n (t, (0, x)) = F.laurent n (t, c.map n x) := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl x => exact F.plus_zero n t x
      | inr x => exact F.minus_zero n t x
    | inr z => exact F.overlap_height_zero n t z.1 z.2

/-- The entire terminal height face has the original target basepoint. -/
theorem inner_one (n : ℕ) (t : T) (x : (HomotopyPushout.prespectrum f g).space n) :
    F.inner n (t, (1, x)) = Y.point n := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl x => exact F.plus_one n t x
      | inr x => exact F.minus_one n t x
    | inr z => exact F.overlap_height_one n t z.1 z.2

/-- The inner family is based at every independent height. -/
theorem inner_point (n : ℕ) (t : T) (h : unitInterval) :
    F.inner n (t, (h, (HomotopyPushout.prespectrum f g).point n)) = Y.point n :=
  F.plus_point n t h

/-- The inner quotient preserves the independently quantified structure coordinate. -/
theorem inner_structure (n : ℕ) (t : T) (h : unitInterval)
    (x : (HomotopyPushout.prespectrum f g).space n) (z : unitInterval) :
    F.inner (n + 1) (t, (h, (HomotopyPushout.prespectrum f g).structureMap n x z)) =
      Y.structureMap n (F.inner n (t, (h, x))) z := by
  induction x using Quot.inductionOn with
  | h x => cases x with
    | inl x => cases x with
      | inl x => exact F.plus_structure n t h x z
      | inr x => exact F.minus_structure n t h x z
    | inr x => exact F.overlap_structure n t h x.1 x.2 z

/-- The full family on the original double quotient, in the original order. -/
def desc (n : ℕ) : C(T × (mappingCone c).space n, Y.space n) :=
  mappingConeParameterDesc c n (F.laurent n) (F.inner n)
    (F.inner_zero n)
    (fun t x ↦ (F.inner_one n t x).trans (F.laurent_point n t).symm)
    (fun t h ↦ (F.inner_point n t h).trans (F.laurent_point n t).symm)

/-- The original Laurent summand is unchanged after both descents. -/
@[simp] theorem desc_inclusion (n : ℕ) (t : T) (x : L.space n) :
    F.desc n (t, (mappingConeInclusion c).map n x) = F.laurent n (t, x) := rfl

/-- The original cone cylinder is exactly the descended inner family. -/
@[simp] theorem desc_cylinder (n : ℕ) (t : T) (h : unitInterval)
    (x : (HomotopyPushout.prespectrum f g).space n) :
    F.desc n (t, (mappingConeHomotopy c).level n (h, x)) = F.inner n (t, (h, x)) := rfl

/-- Every parameter value preserves the original native basepoint. -/
theorem desc_point (n : ℕ) (t : T) :
    F.desc n (t, (mappingCone c).point n) = Y.point n := F.laurent_point n t

/-- The structure time is independent of the full parameter and both quotient coordinates. -/
theorem desc_structure (n : ℕ) (t : T) (x : (mappingCone c).space n) (z : unitInterval) :
    F.desc (n + 1) (t, (mappingCone c).structureMap n x z) =
      Y.structureMap n (F.desc n (t, x)) z := by
  induction x using Quot.inductionOn with
  | h x => cases x with
    | inl x => exact F.laurent_structure n t x z
    | inr x => exact F.inner_structure n t x.1 x.2 z

/-- Each parameter slice is an actual morphism of the original prespectra. -/
def «at» (t : T) : mappingCone c ⟶ Y where
  map n := ⟨fun x ↦ F.desc n (t, x), by fun_prop⟩
  map_point n := F.desc_point n t
  comm n x := by
    apply Path.ext
    funext z
    exact F.desc_structure n t x z

/-- Restrict only the external parameter, retaining every original native cell and attachment. -/
def restrict {S : Type w} [TopologicalSpace S] (q : C(S, T)) :
    PushoutConeFamily S f g c Y where
  laurent n := (F.laurent n).comp (q.prodMap (.id _))
  plus n := (F.plus n).comp (q.prodMap (.id _))
  minus n := (F.minus n).comp (q.prodMap (.id _))
  overlap n := (F.overlap n).comp (q.prodMap (.id _))
  overlap_zero n t h x := F.overlap_zero n (q t) h x
  overlap_one n t h x := F.overlap_one n (q t) h x
  overlap_base n t h s := F.overlap_base n (q t) h s
  plus_zero n t x := F.plus_zero n (q t) x
  minus_zero n t x := F.minus_zero n (q t) x
  overlap_height_zero n t s x := F.overlap_height_zero n (q t) s x
  plus_one n t x := F.plus_one n (q t) x
  minus_one n t x := F.minus_one n (q t) x
  overlap_height_one n t s x := F.overlap_height_one n (q t) s x
  laurent_point n t := F.laurent_point n (q t)
  plus_point n t h := F.plus_point n (q t) h
  laurent_structure n t x z := F.laurent_structure n (q t) x z
  plus_structure n t h x z := F.plus_structure n (q t) h x z
  minus_structure n t h x z := F.minus_structure n (q t) h x z
  overlap_structure n t h s x z := F.overlap_structure n (q t) h s x z

/-- Every parameter restriction commutes strictly with the inner quotient. -/
theorem inner_restrict {S : Type w} [TopologicalSpace S] [LocallyCompactSpace S]
    (q : C(S, T)) (n : ℕ) (t : S) (h : unitInterval)
    (x : (HomotopyPushout.prespectrum f g).space n) :
    (F.restrict q).inner n (t, (h, x)) = F.inner n (q t, (h, x)) := by
  induction x using Quot.inductionOn with
  | h x => cases x with
    | inl x => cases x <;> rfl
    | inr x => rfl

/-- Every parameter restriction, hence every finite cube face, commutes with both quotients. -/
theorem desc_restrict {S : Type w} [TopologicalSpace S] [LocallyCompactSpace S]
    (q : C(S, T)) (n : ℕ) (t : S) (x : (mappingCone c).space n) :
    (F.restrict q).desc n (t, x) = F.desc n (q t, x) := by
  induction x using Quot.inductionOn with
  | h x => cases x with
    | inl x => rfl
    | inr x => exact F.inner_restrict q n t x.1 x.2

/-- The original positive polynomial cylinder survives the two quotients exactly. -/
@[simp] theorem desc_plus (n : ℕ) (t : T) (h : unitInterval) (x : B.space n) :
    F.desc n (t, (mappingConeHomotopy c).level n
      (h, (HomotopyPushout.inl f g).map n x)) = F.plus n (t, (h, x)) := rfl

/-- The original negative polynomial cylinder survives the two quotients exactly. -/
@[simp] theorem desc_minus (n : ℕ) (t : T) (h : unitInterval) (x : C.space n) :
    F.desc n (t, (mappingConeHomotopy c).level n
      (h, (HomotopyPushout.inr f g).map n x)) = F.minus n (t, (h, x)) := rfl

/-- The height and overlap parameters survive in their specified order. -/
@[simp] theorem desc_overlap (n : ℕ) (t : T) (h s : unitInterval) (x : A.space n) :
    F.desc n (t, (mappingConeHomotopy c).level n
      (h, HomotopyPushout.cylinder f g n (s, x))) = F.overlap n (t, (h, (s, x))) := rfl

/-- Joint parameter looping is performed only after both original quotients have descended. -/
def looped (n : ℕ) :
    C(T × (parameterLooping (mappingCone c)).space n, (parameterLooping Y).space n) := by
  change C(T × Path ((mappingCone c).point n) ((mappingCone c).point n),
    Path (Y.point n) (Y.point n))
  exact
    { toFun z :=
        { toFun s := F.desc n (z.1, z.2 s)
          continuous_toFun := by fun_prop
          source' := (congrArg (fun x ↦ F.desc n (z.1, x)) z.2.source).trans (F.desc_point n z.1)
          target' := (congrArg (fun x ↦ F.desc n (z.1, x)) z.2.target).trans (F.desc_point n z.1) }
      continuous_toFun := by
        apply Path.continuous_uncurry_iff.mp
        change Continuous (fun z :
          (T × Path ((mappingCone c).point n) ((mappingCone c).point n)) × unitInterval ↦
            F.desc n (z.1.1, z.1.2 z.2))
        fun_prop }

/-- The extra loop coordinate is independent of all supplied cell parameters. -/
theorem looped_apply (n : ℕ) (t : T) (x : (parameterLooping (mappingCone c)).space n)
    (s : unitInterval) :
    Path.toContinuousMap (F.looped n (t, x)) s = F.desc n (t, Path.toContinuousMap x s) := rfl

/-- Each looped slice is exactly the original parameter-looping map. -/
theorem looped_eq (n : ℕ) (t : T) (x : (parameterLooping (mappingCone c)).space n) :
    F.looped n (t, x) = (parameterLoopingMap (F.at t)).map n x := rfl

/-- Parameter looping preserves the original based point at every external parameter. -/
theorem looped_point (n : ℕ) (t : T) :
    F.looped n (t, (parameterLooping (mappingCone c)).point n) = (parameterLooping Y).point n := by
  apply Path.ext
  funext s
  exact F.desc_point n t

/-- Structure time remains separate from the external parameter and the loop coordinate. -/
theorem looped_structure (n : ℕ) (t : T) (x : (parameterLooping (mappingCone c)).space n)
    (z : unitInterval) :
    F.looped (n + 1) (t, (parameterLooping (mappingCone c)).structureMap n x z) =
      (parameterLooping Y).structureMap n (F.looped n (t, x)) z := by
  apply Path.ext
  funext s
  exact F.desc_structure n t (Path.toContinuousMap x s) z

/-- Whole cube-face restriction commutes with the final independent parameter looping. -/
theorem looped_restrict {S : Type w} [TopologicalSpace S] [LocallyCompactSpace S]
    (q : C(S, T)) (n : ℕ) (t : S) (x : (parameterLooping (mappingCone c)).space n) :
    (F.restrict q).looped n (t, x) = F.looped n (q t, x) := by
  apply Path.ext
  funext s
  exact F.desc_restrict q n t (Path.toContinuousMap x s)

end PushoutConeFamily
end Quillen.LoopPrespectrum
