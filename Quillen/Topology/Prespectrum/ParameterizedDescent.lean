/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.HomotopyPushout
public import Quillen.Topology.Prespectrum.MappingCone

/-!
# Parameterized descent through the original reduced quotients

Jointly continuous families descend through the original pushout and cone by currying
into the compact-open parameter mapping space. The parameter need only be locally compact;
in particular every finite cube is allowed. No separation or compactness of the native
input is required. The equations are precisely the original quotient relations.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u v w
namespace Quillen.LoopPrespectrum
variable {T : Type v} [TopologicalSpace T] [LocallyCompactSpace T]
variable {Z : Type w} [TopologicalSpace Z]

namespace HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C) (n : ℕ)
  (l : C(T × B.space n, Z)) (r : C(T × C.space n, Z))
  (o : C(T × (unitInterval × A.space n), Z))
  (h₀ : ∀ t x, o (t, (0, x)) = l (t, f.map n x))
  (h₁ : ∀ t x, o (t, (1, x)) = r (t, g.map n x))
  (hb : ∀ t s, o (t, (s, A.point n)) = l (t, B.point n))

/-- The original reduced pushout descends into the whole parameter mapping space. -/
def parameterDescCurried : C(Space f g n, C(T, Z)) where
  toFun := Quot.lift (Sum.elim (Sum.elim
    (ContinuousMap.curry ⟨fun z : B.space n × T ↦ l (z.2, z.1), by fun_prop⟩)
    (ContinuousMap.curry ⟨fun z : C.space n × T ↦ r (z.2, z.1), by fun_prop⟩))
    (ContinuousMap.curry ⟨fun z : (unitInterval × A.space n) × T ↦ o (z.2, z.1),
      by fun_prop⟩)) (by
    intro x y h
    cases h with
    | left x => ext t; exact h₀ t x
    | right x => ext t; exact h₁ t x
    | base s => ext t; exact hb t s)
  continuous_toFun := continuous_quot_lift _
    (((ContinuousMap.curry ⟨fun z : B.space n × T ↦ l (z.2, z.1), by fun_prop⟩).continuous.sumElim
      (ContinuousMap.curry ⟨fun z : C.space n × T ↦ r (z.2, z.1), by fun_prop⟩).continuous).sumElim
      (ContinuousMap.curry ⟨fun z : (unitInterval × A.space n) × T ↦ o (z.2, z.1),
        by fun_prop⟩).continuous)

/-- Evaluate the parameter only after descent through the original quotient. -/
def parameterDesc : C(T × Space f g n, Z) :=
  ⟨fun z ↦ parameterDescCurried f g n l r o h₀ h₁ hb z.2 z.1,
    (parameterDescCurried f g n l r o h₀ h₁ hb).uncurry.continuous.comp continuous_swap⟩

/-- The entire left family is unchanged. -/
@[simp] theorem parameterDesc_left (t : T) (x : B.space n) :
    parameterDesc f g n l r o h₀ h₁ hb (t, left f g n x) = l (t, x) := rfl

/-- The entire right family is unchanged. -/
@[simp] theorem parameterDesc_right (t : T) (x : C.space n) :
    parameterDesc f g n l r o h₀ h₁ hb (t, right f g n x) = r (t, x) := rfl

/-- The overlap coordinate is retained independently of the parameter. -/
@[simp] theorem parameterDesc_cylinder (t : T) (s : unitInterval) (x : A.space n) :
    parameterDesc f g n l r o h₀ h₁ hb (t, cylinder f g n (s, x)) = o (t, (s, x)) := rfl

/-- Restriction of parameters strictly commutes with the original quotient descent. -/
theorem parameterDesc_restrict {S : Type*} [TopologicalSpace S] [LocallyCompactSpace S]
    (q : C(S, T)) (t : S) (x : Space f g n) :
    parameterDesc f g n (l.comp (q.prodMap (.id _))) (r.comp (q.prodMap (.id _)))
      (o.comp (q.prodMap (.id _))) (fun t x ↦ h₀ (q t) x)
      (fun t x ↦ h₁ (q t) x) (fun t s ↦ hb (q t) s) (t, x) =
        parameterDesc f g n l r o h₀ h₁ hb (q t, x) := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z <;> rfl
    | inr z => rfl

end HomotopyPushout

variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (n : ℕ)
  (l : C(T × F.space n, Z)) (h : C(T × (unitInterval × E.space n), Z))
  (h₀ : ∀ t x, h (t, (0, x)) = l (t, f.map n x))
  (h₁ : ∀ t x, h (t, (1, x)) = l (t, F.point n))
  (hb : ∀ t s, h (t, (s, E.point n)) = l (t, F.point n))

/-- Reuse the original reduced-cone descent with the parameter mapping space as target. -/
def mappingConeParameterDescCurried : C((mappingCone f).space n, C(T, Z)) :=
  ReducedMappingCone.desc (E.point n) (F.point n) (f.map n)
    (ContinuousMap.curry ⟨fun z : F.space n × T ↦ l (z.2, z.1), by fun_prop⟩)
    (ContinuousMap.curry ⟨fun z : (unitInterval × E.space n) × T ↦ h (z.2, z.1),
      by fun_prop⟩)
    (by intro x; ext t; exact h₀ t x)
    (by intro x; ext t; exact h₁ t x)
    (by intro s; ext t; exact hb t s)

/-- Joint evaluation of the unchanged parameterized cone quotient. -/
def mappingConeParameterDesc : C(T × (mappingCone f).space n, Z) :=
  ⟨fun z ↦ mappingConeParameterDescCurried f n l h h₀ h₁ hb z.2 z.1,
    (mappingConeParameterDescCurried f n l h h₀ h₁ hb).uncurry.continuous.comp continuous_swap⟩

/-- Laurent inputs retain the supplied family exactly. -/
@[simp] theorem mappingConeParameterDesc_inclusion (t : T) (x : F.space n) :
    mappingConeParameterDesc f n l h h₀ h₁ hb (t, (mappingConeInclusion f).map n x) =
      l (t, x) := rfl

/-- The cone height remains an independent parameter. -/
@[simp] theorem mappingConeParameterDesc_cylinder (t : T) (s : unitInterval) (x : E.space n) :
    mappingConeParameterDesc f n l h h₀ h₁ hb
      (t, ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x)) =
        h (t, (s, x)) := rfl

/-- Every continuous parameter restriction commutes with the same cone descent. -/
theorem mappingConeParameterDesc_restrict
    {S : Type*} [TopologicalSpace S] [LocallyCompactSpace S]
    (q : C(S, T)) (t : S) (x : (mappingCone f).space n) :
    mappingConeParameterDesc f n (l.comp (q.prodMap (.id _))) (h.comp (q.prodMap (.id _)))
      (fun t x ↦ h₀ (q t) x) (fun t x ↦ h₁ (q t) x) (fun t s ↦ hb (q t) s) (t, x) =
        mappingConeParameterDesc f n l h h₀ h₁ hb (q t, x) := by
  induction x using Quot.inductionOn with
  | h z => cases z <;> rfl

end Quillen.LoopPrespectrum
