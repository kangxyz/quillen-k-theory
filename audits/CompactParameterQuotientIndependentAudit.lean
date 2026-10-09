import Quillen.Topology.Pushout.CompactParameter
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.Maps.CompactParameterQuotient,
    `Quillen.Topology.Realization.CompactGraph,`Quillen.Topology.Pushout.CompactParameter]
  let mut count : Nat := 0
  let mut counts : Array Nat := #[0,0,0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some i := targets.idxOf? env.header.moduleNames[index.toNat]! | continue
    count := count + 1
    counts := counts.modify i (·+1)
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axs}"
  unless count == 11 && counts == #[5,3,3] do throwError "Expected 11 origins, got {count}"
  logInfo m!"FIXED11 PASSED {count}: {counts}"
noncomputable section
open Quillen CategoryTheory Limits Topology
open scoped Topology Simplicial
universe u v w z
section Generic
variable {X : Type u} {Y : Type v} {D : Type w} {T : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace D]
  [TopologicalSpace T] [LocallyCompactSpace D]
  (q : X → Y) (hq : IsQuotientMap q) (p : C(Y,T)) (b : C(D,T))
example {s : Set Y} (hs : IsClosed s) : IsQuotientMap (s.restrictPreimage q) :=
  quotientMap_restrictPreimage_isClosed hq hs
example : IsQuotientMap (fun z : X × D ↦ (q z.1,z.2)) := quotientMap_prod_parameter hq
example (hc : IsClosed (Set.ofPred (fun z : Y × D ↦ p z.1 = b z.2))) :
    IsQuotientMap (fun z : {z : X × D // p (q z.1) = b z.2} ↦
      (⟨(q z.1.1,z.1.2),z.2⟩ : {z : Y × D // p z.1 = b z.2})) :=
  quotientMap_parameter_pullback_of_isClosed hq p b hc
example (hg : IsClosed (Set.ofPred (fun z : D × T ↦ b z.1 = z.2))) :
    IsQuotientMap (fun z : {z : X × D // p (q z.1) = b z.2} ↦
      (⟨(q z.1.1,z.1.2),z.2⟩ : {z : Y × D // p z.1 = b z.2})) :=
  quotientMap_parameter_pullback_of_closedGraph hq p b hg
example [T2Space T] :
    IsQuotientMap (fun z : {z : X × D // p (q z.1) = b z.2} ↦
      (⟨(q z.1.1,z.1.2),z.2⟩ : {z : Y × D // p z.1 = b z.2})) :=
  quotientMap_parameter_pullback hq p b
end Generic
section Realization
variable (X : SSet.{u}) {E : Type z} {Y : Type w} {D : Type v}
  [TopologicalSpace E] [TopologicalSpace Y] [TopologicalSpace D] [CompactSpace D]
  (p : C(Y,|X|)) (b : C(D,|X|))
example : IsClosed (Set.ofPred (fun z : D × |X| ↦ b z.1 = z.2)) :=
  realization_compactMap_isClosed_graph X b
example : IsClosed (Set.ofPred (fun z : Y × D ↦ p z.1 = b z.2)) :=
  realization_compactMap_matching_isClosed X p b
example [LocallyCompactSpace D] {q : E → Y} (hq : IsQuotientMap q) :
    IsQuotientMap (fun z : {z : E × D // p (q z.1) = b z.2} ↦
      (⟨(q z.1.1,z.1.2),z.2⟩ : {z : Y × D // p z.1 = b z.2})) :=
  realization_compactMap_pullback_quotient X hq p b
example [IsEmpty D] : IsClosed (Set.ofPred (fun z : D × |X| ↦ b z.1 = z.2)) :=
  realization_compactMap_isClosed_graph X b
example (x : |X|) : IsClosed (Set.ofPred (fun z : ULift.{v} PUnit × |X| ↦ x = z.2)) :=
  realization_compactMap_isClosed_graph X (ContinuousMap.const _ x)
end Realization
section Pushout
variable {A B C M : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ M} {j : C ⟶ M}
  (sq : IsPushout i f g j) (X : SSet.{u}) {D : Type v} [TopologicalSpace D]
  [CompactSpace D] [LocallyCompactSpace D] (p : C(M,|X|)) (b : C(D,|X|))
example : IsQuotientMap (Sum.elim g j) := pushout_sum_isQuotientMap sq
example : IsQuotientMap (fun z : {z : (B ⊕ C) × D // p (Sum.elim g j z.1) = b z.2} ↦
    (⟨(Sum.elim g j z.1.1,z.1.2),z.2⟩ : {z : M × D // p z.1 = b z.2})) :=
  pushout_realization_parameter_pullback_quotient sq X p b
example [IsEmpty D] : IsQuotientMap (fun z : {z : (B ⊕ C) × D // p (Sum.elim g j z.1) = b z.2} ↦
    (⟨(Sum.elim g j z.1.1,z.1.2),z.2⟩ : {z : M × D // p z.1 = b z.2})) :=
  pushout_realization_parameter_pullback_quotient sq X p b
end Pushout

section IndependentExactDescent
variable {X : Type u} {Y : Type v} {D : Type w} {T : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace D] [LocallyCompactSpace D]
  {q : X → Y} (hq : IsQuotientMap q)
example : IsQuotientMap ((∅ : Set Y).restrictPreimage q) :=
  quotientMap_restrictPreimage_isClosed hq isClosed_empty
example (p : Y → T) (b : D → T)
    (hc : IsClosed (Set.ofPred (fun z : Y × D ↦ p z.1 = b z.2))) :
    IsQuotientMap (fun z : {z : X × D // p (q z.1) = b z.2} ↦
      (⟨(q z.1.1,z.1.2),z.2⟩ : {z : Y × D // p z.1 = b z.2})) :=
  quotientMap_parameter_pullback_of_isClosed hq p b hc
example {Z : Type*} [TopologicalSpace Z] (k : Y × D → Z) :
    Continuous k ↔ Continuous (fun z : X × D ↦ k (q z.1,z.2)) :=
  (quotientMap_prod_parameter hq).continuous_iff
example {Z : Type*} [TopologicalSpace Z] (p : Y → T) (b : D → T)
    (hc : IsClosed (Set.ofPred (fun z : Y × D ↦ p z.1 = b z.2)))
    (k : {z : Y × D // p z.1 = b z.2} → Z) :
    Continuous k ↔ Continuous (fun z : {z : X × D // p (q z.1) = b z.2} ↦
      k ⟨(q z.1.1,z.1.2),z.2⟩) :=
  (quotientMap_parameter_pullback_of_isClosed hq p b hc).continuous_iff
end IndependentExactDescent

section IndependentPushoutDescent
variable {A B C M : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ M} {j : C ⟶ M}
  (sq : IsPushout i f g j) (X : SSet.{u}) {D : Type v} [TopologicalSpace D]
  [CompactSpace D] [LocallyCompactSpace D] (p : C(M,|X|)) (b : C(D,|X|))
example {Z : Type w} [TopologicalSpace Z] (k : {z : M × D // p z.1 = b z.2} → Z) :
    Continuous k ↔ Continuous (fun z : {z : (B ⊕ C) × D // p (Sum.elim g j z.1) = b z.2} ↦
      k ⟨(Sum.elim g j z.1.1,z.1.2),z.2⟩) :=
  (pushout_realization_parameter_pullback_quotient sq X p b).continuous_iff
example (n : ℕ) (h : C((Fin n → unitInterval),|X|)) :
    IsClosed (Set.ofPred (fun z : (Fin n → unitInterval) × |X| ↦ h z.1 = z.2)) :=
  realization_compactMap_isClosed_graph X h
example (h : C((Fin 0 → unitInterval),|X|)) :
    IsClosed (Set.ofPred (fun z : (Fin 0 → unitInterval) × |X| ↦ h z.1 = z.2)) :=
  realization_compactMap_isClosed_graph X h
end IndependentPushoutDescent
