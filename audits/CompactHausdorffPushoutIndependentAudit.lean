import Quillen.Topology.Pushout.CompactHausdorff
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Topology.Pushout.CompactHausdorff
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origin == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 5 do throwError "Expected 5 compact-pushout origins, got {count}"
  logInfo m!"Audited all {count} compact-Hausdorff pushout origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits Topology Quillen
universe u v
-- The basic quotient lemma is independent-universe and retains the actual map.
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [T1Space Y] {q : X → Y}
    (hq : Continuous q) (hs : Function.Surjective q) (hc : IsClosedMap q) : T2Space Y :=
  t2Space_of_closed_surjection hq hs hc
-- Compactness needs neither the closed embedding nor Hausdorff inputs.
example {A B C D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) [CompactSpace B] [CompactSpace C] : CompactSpace D :=
  compactSpace_pushout sq
-- No compactness or separation assumption on A is supplied.
example {A B C D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (hi : IsClosedEmbedding i)
    [CompactSpace B] [T2Space B] [CompactSpace C] [T2Space C] :
    CompactSpace D ∧ T2Space D :=
  ⟨compactSpace_pushout sq, t2Space_pushout_of_compact_closedEmbedding sq hi⟩
-- The actual cell leg is closed under the weaker A-compact/C-Hausdorff input.
example {A B C D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (hi : IsClosedEmbedding i)
    [CompactSpace A] [T2Space C] : IsClosedMap g :=
  isClosedMap_pushout_left_of_compact sq hi
