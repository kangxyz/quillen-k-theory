import Quillen.Library
import Lean.Util.CollectAxioms
import Quillen.Topology.HomotopyPullback.WeakPasting
open Lean in
run_cmd do
  let env ← getEnv
  let wanted := #[`Quillen.Topology.HomotopyPullback.WeakSource,
    `Quillen.Topology.HomotopyPullback.WeakPasting]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    count := count + 1
    seen := seen.insert origin
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless seen.size == 2 do throwError "Missing defining module"
  unless count == 15 do throwError "Expected 15 declarations, found {count}"
  logInfo m!"Audited all {count} origins of weak pullback source/pasting."
noncomputable section
open Quillen Quillen.HomotopyPullback
open scoped Topology unitInterval
universe u
section Source
variable {X Y A Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace Z]
  (q : C(A,Y)) (f : C(X,Y)) (k : C(Z,X)) (hk : IsWeakHomotopyEquivalence k)
example : HomotopyLiftingProperty (sourceProjection f q) := sourceProjection_homotopyLiftingProperty q f
example : IsWeakHomotopyEquivalence (sourceMap q f k) := sourceMap_isWeakHomotopyEquivalence q f k hk
example (z : HomotopyPullback (f.comp k) q) : (sourceMap q f k z).1.1 = z.1.1 := rfl
example (z : HomotopyPullback (f.comp k) q) : (sourceMap q f k z).1.2.1 = k z.1.2.1 := rfl
example (z : HomotopyPullback (f.comp k) q) : (sourceMap q f k z).1.2.2 = z.1.2.2 := rfl
example (z : HomotopyPullback (f.comp k) q) :
    (sourceMapPullbackHomeomorph q f k z).1.2 = sourceMap q f k z := rfl
example (z : HomotopyPullback (f.comp k) q) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (sourceMap q f k) (x := z) rfl) :=
  (sourceMap_isWeakHomotopyEquivalence q f k hk).homotopy_bijective z n
example (z : HomotopyPullback (f.comp k) q) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (sourceMap q f k) (x := z) rfl) :=
  (sourceMap_isWeakHomotopyEquivalence q f k hk).homotopy_bijective z 0
example [IsEmpty Z] : IsEmpty (HomotopyPullback f q) := by
  let : IsEmpty (HomotopyPullback (f.comp k) q) := ⟨fun z ↦ isEmptyElim z.1.2.1⟩
  exact (sourceMap_isWeakHomotopyEquivalence q f k hk).isEmpty_target
example (z : {z : Z × HomotopyPullback f q // sourceProjection f q z.2 = k z.1}) :
    ((sourceMapPullbackHomeomorph q f k).symm z).1.2.2 = z.1.2.1.2.2 := rfl
example (z : HomotopyPullback f q) : ∃ x, Joined (sourceMap q f k x) z :=
  (sourceMap_isWeakHomotopyEquivalence q f k hk).component_surjective z
end Source
section Pasting
variable {X₀ X₁ X₂ B₀ B₁ B₂ : Type u}
  [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
  [TopologicalSpace B₀] [TopologicalSpace B₁] [TopologicalSpace B₂]
  (p₀ : C(X₀,B₀)) (p₁ : C(X₁,B₁)) (p₂ : C(X₂,B₂))
  (a : C(X₀,X₁)) (a' : C(X₁,X₂)) (b : C(B₀,B₁)) (b' : C(B₁,B₂))
  (w : p₁.comp a = b.comp p₀) (w' : p₂.comp a' = b'.comp p₁)
  (h : IsWeakHomotopyEquivalence (comparison p₁ b p₀ a w))
  (h' : IsWeakHomotopyEquivalence (comparison p₂ b' p₁ a' w'))
example : IsWeakHomotopyEquivalence
    (comparison p₂ (b'.comp b) p₀ (a'.comp a) (pasteSquare p₀ p₁ p₂ a a' b b' w w')) :=
  comparison_paste_isWeakHomotopyEquivalence p₀ p₁ p₂ a a' b b' w w' h h'
example (x : X₀) :
    (comparison p₂ (b'.comp b) p₀ (a'.comp a) (pasteSquare p₀ p₁ p₂ a a' b b' w w') x).1.2.2 =
      ContinuousMap.const unitInterval (b' (b (p₀ x))) := rfl
example (x : X₀) : Function.Bijective (homotopyGroupMap (N := Fin 0)
    (comparison p₂ (b'.comp b) p₀ (a'.comp a) (pasteSquare p₀ p₁ p₂ a a' b b' w w')) (x := x) rfl) :=
  (comparison_paste_isWeakHomotopyEquivalence p₀ p₁ p₂ a a' b b' w w' h h').homotopy_bijective x 0
example [IsEmpty X₀] : IsEmpty (HomotopyPullback p₂ (b'.comp b)) :=
  (comparison_paste_isWeakHomotopyEquivalence p₀ p₁ p₂ a a' b b' w w' h h').isEmpty_target
example : (pastingIntoNestedEquiv p₂ b b').toFun.comp
    (comparison p₂ (b'.comp b) p₀ (a'.comp a) (pasteSquare p₀ p₁ p₂ a a' b b' w w')) =
    (sourceMap b (baseProjection p₂ b') (comparison p₂ b' p₁ a' w')).comp
      (comparison p₁ b p₀ a w) :=
  pastingComparison_factorization p₀ p₁ p₂ a a' b b' w w'
example (x : X₀) (n : ℕ) : Function.Bijective (homotopyGroupMap (N := Fin n)
    (comparison p₂ (b'.comp b) p₀ (a'.comp a) (pasteSquare p₀ p₁ p₂ a a' b b' w w')) (x := x) rfl) :=
  (comparison_paste_isWeakHomotopyEquivalence p₀ p₁ p₂ a a' b b' w w' h h').homotopy_bijective x n
example (z : HomotopyPullback p₂ (b'.comp b)) : ∃ x,
    Joined (comparison p₂ (b'.comp b) p₀ (a'.comp a)
      (pasteSquare p₀ p₁ p₂ a a' b b' w w') x) z :=
  (comparison_paste_isWeakHomotopyEquivalence p₀ p₁ p₂ a a' b b' w w' h h').component_surjective z
end Pasting
