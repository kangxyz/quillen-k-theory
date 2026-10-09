import Quillen.Topology.CubicalSubdivision.ControlledChartLifting
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let wanted := #[`Quillen.Topology.CubicalSubdivision.FaceContainment,
    `Quillen.Topology.CubicalSubdivision.IncidentCharts,
    `Quillen.Topology.CubicalSubdivision.ControlledLifting,
    `Quillen.Topology.CubicalSubdivision.ControlledChartLifting]
  let mut counts : Array Nat := #[0,0,0,0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some j := wanted.idxOf? env.header.moduleNames[index.toNat]! | continue
    counts := counts.set! j (counts[j]! + 1)
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axs}"
  unless counts == #[3,12,2,5] do
    throwError "Unexpected controlled-chart origin counts: {counts}"
  logInfo m!"Audited actual controlled-chart origins: {counts}; total {counts.foldl (· + ·) 0}."
noncomputable section
open Quillen.CubicalSubdivision
open scoped Topology unitInterval
universe u v w
example {n m : ℕ} (F G : FaceIndex n m) (s : Active F → unitInterval)
    (t : Active G → unitInterval) (hs : s ∉ _root_.Cube.boundary (Active F))
    (he : face F s = face G t) : faceSet F ⊆ faceSet G :=
  faceSet_subset_of_interior F G s t hs he
example {n m : ℕ} (F G : FaceIndex n m) (s : Active F → unitInterval)
    (hx : face F s ∈ faceSet G) :
    s ∈ _root_.Cube.boundary (Active F) ∨ faceSet F ⊆ faceSet G :=
  face_boundary_or_subset_of_mem F G s hx
example {m : ℕ} (F G : FaceIndex 0 m) (s : Active F → unitInterval)
    (t : Active G → unitInterval) (hs : s ∉ _root_.Cube.boundary (Active F))
    (he : face F s = face G t) : faceSet F ⊆ faceSet G :=
  faceSet_subset_of_interior F G s t hs he
example {n m : ℕ} {J : Type w} [DecidableEq J] (chart : FaceIndex n m → J) (F : FaceIndex n m) :
    chart F ∈ incidentCharts chart F := self_mem_incidentCharts chart F
example {n m : ℕ} {J : Type w} [DecidableEq J] (chart : FaceIndex n m → J) (F : FaceIndex n m) :
    (incidentCharts chart F).Nonempty := incidentCharts_nonempty chart F
example {n m : ℕ} {J : Type w} [DecidableEq J] (chart : FaceIndex n m → J)
    (F G : FaceIndex n m) (hFG : faceSet F ⊆ faceSet G) :
    incidentCharts chart G ⊆ incidentCharts chart F := incidentCharts_antitone chart hFG
example {n m : ℕ} {J : Type w} [DecidableEq J] {E : Type u}
    (chart : FaceIndex n m → J) (R : J → Set E) (F G : FaceIndex n m)
    (hFG : faceSet F ⊆ faceSet G) : incidentChartSet chart R F ⊆ incidentChartSet chart R G :=
  incidentChartSet_mono chart R hFG
example {n m : ℕ} {J : Type w} [DecidableEq J] (chart : FaceIndex n m → J)
    (F G : FaceIndex n m) (s : Active F → unitInterval)
    (hs : s ∉ _root_.Cube.boundary (Active F)) (hx : face F s ∈ faceSet G) :
    chart G ∈ incidentCharts chart F := chart_mem_incidentCharts_of_interior chart F G s hs hx
variable {E : Type u} {B : Type v} {J : Type w}
  [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E,B)) (R : J → Set E) (W : J → Set B)
example (S : Finset J) (x : {e : E // ∀ j ∈ S,e ∈ R j ∧ p e ∈ W j}) :
    (controlledChartMap p R W S x).val = p x.val := rfl
example (x : {e : E // ∀ j ∈ (∅ : Finset J),e ∈ R j ∧ p e ∈ W j}) :
    (controlledChartMap p R W ∅ x).val = p x.val := rfl
example (hloc : ∀ S : Finset J,S.Nonempty → BoundaryLifting (controlledChartMap p R W S))
    (n : ℕ) (a : C({x : Cube n // x ∈ _root_.Cube.boundary (Fin n)},E))
    (b : C(Cube n,B)) (hab : ∀ x,p (a x) = b x.val)
    (U : J → Set (Cube n)) (hU : ∀ j,IsOpen (U j)) (hcover : ∀ x,∃ j,x ∈ U j)
    (hb : ∀ j x,x ∈ U j → b x ∈ W j)
    (ha : ∀ j (x : {x : Cube n // x ∈ _root_.Cube.boundary (Fin n)}),x.val ∈ U j → a x ∈ R j) :
    ∃ l : C(Cube n,E),(∀ x : {x : Cube n // x ∈ _root_.Cube.boundary (Fin n)},l x.val = a x) ∧ p.comp l = b :=
  exists_lift_of_controlled_chart_cover p R W hloc n a b hab U hU hcover hb ha
example (hloc : ∀ S : Finset J,S.Nonempty → BoundaryLifting (controlledChartMap p R W S))
    (a : C({x : Cube 0 // x ∈ _root_.Cube.boundary (Fin 0)},E))
    (b : C(Cube 0,B)) (hab : ∀ x,p (a x) = b x.val)
    (U : J → Set (Cube 0)) (hU : ∀ j,IsOpen (U j)) (hcover : ∀ x,∃ j,x ∈ U j)
    (hb : ∀ j x,x ∈ U j → b x ∈ W j)
    (ha : ∀ j (x : {x : Cube 0 // x ∈ _root_.Cube.boundary (Fin 0)}),x.val ∈ U j → a x ∈ R j) :
    ∃ l : C(Cube 0,E),(∀ x : {x : Cube 0 // x ∈ _root_.Cube.boundary (Fin 0)},l x.val = a x) ∧ p.comp l = b :=
  exists_lift_of_controlled_chart_cover p R W hloc 0 a b hab U hU hcover hb ha
example [IsEmpty J] (n : ℕ) (U : J → Set (Cube n))
    (hc : ∀ x : Cube n,∃ j,x ∈ U j) : False := by
  obtain ⟨j,_⟩ := hc (fun _ ↦ 0)
  exact isEmptyElim j

section IndependentFaceCoordinates
example {n m : ℕ} (F G : FaceIndex n m)
    (s : Active F → unitInterval) (t : Active G → unitInterval)
    (hs : s ∉ _root_.Cube.boundary (Active F)) (he : face F s = face G t)
    (i : Fin n) (k l : Fin (m+1)) (hF : F i = Sum.inr k) (hG : G i = Sum.inr l) : k = l :=
  moving_label_eq_of_interior F G s t hs he i k l hF hG
example {m : ℕ} (F G : FaceIndex 0 m) : faceSet F ⊆ faceSet G := by
  apply faceSet_subset_of_interior F G (fun _ ↦ 0) (fun _ ↦ 0)
  · rintro ⟨i,_⟩
    exact Fin.elim0 i.val
  · funext i
    exact Fin.elim0 i
example {n m : ℕ} {J : Type w} [DecidableEq J]
    (chart : FaceIndex n m → J) (F G : FaceIndex n m)
    (hFG : faceSet F ⊆ faceSet G) : chart G ∈ incidentCharts chart F :=
  (mem_incidentCharts_iff chart F (chart G)).2 ⟨G,hFG,rfl⟩
example {n m : ℕ} {J : Type w} [DecidableEq J] {E : Type u}
    (chart : FaceIndex n m → J) (R : J → Set E) (F : FaceIndex n m)
    (e : E) (he : e ∈ incidentChartSet chart R F) : e ∈ R (chart F) :=
  he (chart F) (self_mem_incidentCharts chart F)
end IndependentFaceCoordinates

section IndependentLifting
variable {E : Type u} {B : Type v} {J : Type w}
  [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E,B)) (R : J → Set E) (W : J → Set B)
example (S : Finset J) (x : {e : E // ∀ j ∈ S,e ∈ R j ∧ p e ∈ W j})
    (j : J) (hj : j ∈ S) : x.val ∈ R j ∧ (controlledChartMap p R W S x).val ∈ W j :=
  x.property j hj
example (n m : ℕ)
    (a : C({x : Cube n // x ∈ _root_.Cube.boundary (Fin n)},E))
    (b : C(Cube n,B)) (hab : ∀ x,p (a x) = b x.val)
    (K : FaceIndex n m → Set E)
    (hK : ∀ F G,faceSet F ⊆ faceSet G → K F ⊆ K G)
    (haK : ∀ F (x : {x : Cube n // x ∈ _root_.Cube.boundary (Fin n)}),
      x.val ∈ faceSet F → a x ∈ K F)
    (hfill : ∀ F : FaceIndex n m,
      ∀ c : C({t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)},E),
        (∀ t,c t ∈ K F) → (∀ t,p (c t) = b (face F t.val)) →
        ∃ d : C((Active F → unitInterval),E),
          (∀ t : {t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)},d t.val = c t) ∧
          (∀ t,p (d t) = b (face F t)) ∧ (∀ t,d t ∈ K F)) :
    ∃ l : C(Cube n,E),
      (∀ x : {x : Cube n // x ∈ _root_.Cube.boundary (Fin n)},l x.val = a x) ∧
      p.comp l = b ∧ ∀ (F : FaceIndex n m) (t : Active F → unitInterval),l (face F t) ∈ K F :=
  exists_controlled_grid_lift n m p a b hab K hK haK hfill
example (hloc : ∀ S : Finset J,S.Nonempty → BoundaryLifting (controlledChartMap p R W S))
    (hcover : ∀ (n : ℕ) (a : C(Boundary n,E)) (b : C(Cube n,B)),
      (∀ x : Boundary n,p (a x) = b x.val) →
      ∃ U : J → Set (Cube n),(∀ j,IsOpen (U j)) ∧ (∀ x,∃ j,x ∈ U j) ∧
        (∀ j x,x ∈ U j → b x ∈ W j) ∧
        (∀ j (x : Boundary n),x.val ∈ U j → a x ∈ R j)) : BoundaryLifting p := by
  intro n a b hab
  obtain ⟨U,hU,hcov,hb,ha⟩ := hcover n a b hab
  exact exists_lift_of_controlled_chart_cover p R W hloc n a b hab U hU hcov hb ha
example (hloc : ∀ S : Finset J,S.Nonempty → BoundaryLifting (controlledChartMap p R W S))
    (a : C(Boundary 0,E)) (b : C(Cube 0,B)) (hab : ∀ x : Boundary 0,p (a x) = b x.val)
    (U : J → Set (Cube 0)) (hU : ∀ j,IsOpen (U j)) (hcover : ∀ x,∃ j,x ∈ U j)
    (hb : ∀ j x,x ∈ U j → b x ∈ W j)
    (ha : ∀ j (x : Boundary 0),x.val ∈ U j → a x ∈ R j) :
    ∃ e : E,p e = b (fun _ ↦ 0) := by
  obtain ⟨l,_,hl⟩ := exists_lift_of_controlled_chart_cover p R W hloc 0 a b hab U hU hcover hb ha
  exact ⟨l (fun _ ↦ 0),ContinuousMap.congr_fun hl (fun _ ↦ 0)⟩
end IndependentLifting
