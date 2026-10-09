import Quillen.Algebra.FiniteAdjacentSection
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == `Quillen.Algebra.FiniteAdjacentSection do continue
    count := count + 1
    let axioms ← collectAxioms name
    for a in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do throwError "Unsupported {a}: {name}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count == 23 do throwError "Expected 23 section origins, got {count}"
  logInfo m!"Audited all {count} FiniteAdjacentSection origins."
noncomputable section
universe u
open Quillen.FiniteAdjacentComplex
variable (G : Type u) [CommGroup G] (n : ℕ)
example (i : Fin (n+1)) (x : G) : singleCoordinate G i x = Pi.mulSingle i x := rfl
example (k : ℕ) (h : Even k) (x : G) : coordinateSign G k x = x := by simp [h]
example (k : ℕ) (h : ¬Even k) (x : G) : coordinateSign G k x = x⁻¹ := by simp [h]
example (i : Fin (n+1)) (x : G) :
    euler G (n+1) (Pi.mulSingle i x) = if Even i.val then x else x⁻¹ := by
  exact (euler_singleCoordinate G i x).trans (coordinateSign_apply G i.val x)
example (i : Fin (n+1)) : Function.Bijective (fun x : G => euler G (n+1) (Pi.mulSingle i x)) :=
  euler_singleCoordinate_bijective G i
example (i : Fin (n+1)) (x : G) :
    coordinateSection G n i x = Pi.mulSingle i ((coordinateSign G i.val).symm x) := rfl
example (i : Fin (n+1)) (x : G) :
    euler G (n+1) (coordinateSection G n i x) = x := euler_coordinateSection G n i x
example (i : Fin (n+1)) (y : Fin (n+1) → G) :
    coordinateValue G n i y = if Even i.val then euler G (n+1) y else (euler G (n+1) y)⁻¹ :=
  coordinateValue_apply G n i y
example (i : Fin (n+1)) (y : Fin (n+1) → G) :
    coordinateRepresentative G n i y = Pi.mulSingle i (coordinateValue G n i y) := rfl
example (i j : Fin (n+1)) (h : j ≠ i) (y : Fin (n+1) → G) :
    coordinateRepresentative G n i y j = 1 := by
  rw [coordinateRepresentative_apply]
  exact Pi.mulSingle_eq_of_ne h _
example (i : Fin (n+1)) (y : Fin (n+1) → G) :
    ∃! d : Fin n → G, incidence G n d * Pi.mulSingle i (coordinateValue G n i y) = y :=
  existsUnique_incidence_representative G n i y
example (i : Fin (n+1)) (y : Fin (n+1) → G) :
    ∃! c : G, ∃ d : Fin n → G, (Fin.cons 1 d * Fin.snoc d 1) * Pi.mulSingle i c = y :=
  existsUnique_coordinateValue G n i y
example (i : Fin (n+1)) (y : Fin (n+1) → G) :
    ∃! p : (Fin n → G) × G, (Fin.cons 1 p.1 * Fin.snoc p.1 1) * Pi.mulSingle i p.2 = y :=
  existsUnique_incidence_coordinate G n i y
example (x : G) : euler G 1 (Pi.mulSingle (0 : Fin 1) x) = x := by
  exact (euler_singleCoordinate G (0 : Fin 1) x).trans (by simp)
example (x : G) : euler G (n+2) (Pi.mulSingle (1 : Fin (n+2)) x) = x⁻¹ := by
  simpa using euler_singleCoordinate G (1 : Fin (n+2)) x
example (y : Fin 1 → G) :
    ∃! p : (Fin 0 → G) × G, incidence G 0 p.1 * Pi.mulSingle (0 : Fin 1) p.2 = y :=
  existsUnique_incidence_coordinate G 0 0 y
example (y : Fin (n+1) → G) (i : Fin (n+1)) :
    euler G (n+1) (coordinateRepresentative G n i y) = euler G (n+1) y :=
  euler_coordinateRepresentative G n i y
