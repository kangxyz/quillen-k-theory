import Quillen.Algebra.FiniteAdjacentComplex
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == `Quillen.Algebra.FiniteAdjacentComplex do continue
    count := count + 1
    let axioms ← collectAxioms name
    for a in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do throwError "Unsupported {a}: {name}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count == 41 do throwError "Expected 41 core origins, got {count}"
  logInfo m!"Audited all {count} FiniteAdjacentComplex origins."
noncomputable section
universe u
open Quillen.FiniteAdjacentComplex
variable (G : Type u) [CommGroup G] (n : ℕ)
example (x : Fin n → G) : incidence G n x = Fin.cons 1 x * Fin.snoc x 1 := rfl
example : Function.Injective (incidence G n) := incidence_injective G n
example (x : Fin n → G) : euler G (n+1) (incidence G n x) = 1 := euler_incidence G n x
example (y : Fin (n+1) → G) : euler G (n+1) y = 1 ↔ ∃ x, incidence G n x = y := euler_eq_one_iff G n y
example (x : G) : initialTerm G n x = Fin.cons x 1 := rfl
example (x : G) : euler G (n+1) (initialTerm G n x) = x := euler_initialTerm G n x
example : Function.Surjective (euler G (n+1)) := euler_surjective G n
example : Function.Injective (incidence G 0) := incidence_injective G 0
example (y : Fin 1 → G) : euler G 1 y = 1 ↔ ∃ x : Fin 0 → G, incidence G 0 x = y := euler_eq_one_iff G 0 y
example (y : Fin 1 → G) : euler G 1 y = y 0 := by simp
example (y : Fin 2 → G) : euler G 2 y = y 0 / y 1 := by simp [Fin.tail]
example : {y | euler G (n+1) y = 1} = Set.range (incidence G n) := by
  ext y
  exact euler_eq_one_iff G n y
example (y : Fin (n+1) → G) : euler G (n+1) y = 1 ↔ ∃! x, incidence G n x = y := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := (euler_eq_one_iff G n y).1 h
    exact ⟨x,hx,fun z hz => incidence_injective G n (hz.trans hx.symm)⟩
  · rintro ⟨x,hx,_⟩
    exact (euler_eq_one_iff G n y).2 ⟨x,hx⟩
