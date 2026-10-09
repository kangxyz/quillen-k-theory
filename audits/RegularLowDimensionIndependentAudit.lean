import Quillen.Scheme.Regular.AffineLowDimension

open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.Scheme.Regular.LocalPrincipalDomain,
    `Quillen.Scheme.Regular.LocalLowDimension, `Quillen.Scheme.Regular.AffineLowDimension]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let selected := match env.getModuleIdxFor? name with
      | some i => modules.contains env.header.moduleNames[i.toNat]!
      | none => false
    if selected then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "{name} depends on unsupported assumption {axiomName}"
  logInfo m!"Audited {count} low-dimensional regular declarations: only standard Lean logical foundations."

open AlgebraicGeometry in
example (R : CommRingCat) [IsRegularRing R] (h : ringKrullDim R ≤ 1) (n : ℕ) :
    (Quillen.Scheme.KToGRegularDimOneEquiv R h n).toMonoidHom =
      Quillen.Scheme.KToG (Spec R) n := rfl
