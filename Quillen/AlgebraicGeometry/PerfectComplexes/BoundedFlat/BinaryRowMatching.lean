/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BinaryRowEndpoint

/-! Full-node row comparison factored before coefficient specialization. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
variable {V : Model.{u + 1}} {X Y Z : Scheme.{u}}
  {F : V ⟶ modelOf (boundedFlatPerfectWaldhausen X)}
  {P : V ⟶ modelOf (boundedFlatPerfectWaldhausen Z)}
  {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
  {ρ : F.functor ≅ (P ≫ BinaryNormalizationSimplex.sourceMap f g).functor}
  {σ : F.functor ≅ (P ≫ BinaryNormalizationSimplex.sourceMap f' g').functor}
  {N M : Fin 3 → Σ G : V ⟶ modelOf (boundedFlatPerfectWaldhausen X), F.functor ≅ G.functor}

/-- Canonical row forms, a full source identity, and actual scheme-factor equalities suffice. -/
theorem binary_rows_source_match
    (hN : ∀ i, N i = preBinaryNodes F P f g ρ i)
    (hM : ∀ i, M i = preBinaryNodes F P f' g' σ i)
    (he : N 0 = M 0) (hf : f = f') (hg : g = g') (i : Fin 3) : N i = M i :=
  (hN i).trans ((preBinaryNodes_source_congr F P f g hf hg ρ σ
    ((hN 0).symm.trans (he.trans (hM 0))) i).trans (hM i).symm)

/-- The analogous full-target comparison retains the same original binary row normal forms. -/
theorem binary_rows_target_match
    (hN : ∀ i, N i = preBinaryNodes F P f g ρ i)
    (hM : ∀ i, M i = preBinaryNodes F P f' g' σ i)
    (he : N 2 = M 2) (hf : f = f') (hg : g = g') (i : Fin 3) : N i = M i :=
  (hN i).trans ((preBinaryNodes_target_congr F P f g hf hg ρ σ
    ((hN 2).symm.trans (he.trans (hM 2))) i).trans (hM i).symm)

end Quillen.PerfectComplexes.BassH0Merge
