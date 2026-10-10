/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlatObjectsPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.Pullback

/-!
# Arbitrary pullback of bounded-above flat complexes

Actual stalkwise-flat cycles are obtained by descending from the upper bound.
Consequently arbitrary geometric pullback preserves acyclic bounded-above
flat complexes and quasi-isomorphisms between such complexes.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.SchemeSheaf

instance stalkwiseFlat_isClosedUnderIsomorphisms (X : Scheme.{u}) :
    (stalkwiseFlat X).IsClosedUnderIsomorphisms where
  of_iso {M N} e hM := by
    intro x
    let : Module.Flat (X.presheaf.stalk x) ((moduleStalk X x).obj M) := hM x
    exact Module.Flat.of_linearEquiv ((moduleStalk X x).mapIso e.symm).toLinearEquiv

instance stalkwiseFlat_kernelClosed (X : Scheme.{u}) :
    (sheafExactStructure X).IsKernelClosed (stalkwiseFlat X) where
  prop_kernel hS h₂ h₃ := stalkwiseFlat_of_shortExact hS h₂ h₃

/-- Actual cycles of a bounded-above acyclic complex of stalkwise-flat sheaves are flat. -/
theorem stalkwiseFlat_cycles_of_boundedAbove_acyclic {X : Scheme.{u}}
    (K : CochainComplex X.Modules ℤ) (hK : ∀ n, stalkwiseFlat X (K.X n))
    (ha : K.Acyclic) (b : ℤ) (hb : ∀ n, b < n → IsZero (K.X n)) (n : ℤ) :
    stalkwiseFlat X (K.cycles n) :=
  Waldhausen.GilletWaldhausen.cycles_mem (stalkwiseFlat X) K hK ha b hb n

/-- The bounded-above flat acyclic objects really remain acyclic under arbitrary pullback. -/
theorem acyclic_pullback_of_boundedAbove_stalkwiseFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex Y.Modules ℤ) (hK : ∀ n, stalkwiseFlat Y (K.X n))
    (ha : K.Acyclic) (b : ℤ) (hb : ∀ n, b < n → IsZero (K.X n)) :
    ((PerfectComplexes.pullbackComplex f).obj K).Acyclic := by
  apply HomologicalAlgebra.acyclic_map_of_cycle_sequences
  intro n
  exact shortExact_pullback_of_stalkwiseFlat_quotient f
    (Waldhausen.GilletWaldhausen.cycleSequence_shortExact K n (ha (n + 1)))
    (stalkwiseFlat_cycles_of_boundedAbove_acyclic K hK ha b hb (n + 1))

/-- Small-universe coproducts also preserve the actual flat stalk property. -/
theorem stalkwiseFlat_smallCoproduct (X : Scheme.{u}) {I : Type} (M : I → X.Modules)
    (hM : ∀ i, stalkwiseFlat X (M i)) : stalkwiseFlat X (∐ M) := by
  classical
  intro x
  let (i : I) : Module.Flat (X.presheaf.stalk x) ((moduleStalk X x).obj (M i)) := hM i x
  exact Module.Flat.of_linearEquiv
    ((PreservesCoproduct.iso (moduleStalk X x) M) ≪≫
      ModuleCat.coprodIsoDirectSum (fun i => (moduleStalk X x).obj (M i))).toLinearEquiv

/-- Binary coproducts preserve actual stalkwise flatness. -/
theorem stalkwiseFlat_biprod (X : Scheme.{u}) {M N : X.Modules}
    (hM : stalkwiseFlat X M) (hN : stalkwiseFlat X N) : stalkwiseFlat X (M ⊞ N) := by
  let F : WalkingPair → X.Modules := fun i => i.casesOn M N
  let e : (∐ F) ≅ (M ⨿ N) := HasColimit.isoOfNatIso
    (Discrete.natIso (fun i => by cases i; exact Iso.refl _))
  exact (stalkwiseFlat X).prop_of_iso (e ≪≫ (biprod.isoCoprod M N).symm)
    (stalkwiseFlat_smallCoproduct X F (fun i => i.casesOn hM hN))

/-- Arbitrary geometric pullback preserves quasi-isomorphisms between bounded-above
complexes of genuinely stalkwise-flat module sheaves. -/
theorem quasiIso_pullback_of_boundedAbove_stalkwiseFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : CochainComplex Y.Modules ℤ}
    (hK : ∀ n, stalkwiseFlat Y (K.X n)) (hL : ∀ n, stalkwiseFlat Y (L.X n))
    (b c : ℤ) (hb : ∀ n, b < n → IsZero (K.X n))
    (hc : ∀ n, c < n → IsZero (L.X n)) (s : K ⟶ L) [QuasiIso s] :
    QuasiIso ((PerfectComplexes.pullbackComplex f).map s) := by
  have ht (n : ℤ) : stalkwiseFlat Y ((CochainComplex.mappingCone s).X n) := by
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod s n (n + 1) rfl
    exact (stalkwiseFlat Y).prop_of_iso e.symm (stalkwiseFlat_biprod Y (hK (n + 1)) (hL n))
  have hu (n : ℤ) (hn : max (b - 1) c < n) :
      IsZero ((CochainComplex.mappingCone s).X n) :=
    (CochainComplex.mappingCone.isZero_X_iff s n).mpr ⟨hb (n + 1) (by omega), hc n (by omega)⟩
  have ha := acyclic_pullback_of_boundedAbove_stalkwiseFlat f _ ht
    (PerfectComplexes.mappingCone_acyclic_of_quasiIso s) (max (b - 1) c) hu
  apply HomologicalAlgebra.quasiIso_of_mappingCone_acyclic
  intro n
  exact (ha n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso s (Scheme.Modules.pullback f))

end Quillen.SchemeSheaf
