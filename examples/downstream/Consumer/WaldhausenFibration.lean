/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Fibration.CanonicalFiberMap
public import Quillen.Waldhausen.Cylinder.Subcategory
public import Quillen.Waldhausen.Cylinder.JointExact
public import Quillen.Waldhausen.SConstruction.Connected
public import Quillen.Waldhausen.SConstruction.Rows.JointFunctor

/-! Actual canonical fiber and common-cylinder maps, without a fibration conclusion. -/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex Quillen Quillen.Waldhausen
open scoped Topology
universe u v
namespace Consumer
theorem actual_delooping_connected {C : Type u} [Category.{v} C] (W : Structure C) :
    PathConnectedSpace W.Delooping := inferInstance

def actual_delooping_zero_path {C : Type u} [Category.{v} C] (W : Structure C)
    (x : W.Delooping) : Path W.kBasepoint x := Waldhausen.kBasepointPath W x

section Fiber
open Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
def actual_acyclic_fiber_map : C((acyclicStructure N).Delooping,
    HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) := canonicalFiberMap N
theorem actual_acyclic_fiber_projection :
    (HomotopyFiber.projection (changeWeakMap N) N.coarse.kBasepoint).comp
      (actual_acyclic_fiber_map N) = (deloopingMap (acyclicInclusion_exact N)).hom := rfl
theorem actual_consecutive_K_maps (n : ℕ) :
    (Waldhausen.KMap (changeWeak_exact N) n).comp (Waldhausen.KMap (acyclicInclusion_exact N) n) = 1
      :=
  changeWeak_KMap_comp_acyclic N n
end Fiber
section Cylinder
open SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))
theorem actual_joint_cylinder_quasi_exact :
    IsExact (ArrowCategory.waldhausenStructure (complexSubcategory P)).cof
      (ArrowCategory.waldhausenStructure (complexSubcategory P)).weq
      (ExtensionCategory.waldhausenStructure (complexSubcategory P)).cof
      (ExtensionCategory.waldhausenStructure (complexSubcategory P)).weq
      (subcategoryJointFunctor P hcone hshift) := subcategoryJointFunctor_quasiExact P hcone hshift
theorem actual_joint_cylinder_iso_exact :
    let W := ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P)
    IsExact (ArrowCategory.waldhausenStructure W).cof (ArrowCategory.waldhausenStructure W).weq
      (ExtensionCategory.waldhausenStructure W).cof (ExtensionCategory.waldhausenStructure W).weq
      (subcategoryJointFunctor P hcone hshift) := subcategoryJointFunctor_isoExact P hcone hshift
theorem actual_joint_cylinder_on_rows (n : SimplexCategory) :
    IsExact
      (ArrowCategory.waldhausenStructure (QuotientRows.waldhausenStructure (complexSubcategory P)
        n)).cof
      (ArrowCategory.waldhausenStructure (QuotientRows.waldhausenStructure (complexSubcategory P)
        n)).weq
      (ExtensionCategory.waldhausenStructure (QuotientRows.waldhausenStructure (complexSubcategory
        P) n)).cof
      (ExtensionCategory.waldhausenStructure (QuotientRows.waldhausenStructure (complexSubcategory
        P) n)).weq
      (QuotientRows.jointOnRows (complexSubcategory P) (complexSubcategory P)
        (subcategoryJointFunctor_quasiExact P hcone hshift) n) :=
  QuotientRows.jointOnRows_exact _ _ (subcategoryJointFunctor_quasiExact P hcone hshift) n
end Cylinder
end Consumer
