/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Approximation.CoarseKEquivalence
import Quillen.Waldhausen.Fibration.Rows.ComplexRelativeJoint

/-! Actual coarse-cylinder maps and a genuine complex-model specialization. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CoarseApproximationConsumers
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open RowFactorization
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (N : NestedWeakEquivalences W) (J : JointData N)

/-- Coarse gluing controls the source map without assuming either endpoint is fine-weak. -/
theorem actual_source_coarse_weak {f g : Arrow C} (α : f ⟶ g)
    (hl : N.coarse.weq α.left) (hr : N.coarse.weq α.right) :
    N.coarse.weq ((J.joint.map α).hom.left) := jointSource_coarseWeak N J α hl hr

/-- The whole joint square is genuinely coarse-weak from original coarse endpoint maps. -/
theorem actual_joint_coarse_weak [N.coarse.weq.HasTwoOutOfThreeProperty]
    {f g : Arrow C} (α : f ⟶ g) (hl : N.coarse.weq α.left) (hr : N.coarse.weq α.right) :
    ExtensionCategory.weq N.coarse ((coarseJoint N J).map α) :=
  (coarseJoint_exact N J).weak α ⟨hl, hr⟩

/-- Retargeting the weak structure retains the original second endpoint and projection. -/
theorem actual_second_projection [N.coarse.weq.HasTwoOutOfThreeProperty] (f : Arrow C) :
    (J.coarseReflexive N).inr.app f ≫ ((J.coarseReflexive N).joint.obj f).obj.hom ≫
      (J.coarseReflexive N).projection.app f =
      J.inr.app f ≫ (J.joint.obj f).obj.hom ≫ J.projection.app f := rfl

/-- The original strict factorization equation survives coarse retargeting exactly. -/
theorem actual_first_factorization [N.coarse.weq.HasTwoOutOfThreeProperty] (f : Arrow C) :
    (J.coarseReflexive N).inl.app f ≫ ((J.coarseReflexive N).joint.obj f).obj.hom ≫
      (J.coarseReflexive N).projection.app f = f.hom := J.factorization f

variable (h : HasApproximationProperty N.coarse V F)
  (hF : IsExact N.coarse.cof N.coarse.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]

include h hF in
/-- Source saturation is derived, not a separate coarse-source hypothesis. -/
theorem actual_source_saturated : N.coarse.weq.HasTwoOutOfThreeProperty :=
  h.source_twoOutOfThree hF

include J h in
/-- The actual original coarse-source S-map retains complete component surjectivity. -/
theorem original_coarse_component (y : V.Delooping) :
    ∃ x, Joined (deloopingMap hF x) y :=
  (coarse_deloopingMap_isWeakHomotopyEquivalence N J h hF).component_surjective y

/-- K-zero has a genuine inverse for the literal original canonical map. -/
theorem original_coarse_K_zero_right_inverse (y : V.K 0) :
    KMap hF 0 ((coarseKEquiv N J h hF 0).symm y) = y :=
  (coarseKEquiv N J h hF 0).apply_symm_apply y

end CoarseApproximationConsumers

namespace ComplexCoarseApproximationConsumer
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))
  (N : NestedWeakEquivalences (complexSubcategory P))
  {D : Type (max u v)} [Category.{v} D] {V : Structure D} {F : P.FullSubcategory ⥤ D}
  (h : HasApproximationProperty N.coarse V F)
  (hF : IsExact N.coarse.cof N.coarse.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]
include hcone hshift h

/-- The genuine existing complex joint cylinder discharges the coarse-source
structural input; only actual geometric App1/App2 and exactness remain. -/
theorem original_complex_coarse_KMap_bijective (n : ℕ) : Function.Bijective (KMap hF n) :=
  coarse_KMap_bijective N (complexJointDataOfNested P hcone hshift N) h hF n

end ComplexCoarseApproximationConsumer
