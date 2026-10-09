import Quillen.CategoryTheory.TheoremB.CompactMappingCylinderParameters
import Quillen.CategoryTheory.TheoremB.CompactMappingCylinderTimes

/-! # Finite mapping-cylinder lift on the original two pieces

The cylinder piece follows the source lift until it reaches the glued end,
then follows the target lift of the shifted original base path. At the glued
end the formula is exactly the target-side lift, throughout time.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology unitInterval
open unitInterval
universe u
namespace Quillen.TheoremB.CompactMappingCylinder
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)
  {D : Type u} [TopologicalSpace D] (b : C(D,T))

/-- Genuine lifting on the original source and target constructs the exact
piecewise cylinder lift. No HLP of the pushout projection is used. -/
theorem exists_piece_lift
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (H : C(unitInterval × D,T)) (hH₀ : ∀ d,H (0,d) = b d) :
    ∃ L : C(StartPieces (f := f) base b × unitInterval,M),
      (∀ z,L (z,0) = (parameterQuotient sq base b z).1.1) ∧
      (∀ z t,projection sq base (L (z,t)) = H (t,(parameterQuotient sq base b z).1.2)) ∧
      ∀ (a : SourceStart (f := f) base b) t,
        L (.inl (a,ULift.up 1),t) =
          L (.inr (⟨(f a.1.1,a.1.2),a.2⟩ : TargetStart base b),t) := by
  classical
  have htarget (x : C) : projection sq base (c x) = base x :=
    ConcreteCategory.congr_hom (TheoremA.mappingCylinderProjection_target_assoc sq base) x
  let a₀ : C(SourceStart (f := f) base b,A) := ⟨fun z ↦ z.1.1,by fun_prop⟩
  let AH : C(unitInterval × SourceStart (f := f) base b,T) :=
    ⟨fun z ↦ H (z.1,z.2.1.2),by fun_prop⟩
  obtain ⟨LA,hLA₀,hLA⟩ := hp _ a₀ AH (fun z ↦ (hH₀ z.1.2).trans z.2.symm)
  let Q := {z : C × (unitInterval × D) // base z.1 = H (z.2.1,z.2.2)}
  let q₀ : C(Q,C) := ⟨fun z ↦ z.1.1,by fun_prop⟩
  let QH : C(unitInterval × Q,T) :=
    ⟨fun z ↦ H (addTime z.2.1.2.1 z.1,z.2.1.2.2),by dsimp only [Q]; fun_prop⟩
  obtain ⟨LQ,hLQ₀,hLQ⟩ := hq Q q₀ QH (by
    intro z
    change H (addTime z.1.2.1 0,z.1.2.2) = base z.1.1
    rw [addTime_zero]
    exact z.2.symm)
  let qstart : C(SourceStart (f := f) base b × TopCat.I,Q) := {
    toFun z := ⟨(f (LA (σ z.2.down,z.1)),(σ z.2.down,z.1.1.2)),hLA _ _⟩
    continuous_toFun := by fun_prop }
  let targetStart : C(TargetStart base b,Q) := {
    toFun z := ⟨(z.1.1,(0,z.1.2)),z.2.trans (hH₀ z.1.2).symm⟩
    continuous_toFun := by fun_prop }
  let G₁ : C((SourceStart (f := f) base b × TopCat.I) × unitInterval,M) :=
    ⟨fun z ↦ l (LA (z.2,z.1.1),ULift.up (addTime z.1.2.down z.2)),by fun_prop⟩
  let G₂ : C((SourceStart (f := f) base b × TopCat.I) × unitInterval,M) :=
    ⟨fun z ↦ c (LQ (remainingTime z.2 (σ z.1.2.down),qstart z.1)),by fun_prop⟩
  have hseam (z : (SourceStart (f := f) base b × TopCat.I) × unitInterval)
      (hz : z.2 = σ z.1.2.down) : G₁ z = G₂ z := by
    change l (LA (z.2,z.1.1),ULift.up (addTime z.1.2.down z.2)) =
      c (LQ (remainingTime z.2 (σ z.1.2.down),qstart z.1))
    rw [hz,addTime_symm,remainingTime_self,hLQ₀]
    exact ConcreteCategory.congr_hom sq.w (LA (σ z.1.2.down,z.1.1))
  let left : C((SourceStart (f := f) base b × TopCat.I) × unitInterval,M) := {
    toFun z := if z.2 ≤ σ z.1.2.down then G₁ z else G₂ z
    continuous_toFun := Continuous.if_le G₁.continuous G₂.continuous
      (by fun_prop) (by fun_prop) hseam }
  let right : C(TargetStart base b × unitInterval,M) :=
    ⟨fun z ↦ c (LQ (z.2,targetStart z.1)),by fun_prop⟩
  let L : C(StartPieces (f := f) base b × unitInterval,M) :=
    (⟨Sum.elim left right,left.continuous.sumElim right.continuous⟩ : C(_,M)).comp
      ⟨fun z ↦ Homeomorph.sumProdDistrib z,Homeomorph.sumProdDistrib.continuous⟩
  refine ⟨L,?_,?_,?_⟩
  · intro z
    rcases z with ⟨a,s⟩ | a
    · change (if (0 : unitInterval) ≤ σ s.down then G₁ ((a,s),0) else G₂ ((a,s),0)) = l (a.1.1,s)
      rw [ite_eq_left (show (0 : unitInterval) ≤ σ s.down from zero_le)]
      change l (LA (0,a),ULift.up (addTime s.down 0)) = _
      rw [hLA₀,addTime_zero]
      rfl
    · change c (LQ (0,targetStart a)) = c a.1.1
      rw [hLQ₀]
      rfl
  · intro z t
    rcases z with ⟨a,s⟩ | a
    · change projection sq base (if t ≤ σ s.down then G₁ ((a,s),t) else G₂ ((a,s),t)) = H (t,a.1.2)
      split_ifs with ht
      · exact (ConcreteCategory.congr_hom (TheoremA.mappingCylinderProjection_cylinder_assoc sq base)
          (LA (t,a),ULift.up (addTime s.down t))).trans (hLA t a)
      · change projection sq base (c (LQ (remainingTime t (σ s.down),qstart (a,s)))) = _
        rw [htarget]
        rw [hLQ]
        change H (addTime (σ s.down) (remainingTime t (σ s.down)),a.1.2) = _
        rw [addTime_remainingTime (le_of_lt (lt_of_not_ge ht))]
    · change projection sq base (c (LQ (t,targetStart a))) = H (t,a.1.2)
      rw [htarget,hLQ]
      change H (addTime 0 t,a.1.2) = _
      rw [zero_addTime]
  · intro a t
    change (if t ≤ σ (1 : unitInterval) then G₁ ((a,ULift.up 1),t)
      else G₂ ((a,ULift.up 1),t)) =
      c (LQ (t,targetStart ⟨(f a.1.1,a.1.2),a.2⟩))
    rw [symm_one]
    split_ifs with ht
    · have ht' : t = 0 := le_antisymm ht (show (0 : unitInterval) ≤ t from zero_le)
      subst t
      change l (LA (0,a),ULift.up (addTime 1 0)) = _
      rw [addTime_zero,hLA₀,hLQ₀]
      exact ConcreteCategory.congr_hom sq.w a.1.1
    · change c (LQ (remainingTime t (σ (1 : unitInterval)),qstart (a,ULift.up 1))) = _
      rw [symm_one,remainingTime_zero]
      apply congrArg c
      apply congrArg (fun z ↦ LQ (t,z))
      apply Subtype.ext
      change (f (LA (σ (1 : unitInterval),a)),σ (1 : unitInterval),a.1.2) =
        (f a.1.1,0,a.1.2)
      rw [symm_one,hLA₀]
      rfl

end Quillen.TheoremB.CompactMappingCylinder
