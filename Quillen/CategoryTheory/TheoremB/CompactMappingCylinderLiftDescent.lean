import Quillen.CategoryTheory.TheoremB.CompactMappingCylinderLiftFormula
import Quillen.Topology.HomotopyLifting.Compact.Stationary

/-! # Descent of the original finite mapping-cylinder lift -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology unitInterval
universe u
namespace Quillen.TheoremB.CompactMappingCylinder
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)
  {D : Type u} [TopologicalSpace D] (b : C(D,T))

/-- The only identifications of the original piecewise lift are its literal
cap seam. Interior representatives and target representatives are retained. -/
theorem piece_lift_factorsThrough
    (L : C(StartPieces (f := f) base b × unitInterval,M))
    (hcap : ∀ (a : SourceStart (f := f) base b) t,
      L (.inl (a,ULift.up 1),t) =
        L (.inr (⟨(f a.1.1,a.1.2),a.2⟩ : TargetStart base b),t)) :
    Function.FactorsThrough L (fun z ↦ (parameterQuotient sq base b z.1,z.2)) := by
  have hi : Function.Injective (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) := by
    intro a a' h
    exact congrArg Prod.fst h
  have hc : Function.Injective c :=
    Types.pushoutCocone_inr_injective_of_isColimit (sq.map (forget TopCat)).isColimit hi
  have interior (a a' : SourceStart (f := f) base b) (s s' : TopCat.I)
      (hs : s ≠ ULift.up 1)
      (hm : l (a.1.1,s) = l (a'.1.1,s')) (hd : a.1.2 = a'.1.2) :
      (a,s) = (a',s') := by
    have hn : (a.1.1,s) ∉ Set.range (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) := by
      rintro ⟨x,hx⟩
      exact hs (congrArg Prod.snd hx).symm
    have he := pushout_cell_eq_of_not_mem_range sq hn hm
    have hfirst : a.1.1 = a'.1.1 := congrArg (fun z : A × TopCat.I ↦ z.1) he
    have hsecond : s = s' := congrArg (fun z : A × TopCat.I ↦ z.2) he
    have ha : a = a' := Subtype.ext (Prod.ext hfirst hd)
    exact Prod.ext ha hsecond
  have mixed (a : SourceStart (f := f) base b) (s : TopCat.I)
      (a' : TargetStart base b) (t : unitInterval)
      (hm : l (a.1.1,s) = c a'.1.1) (hd : a.1.2 = a'.1.2) :
      L (.inl (a,s),t) = L (.inr a',t) := by
    obtain ⟨x,hx,hf⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      (sq.map (forget TopCat)).isColimit hi (a.1.1,s) a'.1.1).mp hm
    have hx₁ : x = a.1.1 := congrArg Prod.fst hx
    have hs : s = ULift.up 1 := (congrArg Prod.snd hx).symm
    rw [hs,hcap]
    apply congrArg (fun z ↦ L (.inr z,t))
    apply Subtype.ext
    exact Prod.ext (hx₁ ▸ hf) hd
  rintro ⟨z,t⟩ ⟨z',t'⟩ h
  have ht : t = t' := congrArg Prod.snd h
  subst t'
  have hm := congrArg (fun z ↦ z.1.1.1) h
  have hd := congrArg (fun z ↦ z.1.1.2) h
  rcases z with ⟨a,s⟩ | a <;> rcases z' with ⟨a',s'⟩ | a'
  · change l (a.1.1,s) = l (a'.1.1,s') at hm
    change a.1.2 = a'.1.2 at hd
    by_cases hs : s = ULift.up 1
    · by_cases hs' : s' = ULift.up 1
      · subst s
        subst s'
        rw [hcap,hcap]
        have hff : f a.1.1 = f a'.1.1 := hc
          ((ConcreteCategory.congr_hom sq.w a.1.1).symm.trans
            (hm.trans (ConcreteCategory.congr_hom sq.w a'.1.1)))
        exact congrArg (fun z ↦ L (.inr z,t)) (Subtype.ext (Prod.ext hff hd))
      · exact congrArg (fun x ↦ L (.inl x,t)) (interior a' a s' s hs' hm.symm hd.symm).symm
    · exact congrArg (fun x ↦ L (.inl x,t)) (interior a a' s s' hs hm hd)
  · exact mixed a s a' t hm hd
  · exact (mixed a' s' a t hm.symm hd.symm).symm
  · exact congrArg (fun x ↦ L (.inr x,t)) (Subtype.ext (Prod.ext (hc hm) hd))

/-- Lift any displayed homotopy on a locally compact test whose original
matching locus is closed. This is an actual continuous lift on that test,
not a global path-space lifting function. -/
theorem homotopy_lift_of_closed_matching [LocallyCompactSpace D]
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (a : C(D,M)) (H : C(unitInterval × D,T))
    (hH₀ : ∀ d,H (0,d) = projection sq base (a d))
    (hc : IsClosed (Set.ofPred (fun z : M × D ↦ projection sq base z.1 = H (0,z.2)))) :
    ∃ L : C(unitInterval × D,M),(∀ d,L (0,d) = a d) ∧
      ∀ t d,projection sq base (L (t,d)) = H (t,d) := by
  let b : C(D,T) := ⟨fun d ↦ H (0,d),by fun_prop⟩
  obtain ⟨G,hG₀,hG,hcap⟩ := exists_piece_lift sq base b hp hq H (fun _ ↦ rfl)
  have hQ := parameterQuotient_isQuotientMap sq base b hc
  let QI : C(StartPieces (f := f) base b × unitInterval,CylinderStart sq base b × unitInterval) :=
    (parameterQuotient sq base b).prodMap (ContinuousMap.id _)
  have hQI : IsQuotientMap QI := quotientMap_prod_parameter (D := unitInterval) hQ
  let R := hQI.lift G (piece_lift_factorsThrough sq base b G hcap)
  have hR : R.comp QI = G := hQI.lift_comp G _
  let L : C(unitInterval × D,M) := R.comp
    ⟨fun z ↦ (⟨(a z.2,z.2),(hH₀ z.2).symm⟩,z.1),by fun_prop⟩
  refine ⟨L,?_,?_⟩
  · intro d
    obtain ⟨z,hz⟩ := hQ.surjective (⟨(a d,d),(hH₀ d).symm⟩ : CylinderStart sq base b)
    have hh := ContinuousMap.congr_fun hR (z,0)
    change R (parameterQuotient sq base b z,0) = G (z,0) at hh
    change R (⟨(a d,d),(hH₀ d).symm⟩,0) = a d
    rw [← hz,hh,hG₀]
    exact congrArg (fun z ↦ z.1.1) hz
  · intro t d
    obtain ⟨z,hz⟩ := hQ.surjective (⟨(a d,d),(hH₀ d).symm⟩ : CylinderStart sq base b)
    have hh := ContinuousMap.congr_fun hR (z,t)
    change R (parameterQuotient sq base b z,t) = G (z,t) at hh
    change projection sq base (R (⟨(a d,d),(hH₀ d).symm⟩,t)) = H (t,d)
    rw [← hz,hh,hG]
    exact congrArg (fun d ↦ H (t,d)) (congrArg (fun z ↦ z.1.2) hz)

end Quillen.TheoremB.CompactMappingCylinder
