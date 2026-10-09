import Quillen.Topology.HomotopyFiber.Exactness

/-! # Pointed-set exactness, including connected components

The source exactness proof does not require a group operation or a nonempty cube
index. This version includes the π₀ tail using actual homotopy classes.
-/

noncomputable section
universe w u v

namespace Quillen.HomotopyFiber
variable {N : Type w} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (y : Y) (x : X) (h : f x = y)

/-- A constant continuous map sends every homotopy class to the constant class,
without requiring a group structure. -/
lemma homotopyGroupMap_const_apply (a : HomotopyGroup N X x) :
    homotopyGroupMap (ContinuousMap.const X y) rfl a =
      (Quotient.mk' GenLoop.const : HomotopyGroup N Y y) := by
  refine Quotient.inductionOn a (fun p => ?_)
  change Quotient.mk' (genLoopPostcomp (ContinuousMap.const X y) rfl p) = _
  rw [genLoopPostcomp_constant]
  rfl

/-- Pointed-set image-equals-null-preimage for arbitrary cube index types. -/
theorem mem_range_projection_iff_constant (a : HomotopyGroup N X x) :
    a ∈ Set.range (homotopyGroupMap (N := N) (projection f y)
      (projection_basepoint f y x h)) ↔
      homotopyGroupMap f h a = (Quotient.mk' GenLoop.const : HomotopyGroup N Y y) := by
  constructor
  · rintro ⟨b, rfl⟩
    rw [← homotopyGroupMap_comp]
    have hh := homotopyGroupMap_eq_of_based_homotopy (N := N)
      (show (f.comp (projection f y)) (basepoint f y x h) = y from h) rfl
      (projectionNullhomotopy f y) (projectionNullhomotopy_basepoint f y x h)
    exact (congrFun hh b).trans (homotopyGroupMap_const_apply y _ b)
  · refine Quotient.inductionOn a (fun p hp => ?_)
    change Quotient.mk' (genLoopPostcomp f h p) = Quotient.mk' GenLoop.const at hp
    obtain ⟨H⟩ := Quotient.exact hp
    refine ⟨Quotient.mk' (liftGenLoop f y x h p H), ?_⟩
    change Quotient.mk' (genLoopPostcomp (projection f y)
      (projection_basepoint f y x h) (liftGenLoop f y x h p H)) = Quotient.mk' p
    rw [genLoopPostcomp_liftGenLoop]

/-- Exactness of π₀(HF(f)) → π₀(X) → π₀(Y) as pointed sets. -/
theorem piZero_exact :
    Set.range (homotopyGroupMap (N := Fin 0) (projection f y)
      (projection_basepoint f y x h)) =
      {a | homotopyGroupMap f h a =
        (Quotient.mk' GenLoop.const : HomotopyGroup.Pi 0 Y y)} := by
  ext a
  exact mem_range_projection_iff_constant f y x h a

end Quillen.HomotopyFiber
