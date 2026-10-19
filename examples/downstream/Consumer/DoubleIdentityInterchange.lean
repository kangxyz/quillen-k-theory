/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.IdentityActionInterchangeSign

/-!
# Original K-zero and higher identity-action signs in a separate package

These clients use two independent natural automorphisms of the identity.
They retain the original K-groups and actual self-track operation, with no
assumed scalar commutation. Repeated action is only claimed to be two-torsion.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true
open CategoryTheory Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u v
namespace DoubleIdentityInterchangeConsumer
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The two orders cancel already on the original K-zero input. -/
theorem kZero_opposite_orders_cancel (e e' : 𝟭 (SmallModel C) ≅ 𝟭 (SmallModel C))
    (a : W.K 0) :
    originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (modelOf W)) e') 1
        (originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (modelOf W)) e) 0 a) *
      originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (modelOf W)) e) 1
        (originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (modelOf W)) e') 0 a) = 1 := by
  rw [originalKIdentityAction_interchange_sign W e e' 0 a]
  exact inv_mul_cancel _

/-- Every original nonnegative degree has the corresponding repeated-action two-torsion law. -/
theorem same_action_two_torsion (e : 𝟭 (SmallModel C) ≅ 𝟭 (SmallModel C))
    (n : ℕ) (a : W.K n) :
    (originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (modelOf W)) e) (n + 1)
      (originalKSelfTrackOperation W W
        (prespectrumIsoHomotopy (𝟙 (modelOf W)) e) n a)) ^ 2 = 1 := by
  let b := originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (modelOf W)) e) (n + 1)
    (originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (modelOf W)) e) n a)
  have hb : b = b⁻¹ := originalKIdentityAction_interchange_sign W e e n a
  calc
    b ^ 2 = b * b := pow_two b
    _ = b⁻¹ * b := congrArg (fun c ↦ c * b) hb
    _ = 1 := inv_mul_cancel b

end DoubleIdentityInterchangeConsumer
