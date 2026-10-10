import TachikawaCharZero.SourceSideProjectivity
import TachikawaCharZero.SeparatedStableLifts
import OAI.RingTheory.Tachikawa.SideProjectivity

/-! Fix the actual finite bimodule Y as the fourth cosyzygy of the chosen
signed source cokernel in reflected degree five. Its side projectivity is
inherited from the actual source; nonprojectivity survives every cosyzygy.
No evaluated W profile or nonzero tensor-Hom evaluation is asserted here. -/
namespace TachikawaCharZero.FixedBimoduleY
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra

section Generic
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

theorem projective_of_cosyzygy_projective (t : SymmetrizingForm (k := k) (R := R))
    (M : FiniteModule k R) (hp : Module.Projective R (M.cosyzygy t).obj) :
    Module.Projective R M.obj := by
  let : Module.Projective R
      ((Fin (Module.finrank k M) → R) ⧸ LinearMap.range (M.embed t)) := hp
  exact projective_kernel_of_surjective (M.embed t) (LinearMap.range (M.embed t)).mkQ
    (M.embed_injective t) (Submodule.mkQ_surjective _)
    (fun x => Submodule.Quotient.mk_eq_zero _)

theorem negative_nonprojective (t : SymmetrizingForm (k := k) (R := R))
    (M : FiniteModule k R) (hM : ¬ Module.Projective R M.obj) (n : ℕ) :
    ¬ Module.Projective R (M.negative t n).obj := by
  induction n with
  | zero => exact hM
  | succ n ih =>
    intro hp
    exact ih (projective_of_cosyzygy_projective t (M.negative t n) hp)

end Generic

open ScalingSocle
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing

def form : SymmetrizingForm (k := ℚ) (R := EE) :=
  Enveloping.envelopingForm Starting.E_form Starting.E_form

def N : FiniteModule ℚ EE := TwistedStableGate.sourceCoker 5

def Y : FiniteModule ℚ EE := N.negative form 4

theorem N_left_projective : Module.Projective E (Enveloping.Obj N.obj) :=
  SourceSideProjectivity.reflectedCoker_left_projective 4 (le_refl 4)

theorem N_right_projective : Module.Projective Eᵐᵒᵖ (Enveloping.Obj N.obj) :=
  SourceSideProjectivity.reflectedCoker_right_projective 4 (le_refl 4)

theorem Y_side_projective : Module.Projective E (Enveloping.Obj Y.obj) ∧
    Module.Projective Eᵐᵒᵖ (Enveloping.Obj Y.obj) := by
  let := N_left_projective
  let := N_right_projective
  exact Enveloping.negative_side_projective Starting.E_form Starting.E_form N 4

theorem Y_nonprojective : ¬ Module.Projective EE Y.obj := by
  apply negative_nonprojective form N _ 4
  exact SeparatedStableLifts.sourceCoker_nonprojective 5 (le_refl 5)

theorem Y_finite : Module.Finite EE Y.obj := Y.finite

end
end TachikawaCharZero.FixedBimoduleY
