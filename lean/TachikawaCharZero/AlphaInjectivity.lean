import TachikawaCharZero.ExtInjectivity
import TachikawaCharZero.TensorBoundary

/-! Multiplication by the actual Yoneda class alpha is injective in every
degree 3m. The proof tensors the four concrete short exact sequences with
S and uses the contravariant Ext sequence, rather than assuming naturality
of arbitrary Kunneth coordinates. -/
namespace TachikawaCharZero.AlphaInjectivity
noncomputable section
open CategoryTheory CategoryTheory.Abelian Induced TensorProfile TensorInflation SplitInflation
open scoped ModuleCat.Algebra

abbrev initialExact := initial_shortExact.map_of_exact tensorLeft
abbrev middleExact := middle_shortExact.map_of_exact tensorLeft
abbrev upperExact := upper_shortExact.map_of_exact tensorLeft
abbrev lowerExact := lower_shortExact.map_of_exact tensorLeft

def splice (m : ℕ) (x : Ext X₂ X₂ (3*m)) : Ext X₂ X₂ (3*(m+1)) :=
  initialExact.extClass.comp (c := 3*(m+1))
    (middleExact.extClass.comp (c := 3*m+2)
      (upperExact.extClass.comp (c := 3*m+1)
        ((Ext.mk₀ (tensorLeft.map lowerShort.g)).comp x (zero_add (3*m)))
        (by omega)) (by omega)) (by omega)

theorem alpha_comp_eq_splice (m : ℕ) (x : Ext X₂ X₂ (3*m)) :
    alpha.comp x (show 3+3*m=3*(m+1) by omega) = splice m x := by
  rw [alpha_eq_tensor_tau]
  simp only [tau, period_apply, Ext.comp_mk₀_id, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_mk₀]
  unfold splice
  rw [Ext.comp_assoc (a₂₃ := 3*m+2) _ _ _ (by omega) (by omega) (by omega),
    Ext.comp_assoc (a₂₃ := 3*m+1) _ _ _ (by omega) (by omega) (by omega),
    Ext.comp_assoc (a₂₃ := 3*m) _ _ _ (by omega) (by omega) (by omega)]

theorem splice_injective (m : ℕ) : Function.Injective (splice m) := by
  let : Subsingleton (Ext (initialShort.map tensorLeft).X₂ X₂ (3*m+2)) :=
    TensorBoundary.tf_ext_zero m
  have hi := ExtInjectivity.connecting initialExact X₂ (3*m+2) (3*(m+1)) (by omega)
  let : Subsingleton (Ext (middleShort.map tensorLeft).X₂ X₂ (3*m+1)) :=
    TensorBoundary.te_ext_zero (3*m+1)
  have hm := ExtInjectivity.connecting middleExact X₂ (3*m+1) (3*m+2) (by omega)
  let : Subsingleton (Ext (upperShort.map tensorLeft).X₂ X₂ (3*m)) :=
    TensorBoundary.te_ext_zero (3*m)
  have hu := ExtInjectivity.connecting upperExact X₂ (3*m) (3*m+1) (by omega)
  have hl := ExtInjectivity.pullback lowerExact X₂ (3*m) TensorBoundary.boundary_ext_zero
  intro x y h
  exact hl (hu (hm (hi h)))

def alphaMap (m : ℕ) : Ext X₂ X₂ (3*m) →ₗ[ℚ] Ext X₂ X₂ (3*(m+1)) :=
  alpha.precompOfLinear ℚ X₂ (by omega)

theorem alphaMap_injective (m : ℕ) : Function.Injective (alphaMap m) := by
  intro x y h
  apply splice_injective m
  have h' : alpha.comp x (show 3+3*m=3*(m+1) by omega) =
      alpha.comp y (show 3+3*m=3*(m+1) by omega) := h
  simpa only [alpha_comp_eq_splice] using h'

theorem alphaMap_eq_zero_iff (m : ℕ) (x : Ext X₂ X₂ (3*m)) :
    alphaMap m x = 0 ↔ x = 0 := (alphaMap m).map_eq_zero_iff (alphaMap_injective m)

end
end TachikawaCharZero.AlphaInjectivity
