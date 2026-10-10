import TachikawaCharZero.TensorTwistWeights
import TachikawaCharZero.TateProfile
import TachikawaCharZero.CompleteTwistSeam
import TachikawaCharZero.ScalingSocle

/-! Genuine complete-resolution scaling weights in positive degrees and
every negative degree, including -1. Symmetric free-Hom duality uses the inverse
ordinary twist and the actual H^2 form multiplier. The pointwise fixed module
also gives the identity action at zero. -/
namespace TachikawaCharZero.TateTwistWeights
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Abelian OAI.Tachikawa TensorProfile TensorTwistWeights
open SplitInflation
open scoped TensorProduct ModuleCat.Algebra

variable (H : ℚ) (hH : H ≠ 0)

abbrev cochainMap := StableSeam.finiteX.completeTwistHom TateProfile.form
  (TensorTwistWeights.scale H hH) (TensorTwistWeights.simpleIso H hH)
abbrev action (a : ℤ) := VectorSplit.Hmap (cochainMap H hH) a

theorem scale_eq_socle : TensorTwistWeights.scale H hH = ScalingSocle.scaling H hH := by
  apply AlgEquiv.ext
  intro r
  induction r using TensorProduct.inductionOn with
  | add r s hr hs =>
    simp only [map_add,hr,hs]
    exact ((ScalingSocle.scaling H hH).map_add r s).symm
  | tmul a b => rfl

theorem zero (x : TateProfile.Tate 0) : action H hH 0 x=x :=
  CompleteTwistSeam.zero StableSeam.finiteX TateProfile.form
    (TensorTwistWeights.scale H hH) (TensorTwistWeights.simpleIso H hH)
    (fun _ => rfl) x

theorem scale_inverse : (TensorTwistWeights.scale H hH).symm =
    TensorTwistWeights.scale H⁻¹ (inv_ne_zero hH) := by
  apply AlgEquiv.ext
  intro r
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => simp only [map_add,hr,hs]
  | tmul a b => rfl

def inverseIso : (SymmetrizingForm.twistFunctor (TensorTwistWeights.scale H hH).symm).obj X₂ ≅ X₂ where
  hom := ModuleCat.ofHom
    (X := (SymmetrizingForm.twistFunctor (TensorTwistWeights.scale H hH).symm).obj X₂) (Y := X₂)
    { toFun := id
      map_add' _ _ := rfl
      map_smul' r x := by
        apply groundEquiv.injective
        change groundEquiv (TensorTwistWeights.scale H hH r • (show X₂ from x)) =
          groundEquiv (r • (show X₂ from x))
        rw [groundEquiv_action,groundEquiv_action,character_scale] }
  inv := ModuleCat.ofHom (X := X₂)
    (Y := (SymmetrizingForm.twistFunctor (TensorTwistWeights.scale H hH).symm).obj X₂)
    { toFun := id
      map_add' _ _ := rfl
      map_smul' r x := by
        apply groundEquiv.injective
        change groundEquiv (r • x) = groundEquiv (TensorTwistWeights.scale H hH r • x)
        rw [groundEquiv_action,groundEquiv_action,character_scale] }
  hom_inv_id := rfl
  inv_hom_id := rfl

theorem ordinary_of_eq (σ : E ≃ₐ[ℚ] E) (hσ : σ=TensorTwistWeights.scale H hH)
    (e : (SymmetrizingForm.twistFunctor σ).obj X₂ ≅ X₂) (he : ∀ x, e.hom x=x)
    (n : ℕ) (x : Ext X₂ X₂ n) :
    extIso (k:=ℚ) e e n (x.mapExactFunctor (SymmetrizingForm.twistFunctor σ)) =
      (H⁻¹)^(n/3) • x := by
  subst σ
  have heq : e=TensorTwistWeights.simpleIso H hH := by
    apply Iso.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact he z
  rw [heq]
  exact TensorTwistWeights.action_all H hH n x

theorem inverse_ordinary (n : ℕ) (x : Ext X₂ X₂ n) :
    extIso (k:=ℚ) (inverseIso H hH) (inverseIso H hH) n
      (x.mapExactFunctor (SymmetrizingForm.twistFunctor (TensorTwistWeights.scale H hH).symm)) =
      H^(n/3) • x := by
  simpa only [inv_inv] using ordinary_of_eq H⁻¹ (inv_ne_zero hH)
    (TensorTwistWeights.scale H hH).symm (scale_inverse H hH)
    (inverseIso H hH) (fun _ => rfl) n x

theorem form_scale (r : E) :
    TateProfile.form.linear (TensorTwistWeights.scale H hH r)=H^2*TateProfile.form.linear r := by
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => simp only [map_add,hr,hs,mul_add]
  | tmul a b =>
    change (H*a.snd 1)*(H*b.snd 1)=H^2*(a.snd 1*b.snd 1)
    ring

theorem negative_one (x : TateProfile.Tate (-1)) :
    action H hH (-1) x=H^2 • x :=
  CompleteTwistSeam.negative_one StableSeam.finiteX TateProfile.form
    (TensorTwistWeights.scale H hH) (TensorTwistWeights.simpleIso H hH)
    (fun _ => rfl) (H^2) (form_scale H hH) x

theorem positive (n : ℕ) (x : TateProfile.Tate ((n+1:ℕ):ℤ)) :
    action H hH _ x = (H⁻¹)^((n+1)/3) • x := by
  apply StableSeam.finiteX.completeTwistHom_positive TateProfile.form
    (TensorTwistWeights.scale H hH) (TensorTwistWeights.simpleIso H hH) n _
  intro z
  exact TensorTwistWeights.action_all H hH (n+1) z

theorem negative (n : ℕ) (x : TateProfile.Tate (Int.negSucc (n+1))) :
    action H hH _ x = (H^2*H^((n+1)/3)) • x := by
  apply StableSeam.finiteX.completeTwistHom_negative TateProfile.form
    (TensorTwistWeights.scale H hH) (TensorTwistWeights.simpleIso H hH)
    (fun _ => rfl) (inverseIso H hH) (fun _ => rfl) n (H^2) (H^((n+1)/3))
  · exact form_scale H hH
  · exact inverse_ordinary H hH (n+1)

theorem positive_multiple (m : ℕ) (hm : 0 < m) (x : TateProfile.Tate ((3*m:ℕ):ℤ)) :
    action H hH _ x = (H⁻¹)^m • x := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  have h := positive H hH (3*n+2)
  have he : 3*n+2+1=3*(n+1) := by omega
  rw [he] at h
  simpa only [Nat.mul_div_cancel_left (n+1) (by omega : 0<3)] using h x

theorem negative_positive_multiple (m : ℕ) (hm : 0 < m) (x : TateProfile.Tate (-((3*m:ℕ):ℤ)-1)) :
    action H hH _ x = H^(m+2) • x := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  have h := negative H hH (3*n+2)
  have he : Int.negSucc (3*n+2+1) = -((3*(n+1):ℕ):ℤ)-1 := by omega
  rw [he] at h
  simpa only [show 3*n+2+1=3*(n+1) by omega,
    Nat.mul_div_cancel_left (n+1) (by omega : 0<3),← pow_add,
    show 2+(n+1)=n+1+2 by omega] using h x

theorem negative_multiple (m : ℕ) (x : TateProfile.Tate (-((3*m:ℕ):ℤ)-1)) :
    action H hH _ x = H^(m+2) • x := by
  cases m with
  | zero => exact negative_one H hH x
  | succ m => exact negative_positive_multiple H hH (m+1) (by omega) x

theorem nonnegative_multiple (m : ℕ) (x : TateProfile.Tate ((3*m:ℕ):ℤ)) :
    action H hH _ x = (H⁻¹)^m • x := by
  cases m with
  | zero =>
    change action H hH 0 x = (H⁻¹)^0 • x
    simpa only [pow_zero,one_smul] using zero H hH x
  | succ m => exact positive_multiple H hH (m+1) (by omega) x

end
end TachikawaCharZero.TateTwistWeights
