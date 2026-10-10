import TachikawaCharZero.TwoBranchDelta
import TachikawaCharZero.SignedDeltaMatrices

/-! Subtracting the two actual Delta projections recovers its input.
This proves actual Delta injectivity and projection-pair surjectivity without
assuming the F-Hom profile. Delta surjectivity still needs pair injectivity. -/
namespace TachikawaCharZero.TwoBranchCancellation
noncomputable section
set_option backward.isDefEq.respectTransparency false

section ScalarBlock
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

def block (c₁ c₂ ε : k) : (V × V) →ₗ[k] (V × V) :=
  (c₁ • LinearMap.fst k V V - ε • LinearMap.snd k V V).prod
    (c₂ • LinearMap.fst k V V - ε • LinearMap.snd k V V)

theorem block_injective {c₁ c₂ ε : k} (hc : c₁ ≠ c₂) (hε : ε ≠ 0) :
    Function.Injective (block (V:=V) c₁ c₂ ε) := by
  have hk : ∀ z : V × V, block c₁ c₂ ε z = 0 → z = 0 := by
    rintro ⟨x,y⟩ h
    have h₁ : c₁ • x - ε • y = 0 := congrArg Prod.fst h
    have h₂ : c₂ • x - ε • y = 0 := congrArg Prod.snd h
    have hx : (c₁-c₂) • x = 0 := by
      rw [sub_smul,sub_eq_zero.mp h₁,sub_eq_zero.mp h₂,sub_self]
    have hx0 : x = 0 := (smul_eq_zero.mp hx).resolve_left (sub_ne_zero.mpr hc)
    have hy : ε • y = 0 := by
      rw [hx0,smul_zero,zero_sub,neg_eq_zero] at h₁
      exact h₁
    exact Prod.ext hx0 ((smul_eq_zero.mp hy).resolve_left hε)
  intro z z' h
  apply sub_eq_zero.mp
  apply hk
  rw [map_sub,h,sub_self]

theorem block_surjective {c₁ c₂ ε : k} (hc : c₁ ≠ c₂) (hε : ε ≠ 0) :
    Function.Surjective (block (V:=V) c₁ c₂ ε) := by
  rintro ⟨u,w⟩
  let x := (c₁-c₂)⁻¹ • (u-w)
  let y := ε⁻¹ • (c₁ • x-u)
  have hy : ε • y = c₁ • x-u := by
    dsimp [y]
    rw [smul_smul,mul_inv_cancel₀ hε,one_smul]
  have hx : (c₁-c₂) • x = u-w := by
    dsimp [x]
    rw [smul_smul,mul_inv_cancel₀ (sub_ne_zero.mpr hc),one_smul]
  refine ⟨(x,y),Prod.ext ?_ ?_⟩
  · change c₁ • x - ε • y = u
    rw [hy]
    abel
  · change c₂ • x - ε • y = w
    rw [hy]
    calc
      c₂ • x - (c₁ • x-u) = u-(c₁-c₂) • x := by rw [sub_smul]; abel
      _ = w := by rw [hx]; abel

theorem block_bijective {c₁ c₂ ε : k} (hc : c₁ ≠ c₂) (hε : ε ≠ 0) :
    Function.Bijective (block (V:=V) c₁ c₂ ε) :=
  ⟨block_injective hc hε,block_surjective hc hε⟩

end ScalarBlock

theorem factor_properties {A B : Type*} (f : A → B) (p : B → A)
    (h : Function.Bijective (p ∘ f)) :
    Function.Injective f ∧ Function.Surjective p ∧
      (Function.Surjective f ↔ Function.Injective p) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x y he
    exact h.1 (congrArg p he)
  · intro y
    obtain ⟨x,hx⟩ := h.2 y
    exact ⟨f x,hx⟩
  · intro hf x y he
    obtain ⟨u,rfl⟩ := hf x
    obtain ⟨v,rfl⟩ := hf y
    exact congrArg f (h.1 he)
  · intro hp y
    obtain ⟨x,hx⟩ := h.2 (p y)
    exact ⟨x,hp hx⟩

theorem weight_positive (H : ℚ) (m : ℕ) :
    TwistedBranchWeights.weight H ((3*m:ℕ):ℤ) = (H^m)⁻¹ := by
  simp only [TwistedBranchWeights.weight,Nat.mul_div_cancel_left m (by omega : 0 < 3),
    inv_pow]

theorem weight_negative (H : ℚ) (m : ℕ) :
    TwistedBranchWeights.weight H (-((3*m:ℕ):ℤ)-1) = H^(m+2) := by
  rw [show -((3*m:ℕ):ℤ)-1 = Int.negSucc (3*m) by omega]
  simp only [TwistedBranchWeights.weight,Nat.mul_div_cancel_left m (by omega : 0 < 3)]
  rw [pow_add,mul_comm]

theorem weights_distinct_positive (m : ℕ) (hm : 0 < m) :
    TwistedBranchWeights.weight H₁ ((3*m:ℕ):ℤ) ≠
      TwistedBranchWeights.weight H₂ ((3*m:ℕ):ℤ) := by
  rw [weight_positive,weight_positive]
  exact (sub_ne_zero.mp (positive_determinant_ne_zero m hm)).symm

theorem weights_distinct_negative (m : ℕ) :
    TwistedBranchWeights.weight H₁ (-((3*m:ℕ):ℤ)-1) ≠
      TwistedBranchWeights.weight H₂ (-((3*m:ℕ):ℤ)-1) := by
  rw [weight_negative,weight_negative]
  exact (sub_ne_zero.mp (negative_determinant_ne_zero m)).symm

theorem actual_block_bijective (ε : ℚ) (a : ℤ) (hε : ε ≠ 0)
    (hc : TwistedBranchWeights.weight H₁ a ≠ TwistedBranchWeights.weight H₂ a) :
    Function.Bijective (TwoBranchDelta.pair H₁ H₂ (by norm_num) (by norm_num) a ∘
      TwoBranchDelta.delta H₁ H₂ (by norm_num) (by norm_num) ε a) := by
  have he : TwoBranchDelta.pair H₁ H₂ (by norm_num) (by norm_num) a ∘
      TwoBranchDelta.delta H₁ H₂ (by norm_num) (by norm_num) ε a =
      block (V:=TateProfile.Tate a) (TwistedBranchWeights.weight H₁ a)
        (TwistedBranchWeights.weight H₂ a) ε := by
    funext z
    exact TwoBranchDelta.pair_delta H₁ H₂ (by norm_num) (by norm_num) ε a z.1 z.2
  rw [he]
  exact block_bijective hc hε

theorem actual_properties (ε : ℚ) (a : ℤ) (hε : ε ≠ 0)
    (hc : TwistedBranchWeights.weight H₁ a ≠ TwistedBranchWeights.weight H₂ a) :
    Function.Injective (TwoBranchDelta.delta H₁ H₂ (by norm_num) (by norm_num) ε a) ∧
    Function.Surjective (TwoBranchDelta.pair H₁ H₂ (by norm_num) (by norm_num) a) ∧
      (Function.Surjective (TwoBranchDelta.delta H₁ H₂ (by norm_num) (by norm_num) ε a) ↔
       Function.Injective (TwoBranchDelta.pair H₁ H₂ (by norm_num) (by norm_num) a)) :=
  factor_properties _ _ (actual_block_bijective ε a hε hc)

theorem signed_positive (m : ℕ) (hm : 0 < m) :
    Function.Injective (TwoBranchDelta.delta H₁ H₂ (by norm_num) (by norm_num)
      (SignedDownHom.sign (k:=ℚ) ((3*m:ℕ):ℤ)) ((3*m:ℕ):ℤ)) :=
  (actual_properties _ _ (SignedDeltaMatrices.sign_ne_zero _) (weights_distinct_positive m hm)).1

theorem signed_negative (m : ℕ) :
    Function.Injective (TwoBranchDelta.delta H₁ H₂ (by norm_num) (by norm_num)
      (SignedDownHom.sign (k:=ℚ) (-((3*m:ℕ):ℤ)-1)) (-((3*m:ℕ):ℤ)-1)) :=
  (actual_properties _ _ (SignedDeltaMatrices.sign_ne_zero _) (weights_distinct_negative m)).1

theorem nonzero_degree (ε : ℚ) (a : ℤ) (ha : a ≠ 0) (hε : ε ≠ 0) :
    Function.Injective (TwoBranchDelta.delta H₁ H₂ (by norm_num) (by norm_num) ε a) := by
  cases a with
  | ofNat n =>
    by_cases hn : n%3 = 0
    · have hn0 : n ≠ 0 := by
        intro h
        apply ha
        simp [h]
      have hm : 0 < n/3 := by omega
      rw [show Int.ofNat n = ((3*(n/3):ℕ):ℤ) by
        rw [Int.ofNat_eq_natCast]
        omega]
      exact (actual_properties _ _ hε (weights_distinct_positive (n/3) hm)).1
    · let := TateProfile.nonnegative_zero n hn
      intro x y _
      exact Subsingleton.elim x y
  | negSucc n =>
    by_cases hn : n%3 = 0
    · rw [show Int.negSucc n = -((3*(n/3):ℕ):ℤ)-1 by omega]
      exact (actual_properties _ _ hε (weights_distinct_negative (n/3))).1
    · let : Subsingleton (TateProfile.Tate (Int.negSucc n)) := by
        rw [show Int.negSucc n = -(n:ℤ)-1 by omega]
        exact TateProfile.negative_zero n hn
      intro x y _
      exact Subsingleton.elim x y

theorem signed_nonzero_degree (a : ℤ) (ha : a ≠ 0) :
    Function.Injective (TwoBranchDelta.delta H₁ H₂ (by norm_num) (by norm_num)
      (SignedDownHom.sign (k:=ℚ) a) a) :=
  nonzero_degree _ a ha (SignedDeltaMatrices.sign_ne_zero a)

end
end TachikawaCharZero.TwoBranchCancellation
