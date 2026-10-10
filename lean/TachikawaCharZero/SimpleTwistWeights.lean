import TachikawaCharZero.TauPowers
import TachikawaCharZero.TwistedCorner
import TachikawaCharZero.ExtTransport
import OAI.RingTheory.Tachikawa.TwistHom
import OAI.RingTheory.Tachikawa.ScaleDual

/-! Scaling on the actual rational T-character Ext groups. The comparison
acts by H on the dual coordinate of each principal projective, so the
degree-two defect map twoAug also scales by H. Naturality of the four
checked short exact sequences then gives the inverse weight on tau.
The naturality and power argument follows the characteristic-independent
pattern of OpenAI Math Period.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
(Apache-2.0); the short complexes here are the local rational ones. -/
namespace TachikawaCharZero.SimpleTwistWeights
noncomputable section
set_option maxHeartbeats 200000
set_option Elab.async false
open CategoryTheory CategoryTheory.Abelian OAI.Tachikawa Induced Resolution
open scoped ModuleCat.Algebra

variable (H : ℚ) (hH : H ≠ 0)

def scale : T ≃ₐ[ℚ] T where
  toFun a := ⟨a.fst,H • a.snd⟩
  invFun a := ⟨a.fst,H⁻¹ • a.snd⟩
  left_inv a := by
    apply TrivSqZeroExt.ext
    · rfl
    · change H⁻¹ • (H • a.snd)=a.snd
      rw [smul_smul,inv_mul_cancel₀ hH,one_smul]
  right_inv a := by
    apply TrivSqZeroExt.ext
    · rfl
    · change H • (H⁻¹ • a.snd)=a.snd
      rw [smul_smul,mul_inv_cancel₀ hH,one_smul]
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · rfl
    · apply Resolution.dual_ext
      intro r
      change H*(b.snd (r*a.fst)+a.snd (b.fst*r))=
        H*b.snd (r*a.fst)+H*a.snd (b.fst*r)
      exact mul_add _ _ _
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact smul_add H a.snd b.snd
  commutes' c := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact smul_zero H

theorem scale_inl (a : A) : scale H hH (TrivSqZeroExt.inl a)=TrivSqZeroExt.inl a := by
  apply TrivSqZeroExt.ext
  · rfl
  · exact smul_zero H

abbrev twist := SymmetrizingForm.twistFunctor (scale H hH)

instance : (twist H hH).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv (scale H hH).symm.toRingEquiv

def simpleIso : (twist H hH).obj X ≅ X where
  hom := ModuleCat.ofHom
    { toFun := id
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  inv := ModuleCat.ofHom
    { toFun := id
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

def cornerComparison (p : A) :
    (twist H hH).obj (ModuleCat.of T (corner p)) ⟶ ModuleCat.of T (corner p) :=
  TwistedCorner.comparison (scale H hH) (TrivSqZeroExt.inl p) (scale_inl H hH p)

theorem differential_natural {p r : A} (b : A) (hbr : b*r=b) :
    (twist H hH).map (ModuleCat.ofHom (differential (p:=p) b hbr)) ≫
      cornerComparison H hH r =
    cornerComparison H hH p ≫ ModuleCat.ofHom (differential b hbr) :=
  TwistedCorner.differential_natural (scale H hH) (scale_inl H hH p)
    (scale_inl H hH r) (TrivSqZeroExt.inl b)
    (by apply TrivSqZeroExt.ext; exact hbr; simp) (scale_inl H hH b)

def uComparison : (twist H hH).obj UObj ⟶ UObj :=
  ModuleCat.ofHom (X := (twist H hH).obj UObj) (Y := UObj)
    { toFun := fun x => ⟨cornerComparison H hH vertexF x.val, by
        obtain ⟨y,hy⟩ := x.property
        refine ⟨cornerComparison H hH vertexE y, ?_⟩
        rw [← hy]
        exact (congrArg (fun f => f y)
          (differential_natural H hH _ u_fixed_by_f)).symm⟩
      map_add' x y := Subtype.ext ((cornerComparison H hH vertexF).hom.map_add _ _)
      map_smul' r x := Subtype.ext ((cornerComparison H hH vertexF).hom.map_smul _ _) }

def bComparison : (twist H hH).obj B₁Obj ⟶ B₁Obj :=
  ModuleCat.ofHom (X := (twist H hH).obj B₁Obj) (Y := B₁Obj)
    { toFun := fun x => ⟨cornerComparison H hH vertexE x.val, by
        obtain ⟨y,hy⟩ := x.property
        refine ⟨cornerComparison H hH vertexE y, ?_⟩
        rw [← hy]
        exact (congrArg (fun f => f y)
          (differential_natural H hH _ (ell_mem 1))).symm⟩
      map_add' x y := Subtype.ext ((cornerComparison H hH vertexE).hom.map_add _ _)
      map_smul' r x := Subtype.ext ((cornerComparison H hH vertexE).hom.map_smul _ _) }

def cyclesComparison : (twist H hH).obj CyclesObj ⟶ CyclesObj :=
  ModuleCat.ofHom (X := (twist H hH).obj CyclesObj) (Y := CyclesObj)
    { toFun := fun x => ⟨cornerComparison H hH vertexE x.val, by
        have hd := congrArg (fun f => f x.val)
          (differential_natural H hH _ (ell_mem 1))
        change cornerComparison H hH vertexE (teDiff 1 x.val) =
          teDiff 1 (cornerComparison H hH vertexE x.val) at hd
        rw [x.property] at hd
        have hz : cornerComparison H hH vertexE (0 : (twist H hH).obj (ModuleCat.of T TE))=0 :=
          (cornerComparison H hH vertexE).hom.map_zero
        exact hd.symm.trans hz⟩
      map_add' x y := Subtype.ext ((cornerComparison H hH vertexE).hom.map_add _ _)
      map_smul' r x := Subtype.ext ((cornerComparison H hH vertexE).hom.map_smul _ _) }

def initialHom : initialShort.map (twist H hH) ⟶ initialShort where
  τ₁ := uComparison H hH
  τ₂ := cornerComparison H hH vertexF
  τ₃ := (simpleIso H hH).hom
  comm₁₂ := rfl
  comm₂₃ := rfl

def middleHom : middleShort.map (twist H hH) ⟶ middleShort where
  τ₁ := bComparison H hH
  τ₂ := cornerComparison H hH vertexE
  τ₃ := uComparison H hH
  comm₁₂ := rfl
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (congrArg (fun f => f x) (differential_natural H hH _ u_fixed_by_f)).symm

def upperHom : upperShort.map (twist H hH) ⟶ upperShort where
  τ₁ := cyclesComparison H hH
  τ₂ := cornerComparison H hH vertexE
  τ₃ := bComparison H hH
  comm₁₂ := rfl
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (congrArg (fun f => f x) (differential_natural H hH _ (ell_mem 1))).symm

theorem twoAug_natural :
    (twist H hH).map lowerShort.g ≫ (H • (simpleIso H hH).hom) =
      cyclesComparison H hH ≫ lowerShort.g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem initial_natural :
    (initial_shortExact.extClass.mapExactFunctor (twist H hH)).comp
      (Ext.mk₀ (uComparison H hH)) (add_zero 1) =
    (Ext.mk₀ (simpleIso H hH).hom).comp initial_shortExact.extClass (zero_add 1) := by
  erw [Ext.mapExactFunctor_extClass]
  exact ((initial_shortExact.map_of_exact (twist H hH)).extClass_naturality
    initial_shortExact (initialHom H hH))

theorem middle_natural :
    (middle_shortExact.extClass.mapExactFunctor (twist H hH)).comp
      (Ext.mk₀ (bComparison H hH)) (add_zero 1) =
    (Ext.mk₀ (uComparison H hH)).comp middle_shortExact.extClass (zero_add 1) := by
  erw [Ext.mapExactFunctor_extClass]
  exact ((middle_shortExact.map_of_exact (twist H hH)).extClass_naturality
    middle_shortExact (middleHom H hH))

theorem upper_natural :
    (upper_shortExact.extClass.mapExactFunctor (twist H hH)).comp
      (Ext.mk₀ (cyclesComparison H hH)) (add_zero 1) =
    (Ext.mk₀ (bComparison H hH)).comp upper_shortExact.extClass (zero_add 1) := by
  erw [Ext.mapExactFunctor_extClass]
  exact ((upper_shortExact.map_of_exact (twist H hH)).extClass_naturality
    upper_shortExact (upperHom H hH))

theorem homology_natural :
    ((Ext.mk₀ lowerShort.g).mapExactFunctor (twist H hH)).comp
      (Ext.mk₀ (H • (simpleIso H hH).hom)) (add_zero 0) =
    (Ext.mk₀ (cyclesComparison H hH)).comp (Ext.mk₀ lowerShort.g) (zero_add 0) := by
  rw [Ext.mapExactFunctor_mk₀,Ext.mk₀_comp_mk₀,Ext.mk₀_comp_mk₀]
  exact congrArg Ext.mk₀ (twoAug_natural H hH)

theorem push_comparison {A A' B B' Z : ModuleCat T} {a n : ℕ}
    (f : Ext A B a) (f' : Ext A' B' a) (u : A ⟶ A') (v : B ⟶ B')
    (h : f.comp (Ext.mk₀ v) (add_zero a) = (Ext.mk₀ u).comp f' (zero_add a))
    (z : Ext B' Z n) (c : ℕ) (hc : a+n=c) :
    f.comp ((Ext.mk₀ v).comp z (zero_add n)) hc =
      (Ext.mk₀ u).comp (f'.comp z hc) (zero_add c) := by
  rw [← Ext.comp_assoc_of_second_deg_zero,h]
  exact Ext.comp_assoc _ _ _ (zero_add a) hc (by omega)

theorem tau_natural :
    (tau.mapExactFunctor (twist H hH)).comp
      (Ext.mk₀ (H • (simpleIso H hH).hom)) (add_zero 3) =
    (Ext.mk₀ (simpleIso H hH).hom).comp tau (zero_add 3) := by
  simp only [tau,period_apply,Ext.comp_mk₀_id,Ext.mapExactFunctor_comp,
    Ext.comp_assoc_of_third_deg_zero]
  rw [homology_natural H hH]
  rw [push_comparison _ _ _ _ (upper_natural H hH),
    push_comparison _ _ _ _ (middle_natural H hH),
    push_comparison _ _ _ _ (initial_natural H hH)]

def action (n : ℕ) : Ext X X n →ₗ[ℚ] Ext X X n :=
  (ExtTransport.conjugateLinearMap ℚ (simpleIso H hH) n).comp
    ((twist H hH).mapExtLinearMap ℚ X X n)

theorem action_comp {a b c : ℕ} (x : Ext X X a) (y : Ext X X b) (h : a+b=c) :
    action H hH c (x.comp y h) =
      (action H hH a x).comp (action H hH b y) h := by
  change ExtTransport.conjugate _ ((x.comp y h).mapExactFunctor _) = _
  rw [Ext.mapExactFunctor_comp,ExtTransport.conjugate_comp]
  rfl

theorem mk0_scalar : Ext.mk₀ (H • (simpleIso H hH).hom) =
    H • Ext.mk₀ (simpleIso H hH).hom := by
  have h := Ext.mk₀_smul H (simpleIso H hH).hom
  convert h using 1
  all_goals
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change H*(show ℚ from x)=(H*1)*(show ℚ from x)
    rw [mul_one]

theorem action_tau : action H hH 3 tau = H⁻¹ • tau := by
  have hs := congrArg (fun x => (Ext.mk₀ (simpleIso H hH).inv).comp x (zero_add 3))
    (tau_natural H hH)
  have hscalar : H • action H hH 3 tau = tau := by
    rw [mk0_scalar H hH,Ext.comp_smul,Ext.comp_smul] at hs
    change H • action H hH 3 tau = _ at hs
    simpa only [← Ext.comp_assoc_of_second_deg_zero,Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id,Ext.mk₀_id_comp] using hs
  calc
    action H hH 3 tau = H⁻¹ • (H • action H hH 3 tau) := by
      rw [smul_smul,inv_mul_cancel₀ hH,one_smul]
    _ = H⁻¹ • tau := congrArg (fun x => H⁻¹ • x) hscalar

theorem action_tauPower (m : ℕ) :
    action H hH (3*m) (tauPower m) = (H⁻¹)^m • tauPower m := by
  induction m with
  | zero =>
    rw [tauPower_zero]
    change ExtTransport.conjugate _ ((Ext.mk₀ (𝟙 X)).mapExactFunctor _) = _
    rw [Ext.mapExactFunctor_mk₀,CategoryTheory.Functor.map_id,ExtTransport.conjugate_unit]
    simp only [pow_zero,one_smul]
  | succ m ih =>
    rw [tauPower_succ,action_comp,action_tau H hH,ih,
      Ext.smul_comp,Ext.comp_smul,smul_smul,pow_succ']

theorem action_multiple (m : ℕ) (x : Ext X X (3*m)) :
    action H hH (3*m) x = (H⁻¹)^m • x := by
  nth_rw 1 [eq_smul_tauPower m x]
  rw [map_smul,action_tauPower H hH,smul_comm,← eq_smul_tauPower m x]

theorem action_all (n : ℕ) (x : Ext X X n) :
    action H hH n x = (H⁻¹)^(n/3) • x := by
  by_cases hn : n%3=0
  · obtain ⟨m,rfl⟩ := Nat.dvd_of_mod_eq_zero hn
    simpa only [Nat.mul_div_cancel_left m (by omega : 0<3)] using
      action_multiple H hH m x
  · let := Induced.self_ext_off_multiples n hn
    exact Subsingleton.elim _ _

end
end TachikawaCharZero.SimpleTwistWeights
