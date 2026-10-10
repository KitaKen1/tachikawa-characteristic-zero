import TachikawaCharZero.SignedCompleteHomComparison

/-! Natural operations and componentwise linear comparisons for the
actual signed Hom differential. The component-equivalence strategy
adapts pinned OpenAI Math DownHom.lean 361--407; evaluation naturality
adapts lines 534--595 (Apache-2.0, commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). All minus signs and scalar
actions are retained over an arbitrary field. -/
namespace TachikawaCharZero.SignedCochainTransport
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open OAI.Tachikawa SignedDownHom SignedCompleteHomComparison
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q U : ChainComplex (ModuleCat.{0} R) ℤ}

theorem closed_smul {a : ℤ} (c : k) {f : Cochain P Q a} (hf : Closed (k:=k) f) :
    Closed (k:=k) (c • f) := by
  unfold SignedDownHom.Closed at *
  rw [diff_smul,hf,smul_zero]

theorem diff_pre (u : U ⟶ P) {a : ℤ} (f : Cochain P Q a) :
    diff (k:=k) (pre u f)=pre u (diff (k:=k) f) := by
  funext i j h
  simp only [diff,pre,comp_sub,Linear.comp_smul,Category.assoc]
  rw [← u.comm_assoc i (i-1)]

theorem diff_post {a : ℤ} (f : Cochain P Q a) (u : Q ⟶ U) :
    diff (k:=k) (post f u)=post (diff (k:=k) f) u := by
  funext i j h
  simp only [diff,post,sub_comp,Linear.smul_comp,Category.assoc,u.comm]

theorem pre_closed (u : U ⟶ P) {a : ℤ} {f : Cochain P Q a} (hf : Closed (k:=k) f) :
    Closed (k:=k) (pre u f) := by
  unfold SignedDownHom.Closed at *
  rw [diff_pre,hf]
  funext i j h
  simp only [pre,SignedDownHom.zero_apply,comp_zero]

theorem post_closed {a : ℤ} {f : Cochain P Q a} (hf : Closed (k:=k) f) (u : Q ⟶ U) :
    Closed (k:=k) (post f u) := by
  unfold SignedDownHom.Closed at *
  rw [diff_post,hf]
  funext i j h
  simp only [post,SignedDownHom.zero_apply,zero_comp]

section Components
variable {R' : Type} [Ring R'] [Algebra k R']
variable {P' Q' : ChainComplex (ModuleCat.{0} R') ℤ}
variable (e : ∀ i j, (P.X i ⟶ Q.X j) ≃ₗ[k] (P'.X i ⟶ Q'.X j))

def cochainEquiv (a : ℤ) : Cochain P Q a ≃ₗ[k] Cochain P' Q' a where
  toFun f i j h := e i j (f i j h)
  invFun f i j h := (e i j).symm (f i j h)
  left_inv f := by funext i j h; exact (e i j).symm_apply_apply _
  right_inv f := by funext i j h; exact (e i j).apply_symm_apply _
  map_add' f g := by funext i j h; exact (e i j).map_add _ _
  map_smul' c f := by funext i j h; exact (e i j).map_smul c _

variable (hpre : ∀ i l j (f : P.X l ⟶ Q.X j),
    e i j (P.d i l ≫ f)=P'.d i l ≫ e l j f)
  (hpost : ∀ i j m (f : P.X i ⟶ Q.X j),
    e i m (f ≫ Q.d j m)=e i j f ≫ Q'.d j m)
include hpre hpost

theorem cochainEquiv_diff {a : ℤ} (f : Cochain P Q a) :
    cochainEquiv e (a+1) (diff (k:=k) f)=diff (k:=k) (cochainEquiv e a f) := by
  funext i j h
  change e i j (_-_)=_-_
  rw [map_sub,map_smul,hpre,hpost]
  rfl

theorem cochainEquiv_diffAt {a : ℤ} (f : Cochain P Q (a-1)) :
    cochainEquiv e a (diffAt (k:=k) f)=diffAt (k:=k) (cochainEquiv e (a-1) f) := by
  funext i j h
  change e i j (_-_)=_-_
  rw [map_sub,map_smul,hpre,hpost]
  rfl

theorem cochainEquiv_closed_iff {a : ℤ} (f : Cochain P Q a) :
    Closed (k:=k) (cochainEquiv e a f) ↔ Closed (k:=k) f := by
  unfold SignedDownHom.Closed
  rw [← cochainEquiv_diff e hpre hpost]
  exact (cochainEquiv e (a+1)).map_eq_zero_iff

theorem cochainEquiv_boundary_iff {a : ℤ} (f : Cochain P Q a) :
    Boundary (k:=k) (cochainEquiv e a f) ↔ Boundary (k:=k) f := by
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨(cochainEquiv e (a-1)).symm g,?_⟩
    apply (cochainEquiv e a).injective
    rw [cochainEquiv_diffAt e hpre hpost,LinearEquiv.apply_symm_apply,hg]
  · rintro ⟨g,rfl⟩
    exact ⟨cochainEquiv e (a-1) g,(cochainEquiv_diffAt e hpre hpost g).symm⟩
end Components

section Evaluation
variable {N : ModuleCat.{0} R} (ε : Q.X 0 ⟶ N) (hε : Q.d 1 0 ≫ ε=0)

theorem eval_sub {a : ℤ} (f g : Cochain P Q a) (hf : Closed (k:=k) f)
    (hg : Closed (k:=k) g) :
    evalClass ε hε (f-g) (closed_sub hf hg)=evalClass ε hε f hf-evalClass ε hε g hg := by
  unfold evalClass
  rw [← map_sub]
  apply congrArg (VectorSplit.quotient _ a)
  apply Subtype.ext
  change (f a 0 _-g a 0 _) ≫ ε=f a 0 _ ≫ ε-g a 0 _ ≫ ε
  rw [sub_comp]

theorem eval_smul {a : ℤ} (c : k) (f : Cochain P Q a) (hf : Closed (k:=k) f) :
    evalClass ε hε (c • f) (closed_smul c hf)=c • evalClass ε hε f hf := by
  unfold evalClass
  rw [← map_smul]
  apply congrArg (VectorSplit.quotient _ a)
  apply Subtype.ext
  change (c • f a 0 _) ≫ ε=c • (f a 0 _ ≫ ε)
  rw [Linear.smul_comp]
end Evaluation

section Functor
variable (F : ModuleCat.{0} R ⥤ ModuleCat.{0} R) [F.Additive] [F.Linear k]

abbrev mapComplex (P : ChainComplex (ModuleCat.{0} R) ℤ) :=
  (F.mapHomologicalComplex (.down ℤ)).obj P

def mapCochain {a : ℤ} (f : Cochain P Q a) :
    Cochain (mapComplex F P) (mapComplex F Q) a := fun i j h => F.map (f i j h)

theorem map_diff {a : ℤ} (f : Cochain P Q a) :
    mapCochain F (diff (k:=k) f)=diff (k:=k) (mapCochain F f) := by
  funext i j h
  change F.map (_-_) = _-_
  rw [F.map_sub,F.map_smul,F.map_comp,F.map_comp]
  rfl

theorem map_closed {a : ℤ} {f : Cochain P Q a} (hf : Closed (k:=k) f) :
    Closed (k:=k) (mapCochain F f) := by
  unfold SignedDownHom.Closed at *
  rw [← map_diff,hf]
  funext i j h
  simp only [mapCochain,SignedDownHom.zero_apply,F.map_zero]

variable {N : ModuleCat.{0} R} (ε : P.X 0 ⟶ N) (hε : P.d 1 0 ≫ ε=0)
  (u : P ⟶ mapComplex F P) (u₀ : N ⟶ F.obj N)
  (hu : u.f 0 ≫ F.map ε=ε ≫ u₀)

include hε in
theorem map_augmentation_zero : (mapComplex F P).d 1 0 ≫ F.map ε=0 := by
  change F.map (P.d 1 0) ≫ F.map ε=0
  rw [← F.map_comp,hε,F.map_zero]

theorem eval_pre_functor {a : ℤ} (f : Cochain P P a) (hf : Closed (k:=k) f) :
    evalClass (F.map ε) (map_augmentation_zero F ε hε)
      (pre u (mapCochain F f)) (pre_closed u (map_closed F hf)) =
    VectorSplit.Hmap (completeFunctorHom (k:=k) F P P N u) a (evalClass ε hε f hf) := by
  unfold evalClass
  rw [VectorSplit.Hmap_quotient]
  apply congrArg (VectorSplit.quotient _ a)
  apply Subtype.ext
  change (u.f a ≫ F.map (f a 0 _)) ≫ F.map ε=u.f a ≫ F.map (f a 0 _ ≫ ε)
  rw [F.map_comp,Category.assoc]

include hu in
omit [F.Linear k] in
theorem eval_post_lift {a : ℤ} (g : Cochain P P a) (hg : Closed (k:=k) g) :
    evalClass (F.map ε) (map_augmentation_zero F ε hε)
      (post g u) (post_closed hg u) =
    VectorSplit.Hmap (completeHomMap (k:=k) P u₀) a (evalClass ε hε g hg) := by
  unfold evalClass
  rw [VectorSplit.Hmap_quotient]
  apply congrArg (VectorSplit.quotient _ a)
  apply Subtype.ext
  change (g a 0 _ ≫ u.f 0) ≫ F.map ε=(g a 0 _ ≫ ε) ≫ u₀
  rw [Category.assoc,hu,Category.assoc]
end Functor

end
end TachikawaCharZero.SignedCochainTransport
