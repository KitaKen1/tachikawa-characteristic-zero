import TachikawaCharZero.SignedTensorCoker
import TachikawaCharZero.CornerTensorExt
import TachikawaCharZero.EvaluatedWProfile

/-! The complete tensor fiber has maps to X only at degrees 0 and 3.
This determines vanishing of the actual evaluated W away from -3 and 0.
Dimensions at those two degrees and branch normalization are separate. -/
namespace TachikawaCharZero.ReverseCorner
noncomputable section
set_option backward.isDefEq.respectTransparency false
open TachikawaCharZero.Resolution TachikawaCharZero.Starting OAI.Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra

local instance (j : ℤ) : Module.Finite T (inducedForward.X j) :=
  inducedForward_term_finiteT j
local instance (j : ℤ) : Module.Finite T (inducedReverse.X j) :=
  inducedReverse_term_finiteT j
local instance (j : ℤ) : Module.Projective T (inducedForward.X j) :=
  inducedForward_term_moduleProjective j
local instance (j : ℤ) : Module.Projective T (inducedReverse.X j) :=
  inducedReverse_term_moduleProjective j
local instance (j : ℤ) : FiniteDimensional ℚ (inducedForward.X j) :=
  inducedForward_term_finite j
local instance (j : ℤ) : FiniteDimensional ℚ (inducedReverse.X j) :=
  inducedReverse_term_finite j
local instance : Module E SocleBimodule.X :=
  inferInstanceAs (Module TensorProfile.E SocleBimodule.X)
local instance : IsScalarTower ℚ E SocleBimodule.X :=
  inferInstanceAs (IsScalarTower ℚ TensorProfile.E SocleBimodule.X)

def natCornerTermIso (n : ℕ) : natForward.X n ≅ Induced.complex.X n :=
  (HomologicalComplex.eval (ModuleCat T) (.down ℕ) n).mapIso natCornerIso

theorem inducedForwardHom_zero (j : ℤ) (hj : j≠0)
    (f : inducedForward.X j ⟶ Induced.X) : f=0 := by
  cases j with
  | ofNat n =>
    have h : (natCornerTermIso n).inv ≫ f = 0 :=
      CornerTensorExt.jHom_zero n (by intro hn; subst n; exact hj rfl) _
    have h' := congrArg (fun g => (natCornerTermIso n).hom ≫ g) h
    simpa only [← Category.assoc,Iso.hom_inv_id,Category.id_comp,comp_zero] using h'
  | negSucc n => exact (inducedForward_below _ (by omega)).eq_of_src _ _

theorem inducedCeHom_zero (f : natForward.X 1 ⟶ Induced.X) : f=0 := by
  have h : (natCornerTermIso 1).inv ≫ f = 0 :=
    CornerTensorExt.jHom_zero 1 (by omega) _
  have h' := congrArg (fun g => (natCornerTermIso 1).hom ≫ g) h
  simpa only [← Category.assoc,Iso.hom_inv_id,Category.id_comp,comp_zero] using h'

theorem inducedReverseHom_zero (j : ℤ) (hj : j≠2)
    (f : inducedReverse.X j ⟶ Induced.X) : f=0 := by
  cases j with
  | ofNat n =>
    rcases n with _ | _ | _ | n
    · exact inducedCeHom_zero f
    · exact inducedCeHom_zero f
    · exact (hj rfl).elim
    · exact (inducedReverse_above _ (by norm_num; omega)).eq_of_src _ _
  | negSucc n => exact inducedCeHom_zero f

theorem forwardTensorSummandHom_subsingleton (i j : ℤ) (h : i≠0 ∨ j≠0) :
    Subsingleton ((((OuterTensor.bifunctor ℚ T T).obj
      (inducedForward.X i)).obj (inducedForward.X j)) ⟶ SocleBimodule.X) := by
  rcases h with hi | hj
  · let : Subsingleton (inducedForward.X i ⟶ Induced.X) :=
      ⟨fun f g => (inducedForwardHom_zero i hi f).trans (inducedForwardHom_zero i hi g).symm⟩
    exact (OuterTensor.homEquiv (k:=ℚ) (A:=T) (B:=T) (inducedForward.X i) Induced.X
      (inducedForward.X j) Induced.X).symm.injective.subsingleton
  · let : Subsingleton (inducedForward.X j ⟶ Induced.X) :=
      ⟨fun f g => (inducedForwardHom_zero j hj f).trans (inducedForwardHom_zero j hj g).symm⟩
    exact (OuterTensor.homEquiv (k:=ℚ) (A:=T) (B:=T) (inducedForward.X i) Induced.X
      (inducedForward.X j) Induced.X).symm.injective.subsingleton

theorem reverseTensorSummandHom_subsingleton (i j : ℤ) (h : i≠2 ∨ j≠2) :
    Subsingleton ((((OuterTensor.bifunctor ℚ T T).obj
      (inducedReverse.X i)).obj (inducedReverse.X j)) ⟶ SocleBimodule.X) := by
  rcases h with hi | hj
  · let : Subsingleton (inducedReverse.X i ⟶ Induced.X) :=
      ⟨fun f g => (inducedReverseHom_zero i hi f).trans (inducedReverseHom_zero i hi g).symm⟩
    exact (OuterTensor.homEquiv (k:=ℚ) (A:=T) (B:=T) (inducedReverse.X i) Induced.X
      (inducedReverse.X j) Induced.X).symm.injective.subsingleton
  · let : Subsingleton (inducedReverse.X j ⟶ Induced.X) :=
      ⟨fun f g => (inducedReverseHom_zero j hj f).trans (inducedReverseHom_zero j hj g).symm⟩
    exact (OuterTensor.homEquiv (k:=ℚ) (A:=T) (B:=T) (inducedReverse.X i) Induced.X
      (inducedReverse.X j) Induced.X).symm.injective.subsingleton

theorem forwardTensorHom_zero (j : ℤ) (hj : j≠0)
    (f : forwardTensor.X j ⟶ SocleBimodule.X) : f=0 := by
  apply mapBifunctor.hom_ext
  intro i k h
  rw [comp_zero]
  have hik : i+k=j := h
  exact (forwardTensorSummandHom_subsingleton i k (by omega)).elim _ _

theorem reverseTensorHom_zero (j : ℤ) (hj : j≠4)
    (f : reverseTensor.X j ⟶ SocleBimodule.X) : f=0 := by
  apply mapBifunctor.hom_ext
  intro i k h
  rw [comp_zero]
  have hik : i+k=j := h
  exact (reverseTensorSummandHom_subsingleton i k (by omega)).elim _ _

theorem tensorFiberHom_zero (j : ℤ) (h0 : j≠0) (h3 : j≠3)
    (f : tensorFiber.X j ⟶ SocleBimodule.X) : f=0 := by
  have h₁ : f.hom.comp (LinearMap.inl E (reverseTensor.X (j+1)) (forwardTensor.X j))=0 :=
    ModuleCat.hom_ext_iff.mp (reverseTensorHom_zero (j+1) (by omega) _)
  have h₂ : f.hom.comp (LinearMap.inr E (reverseTensor.X (j+1)) (forwardTensor.X j))=0 :=
    ModuleCat.hom_ext_iff.mp (forwardTensorHom_zero j h0 _)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have ha : f.hom (x.1,0)=0 := LinearMap.congr_fun h₁ x.1
  have hb : f.hom (0,x.2)=0 := LinearMap.congr_fun h₂ x.2
  change f.hom (x.1,x.2)=0
  calc
    f.hom (x.1,x.2) = f.hom ((x.1,0)+(0,x.2)) :=
      congrArg f.hom (Prod.ext (add_zero _).symm (zero_add _).symm)
    _ = 0 := by rw [map_add,ha,hb,add_zero]

theorem fiberCokerHom_zero (j : ℤ) (h0 : j≠0) (h3 : j≠3)
    (f : CokerAt tensorFiber j →ₗ[E] SocleBimodule.X) : f=0 := by
  have h := ModuleCat.hom_ext_iff.mp (tensorFiberHom_zero j h0 h3
    (ModuleCat.ofHom (X:=tensorFiber.X j) (Y:=SocleBimodule.X)
      (f.comp (CokerAt.π tensorFiber j))))
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := CokerAt.π_surjective tensorFiber j x
  exact LinearMap.congr_fun h y

theorem fiberCokerStableHom_subsingleton (j : ℤ) (h0 : j≠0) (h3 : j≠3) :
    Subsingleton (StableHom (k:=ℚ) (R:=E) (M:=CokerAt tensorFiber j)
      (N:=SocleBimodule.X)) := by
  let : Subsingleton (CokerAt tensorFiber j →ₗ[E] SocleBimodule.X) :=
    ⟨fun f g => (fiberCokerHom_zero j h0 h3 f).trans (fiberCokerHom_zero j h0 h3 g).symm⟩
  change Subsingleton ((CokerAt tensorFiber j →ₗ[E] SocleBimodule.X) ⧸
    projectiveFactors (k:=ℚ))
  infer_instance

theorem fiberCokerStableHom_from_X_subsingleton (j : ℤ) (h1 : j≠1) (h4 : j≠4) :
    Subsingleton (StableHom (k:=ℚ) (R:=E) (M:=SocleBimodule.X)
      (N:=CokerAt tensorFiber j)) := by
  let := fiberCokerStableHom_subsingleton (j-1) (by omega) (by omega)
  have e := completeCokerDuality E_form tensorFiber tensorFiber_exact
    tensorFiber_term_finite tensorFiber_term_projective (j-1) SocleBimodule.X
  rw [show j-1+1=j by omega] at e
  exact e.injective.subsingleton

def evaluatedFiberComparison : StableEquiv (k:=ℚ) EvaluatedWProfile.finiteYX.obj fiberY.obj :=
  CornerTensorModel.fixedYComparison.trans cornerYFiberComparison

def evaluatedShiftFiberComparison (a : ℤ) : StableEquiv (k:=ℚ)
    (EvaluatedWProfile.shift EvaluatedWProfile.finiteYX a).obj
    (ModuleCat.of E (CokerAt tensorFiber (1-a))) := by
  cases a with
  | ofNat n =>
    exact negativeCokerStableEquiv E_form tensorFiber tensorFiber_exact
      tensorFiber_term_finite tensorFiber_term_projective EvaluatedWProfile.finiteYX 1
      evaluatedFiberComparison n
  | negSucc n =>
    rw [show 1-Int.negSucc n = 1+((n+1:ℕ):ℤ) by omega]
    exact positiveCokerStableEquiv E_form tensorFiber tensorFiber_exact
      tensorFiber_term_finite tensorFiber_term_projective EvaluatedWProfile.finiteYX 1
      evaluatedFiberComparison (n+1)

theorem evaluatedW_subsingleton (a : ℤ) (h0 : a≠0) (hm3 : a≠-3) :
    Subsingleton (EvaluatedWProfile.W a) := by
  let := fiberCokerStableHom_from_X_subsingleton (1-a) (by omega) (by omega)
  exact ((evaluatedShiftFiberComparison a).post SocleBimodule.X).injective.subsingleton

end
end TachikawaCharZero.ReverseCorner
