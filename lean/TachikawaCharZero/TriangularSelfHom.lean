import TachikawaCharZero.SignedTriangularComparison
import TachikawaCharZero.TriangularCochains
import TachikawaCharZero.TriangularNonprojective

/-! Discharge the signed boundary criterion for the actual rational cone.
All maps use the fixed F, complete lift and rational Delta. The generic
evaluation theorem is instantiated at the actual complete augmentations,
rather than replacing their Hom spaces by dimensional surrogates. -/
namespace TachikawaCharZero.TriangularSelfHom
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open OAI.Tachikawa ScalingSocle SocleBimodule
open SignedDownHom SignedCompleteHomComparison SignedCochainTransport SignedTriangularComparison
open TriangularWitness
open scoped ModuleCat.Algebra
local instance eeRing : Ring EE := InducedTwistedSocle.eeRing
local instance finiteF : Module.Finite ℚ F := F_finite
local instance finiteObjF : FiniteDimensional ℚ (Enveloping.Obj F) :=
  inferInstanceAs (FiniteDimensional ℚ F)
local instance leftProjective : Module.Projective E (Enveloping.Obj F) :=
  (TwoBranchFiber.side_projective H₁ H₂ (by norm_num) (by norm_num)).1
local instance rightProjective : Module.Projective Eᵐᵒᵖ (Enveloping.Obj F) :=
  (TwoBranchFiber.side_projective H₁ H₂ (by norm_num) (by norm_num)).2

abbrev P := TateProfile.P
abbrev FP := Enveloping.tensorComplex F P
local instance crossAdd (a : ℤ) : AddCommGroup (Cochain P FP a) :=
  SignedDownHom.instAddCommGroupCochain (R:=E) (P:=P) (Q:=FP) a
local instance crossModule (a : ℤ) : Module ℚ (Cochain P FP a) :=
  SignedDownHom.instModuleCochain (k:=ℚ) (R:=E) (P:=P) (Q:=FP) a
abbrev augmentation : P.X 0 ⟶ X := ModuleCat.ofHom StableSeam.finiteX.cover.map

theorem augmentation_exact : Function.Exact (P.d 1 0) augmentation := by
  change Function.Exact ((StableSeam.finiteX.complete TateProfile.form).d (0+1) 0)
    StableSeam.finiteX.cover.map
  rw [FiniteModule.complete_d]
  exact StableSeam.finiteX.pos_augmentation_exact

theorem augmentation_zero : P.d 1 0 ≫ augmentation=0 :=
  ModuleCat.hom_ext (LinearMap.ext augmentation_exact.apply_apply_eq_zero)

abbrev fiberAugmentation := (Enveloping.tensorFunctor F).map augmentation
theorem fiberAugmentation_zero : FP.d 1 0 ≫ fiberAugmentation=0 :=
  map_augmentation_zero (Enveloping.tensorFunctor F) augmentation augmentation_zero

abbrev selfEval {a : ℤ} (f : Cochain P P a) (hf : Closed (k:=ℚ) f) : TateProfile.Tate a :=
  evalClass augmentation augmentation_zero f hf
abbrev crossEval {a : ℤ} (f : Cochain P FP a) (hf : Closed (k:=ℚ) f) :
    VectorSplit.H (TwoBranchDelta.fiberComplex H₁ H₂ (by norm_num) (by norm_num)) a :=
  evalClass fiberAugmentation fiberAugmentation_zero f hf

theorem selfEval_zero_iff {a : ℤ} (f : Cochain P P a) (hf : Closed (k:=ℚ) f) :
    selfEval f hf=0 ↔ Boundary (k:=ℚ) f :=
  eval_zero_iff_boundary augmentation augmentation_zero
    (StableSeam.finiteX.complete_totallyAcyclic TateProfile.form)
    (StableSeam.finiteX.complete_exact TateProfile.form)
    (StableSeam.finiteX.complete_projective TateProfile.form)
    (StableSeam.finiteX.complete_finite TateProfile.form)
    (StableSeam.finiteX.complete_finite TateProfile.form)
    (StableSeam.finiteX.complete_projective TateProfile.form)
    augmentation_exact StableSeam.finiteX.cover.surjective f hf

theorem selfEval_surjective (a : ℤ) (x : TateProfile.Tate a) :
    ∃ (f : Cochain P P a) (hf : Closed (k:=ℚ) f), selfEval f hf=x :=
  eval_surjective augmentation augmentation_zero
    (StableSeam.finiteX.complete_totallyAcyclic TateProfile.form)
    (StableSeam.finiteX.complete_exact TateProfile.form)
    (StableSeam.finiteX.complete_projective TateProfile.form)
    (StableSeam.finiteX.complete_finite TateProfile.form)
    (StableSeam.finiteX.complete_projective TateProfile.form)
    augmentation_exact StableSeam.finiteX.cover.surjective a x

theorem crossEval_zero_iff {a : ℤ} (f : Cochain P FP a) (hf : Closed (k:=ℚ) f) :
    crossEval f hf=0 ↔ Boundary (k:=ℚ) f :=
  eval_zero_iff_boundary fiberAugmentation fiberAugmentation_zero
    (StableSeam.finiteX.complete_totallyAcyclic TateProfile.form)
    (Enveloping.tensorComplex_exact F P (StableSeam.finiteX.complete_exact TateProfile.form))
    (StableSeam.finiteX.complete_projective TateProfile.form)
    (StableSeam.finiteX.complete_finite TateProfile.form)
    (Enveloping.tensorComplex_finite F P (StableSeam.finiteX.complete_finite TateProfile.form))
    (Enveloping.tensorComplex_projective F P
      (StableSeam.finiteX.complete_finite TateProfile.form)
      (StableSeam.finiteX.complete_projective TateProfile.form))
    (Enveloping.tensor_augmentation_exact F StableSeam.finiteX TateProfile.form)
    (Enveloping.tensor_map_surjective F augmentation StableSeam.finiteX.cover.surjective) f hf

def baseConnecting {a : ℤ} (f g : Cochain P P a) : Cochain P FP a :=
  let first : Cochain P FP a := post g lift
  let second : Cochain P FP a := pre lift (mapCochain (Enveloping.tensorFunctor F) f)
  first-sign (k:=ℚ) a • second

theorem baseConnecting_closed {a : ℤ} (f g : Cochain P P a)
    (hf : Closed (k:=ℚ) f) (hg : Closed (k:=ℚ) g) : Closed (k:=ℚ) (baseConnecting f g) :=
  closed_sub (post_closed hg lift)
    (closed_smul _ (pre_closed lift (map_closed (Enveloping.tensorFunctor F) hf)))

theorem baseConnecting_eval {a : ℤ} (f g : Cochain P P a)
    (hf : Closed (k:=ℚ) f) (hg : Closed (k:=ℚ) g) :
    crossEval (baseConnecting f g) (baseConnecting_closed f g hf hg)=
      -sign (k:=ℚ) a • TwoBranchBijectivity.delta (sign (k:=ℚ) a) a (selfEval f hf,selfEval g hg) := by
  unfold crossEval selfEval baseConnecting
  rw [eval_sub fiberAugmentation fiberAugmentation_zero
      (post g lift) (sign (k:=ℚ) a • (pre lift (mapCochain (Enveloping.tensorFunctor F) f) : Cochain P FP a))
      (post_closed hg lift)
      (closed_smul _ (pre_closed lift (map_closed (Enveloping.tensorFunctor F) hf))),
    eval_smul fiberAugmentation fiberAugmentation_zero _
      (pre lift (mapCochain (Enveloping.tensorFunctor F) f))
      (pre_closed lift (map_closed (Enveloping.tensorFunctor F) hf)),
    eval_post_lift (Enveloping.tensorFunctor F) augmentation augmentation_zero lift
      (TwoBranchFiber.vZero H₁ H₂ (by norm_num) (by norm_num))
      (TwoBranchAction.completeLift_aug H₁ H₂ (by norm_num) (by norm_num)) g hg,
    eval_pre_functor (Enveloping.tensorFunctor F) augmentation augmentation_zero lift f hf]
  rw [TwoBranchDelta.delta_apply]
  let x : VectorSplit.H (TwoBranchDelta.fiberComplex H₁ H₂ (by norm_num) (by norm_num)) a :=
    VectorSplit.Hmap (completeFunctorHom (k:=ℚ) (Enveloping.tensorFunctor F) P P X lift) a
      (evalClass augmentation augmentation_zero f hf)
  let y : VectorSplit.H (TwoBranchDelta.fiberComplex H₁ H₂ (by norm_num) (by norm_num)) a :=
    VectorSplit.Hmap (completeHomMap (k:=ℚ) P
      (TwoBranchFiber.vZero H₁ H₂ (by norm_num) (by norm_num))) a
      (evalClass augmentation augmentation_zero g hg)
  change y-sign (k:=ℚ) a • x= -sign (k:=ℚ) a • (x-sign (k:=ℚ) a • y)
  rw [neg_smul,smul_sub,smul_smul,
    SignedDownHom.sign_mul_self,one_smul]
  abel

theorem connecting_closed {a : ℤ}
    (f : Cochain TriangularCochains.lowComplex TriangularCochains.lowComplex a)
    (g : Cochain TriangularCochains.highComplex TriangularCochains.highComplex a)
    (hf : Closed (k:=ℚ) f) (hg : Closed (k:=ℚ) g) :
    Closed (k:=ℚ) (SignedConeDifferential.connecting (k:=ℚ) TriangularCochains.v f g) :=
  closed_sub (post_closed hg TriangularCochains.v)
    (closed_smul _ (pre_closed TriangularCochains.v hf))

theorem connecting_injective (a : ℤ) (ha : 0<a ∨ a≤ -2)
    (f : Cochain TriangularCochains.lowComplex TriangularCochains.lowComplex a)
    (g : Cochain TriangularCochains.highComplex TriangularCochains.highComplex a)
    (hf : Closed (k:=ℚ) f) (hg : Closed (k:=ℚ) g)
    (hb : Boundary (k:=ℚ) (SignedConeDifferential.connecting (k:=ℚ) TriangularCochains.v f g)) :
    Boundary (k:=ℚ) f ∧ Boundary (k:=ℚ) g := by
  have hf' := (down₀_closed F f).mpr hf
  have hg' := (down₁_closed F g).mpr hg
  have hc := connecting_closed f g hf hg
  have hc' := (downCross_closed F _).mpr hc
  have hb' := (downCross_boundary F _).mpr hb
  have hz := (crossEval_zero_iff _ hc').mpr hb'
  have he := down_connecting F lift f g
  have hz' : crossEval (baseConnecting (down₀ F a f) (down₁ F a g))
      (baseConnecting_closed _ _ hf' hg')=0 := by
    simpa only [baseConnecting,he] using hz
  rw [baseConnecting_eval _ _ hf' hg'] at hz'
  have hd := congrArg (fun z => -sign (k:=ℚ) a • z) hz'
  rw [smul_smul,neg_mul_neg,SignedDownHom.sign_mul_self,one_smul,smul_zero] at hd
  have hinj := (TwoBranchBijectivity.signed_vanishing_ranges a ha).1
  have hp := hinj (hd.trans (map_zero _).symm)
  refine ⟨(down₀_boundary F f).mp ((selfEval_zero_iff _ hf').mp ?_),
    (down₁_boundary F g).mp ((selfEval_zero_iff _ hg').mp ?_)⟩
  · exact congrArg Prod.fst hp
  · exact congrArg Prod.snd hp

theorem connecting_surjective (a : ℤ) (ha : 0<a ∨ a≤ -2)
    (c : Cochain TriangularCochains.highComplex TriangularCochains.lowComplex (a-1))
    (hc : Closed (k:=ℚ) c) :
    ∃ (f : Cochain TriangularCochains.lowComplex TriangularCochains.lowComplex (a-1))
      (g : Cochain TriangularCochains.highComplex TriangularCochains.highComplex (a-1)),
      Closed (k:=ℚ) f ∧ Closed (k:=ℚ) g ∧
      Boundary (k:=ℚ) (c-SignedConeDifferential.connecting (k:=ℚ) TriangularCochains.v f g) := by
  have hc' := (downCross_closed F c).mpr hc
  let x := crossEval (downCross F (a-1) c) hc'
  have hsurj := (TwoBranchBijectivity.signed_vanishing_ranges a ha).2
  obtain ⟨p,hp⟩ := hsurj (-sign (k:=ℚ) (a-1) • x)
  obtain ⟨f₀,hf₀,ef⟩ := selfEval_surjective (a-1) p.1
  obtain ⟨g₀,hg₀,eg⟩ := selfEval_surjective (a-1) p.2
  let f := (down₀ F (a-1)).symm f₀
  let g := (down₁ F (a-1)).symm g₀
  have hf : Closed (k:=ℚ) f := (down₀_closed F f).mp (by
    simpa only [f,LinearEquiv.apply_symm_apply] using hf₀)
  have hg : Closed (k:=ℚ) g := (down₁_closed F g).mp (by
    simpa only [g,LinearEquiv.apply_symm_apply] using hg₀)
  refine ⟨f,g,hf,hg,?_⟩
  have hconn := connecting_closed f g hf hg
  have hd := (downCross_closed F _).mpr (closed_sub hc hconn)
  apply (downCross_boundary F _).mp
  apply (crossEval_zero_iff _ hd).mp
  have he := down_connecting F lift f g
  have hex : crossEval (baseConnecting f₀ g₀) (baseConnecting_closed _ _ hf₀ hg₀)=x := by
    rw [baseConnecting_eval f₀ g₀ hf₀ hg₀,ef,eg,hp,smul_smul,neg_mul_neg,
      SignedDownHom.sign_mul_self,one_smul]
  have hzero : crossEval (downCross F (a-1) c-baseConnecting f₀ g₀)
      (closed_sub hc' (baseConnecting_closed _ _ hf₀ hg₀))=0 := by
    unfold crossEval
    rw [eval_sub fiberAugmentation fiberAugmentation_zero
      (downCross F (a-1) c) (baseConnecting f₀ g₀) hc'
      (baseConnecting_closed _ _ hf₀ hg₀)]
    change x-crossEval (baseConnecting f₀ g₀) (baseConnecting_closed _ _ hf₀ hg₀)=0
    rw [hex,sub_self]
  simpa only [map_sub,he,baseConnecting,f,g,LinearEquiv.apply_symm_apply] using hzero

theorem closed_boundary (a : ℤ) (ha : 0<a ∨ a≤ -2)
    (z : Cochain cone cone a) (hz : Closed (k:=ℚ) z) : Boundary (k:=ℚ) z :=
  TriangularCochains.boundary_of_connecting a (connecting_injective a ha)
    (connecting_surjective a ha) z hz

abbrev coneAugmentation : cone.X 0 ⟶ ModuleCat.of Lambda Z := ModuleCat.ofHom (CokerAt.π cone 0)
theorem coneAugmentation_zero : cone.d 1 0 ≫ coneAugmentation=0 :=
  ModuleCat.hom_ext (CokerAt.π_d cone 0)
theorem coneAugmentation_exact : Function.Exact (cone.d 1 0) coneAugmentation := by
  intro x
  change (LinearMap.range (cone.d 1 0).hom).mkQ x=0 ↔ x ∈ Set.range (cone.d 1 0)
  rw [← LinearMap.mem_ker,Submodule.ker_mkQ]
  rfl

theorem selfHom_vanishing (a : ℤ) (ha : 0<a ∨ a≤ -2) :
    Subsingleton (VectorSplit.H (completeHom (k:=ℚ) cone (ModuleCat.of Lambda Z)) a) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨z,hz,he⟩ := eval_surjective coneAugmentation coneAugmentation_zero
    cone_totallyAcyclic cone_totallyAcyclic.1 cone_projective cone_finite cone_projective
    coneAugmentation_exact (CokerAt.π_surjective cone 0) a x
  rw [← he]
  exact eval_boundary _ _ z hz (closed_boundary a ha z hz)

theorem target : Target := TriangularNonprojective.target_of_selfHom_vanishing selfHom_vanishing

end
end TachikawaCharZero.TriangularSelfHom
