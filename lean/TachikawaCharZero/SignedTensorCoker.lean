import TachikawaCharZero.SignedTensorFiber
import TachikawaCharZero.CornerTensorModel
import OAI.RingTheory.Tachikawa.InductionTensorComparison

/-! Compare the natural and integer signed totals of the actual rational
induced resolution. All Koszul signs are retained. Adapted from the generic
comparison in pinned OpenAI Math Perfect.lean (Apache-2.0). -/
namespace TachikawaCharZero.ReverseCorner
noncomputable section
set_option backward.isDefEq.respectTransparency false
open TachikawaCharZero.Resolution TachikawaCharZero.Starting OAI.Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped TensorProduct ModuleCat.Algebra

abbrev natForward := ((TrivialInduction.functor (k:=ℚ)).mapHomologicalComplex
  (.down ℕ)).obj Resolution.projectiveResolution.complex

theorem natForward_d (n : ℕ) : natForward.d (n+1) n =
    (TrivialInduction.functor (k:=ℚ)).map (resD n) := by
  rw [Functor.mapHomologicalComplex_obj_d,Resolution.projectiveResolution_d]

abbrev natTensor := mapBifunctor natForward natForward (OuterTensor.bifunctor ℚ T T) (.down ℕ)
abbrev natTensorDouble := ((OuterTensor.bifunctor ℚ T T).mapBifunctorHomologicalComplex
  (.down ℕ) (.down ℕ)).obj natForward |>.obj natForward
abbrev intTensorDouble := ((OuterTensor.bifunctor ℚ T T).mapBifunctorHomologicalComplex
  (.down ℤ) (.down ℤ)).obj inducedForward |>.obj inducedForward

def natIntX (n : ℕ) : natTensor.X n ⟶ forwardTensor.X (n:ℤ) :=
  (natTensorDouble).totalDesc (c₁₂ := .down ℕ) (fun i j h =>
    (intTensorDouble).ιTotal (.down ℤ) (i:ℤ) (j:ℤ) (n:ℤ) (by
      change (i:ℤ)+(j:ℤ)=(n:ℤ); change i+j=n at h; omega))

@[reassoc (attr := simp)] theorem ι_natIntX (i j n : ℕ) (h : i+j=n) :
    (natTensorDouble).ιTotal (.down ℕ) i j n h ≫ natIntX n =
      (intTensorDouble).ιTotal (.down ℤ) (i:ℤ) (j:ℤ) (n:ℤ) (by
        change (i:ℤ)+(j:ℤ)=(n:ℤ); omega) := by
  apply ι_totalDesc

def intNatComponent (n : ℕ) (i j : ℤ) (h : i+j=(n:ℤ)) :
    ((intTensorDouble).X i).X j ⟶ natTensor.X n := by
  cases i with
  | ofNat i =>
    cases j with
    | ofNat j => exact (natTensorDouble).ιTotal (.down ℕ) i j n (by change i+j=n; dsimp at h; omega)
    | negSucc j => exact 0
  | negSucc i => exact 0

def intNatX (n : ℕ) : forwardTensor.X (n:ℤ) ⟶ natTensor.X n :=
  (intTensorDouble).totalDesc (c₁₂ := .down ℤ) (intNatComponent n)

@[reassoc (attr := simp)] theorem ι_intNatX (i j : ℤ) (n : ℕ) (h : i+j=(n:ℤ)) :
    (intTensorDouble).ιTotal (.down ℤ) i j (n:ℤ) h ≫ intNatX n =
      intNatComponent n i j h := by
  apply ι_totalDesc

def natIntIso (n : ℕ) : natTensor.X n ≅ forwardTensor.X (n:ℤ) where
  hom := natIntX n
  inv := intNatX n
  hom_inv_id := by
    apply total.hom_ext
    intro i j h
    simp only [ι_natIntX_assoc, Category.comp_id]
    erw [ι_intNatX (i:ℤ) (j:ℤ) n]
    rfl
  inv_hom_id := by
    apply total.hom_ext
    intro i j h
    erw [ι_intNatX_assoc, Category.comp_id]
    cases i with
    | ofNat i =>
      cases j with
      | ofNat j => exact ι_natIntX i j n (by dsimp at h; omega)
      | negSucc j =>
        apply (OuterTensor.isZero_obj_right _ _ (inducedForward_below _ (by omega))).eq_of_src
    | negSucc i =>
      apply (OuterTensor.isZero_obj_left _ _ (inducedForward_below _ (by omega))).eq_of_src




theorem inducedForward_d_nat (n : ℕ) : inducedForward.d ((n:ℤ)+1) (n:ℤ) = (TrivialInduction.functor (k:=ℚ)).map (resD n) := by
  change (TrivialInduction.functor (k := ℚ)).map ((forwardComplex).d ((n:ℤ)+1) n) = _
  rw [show (forwardComplex).d ((n:ℤ)+1) n = forwardD n from ChainComplex.of_d _ _ _]
  rfl

theorem inducedForward_d_bottom : inducedForward.d 0 (-1) = 0 := by
  change (TrivialInduction.functor (k := ℚ)).map ((forwardComplex).d 0 (-1)) = _
  have h : (forwardComplex).d 0 (-1) = 0 := by
    change ChainComplex.of.d forwardObj forwardD 0 (-1) = 0
    simp only [ChainComplex.of.d, dite_eq_left (show (0:ℤ) = -1 + 1 from rfl)]
    rfl
  rw [h, Functor.map_zero]

theorem natInt_d₁ (i j n : ℕ) (h : i+j=n+1) :
    (natTensorDouble).d₁ (.down ℕ) i j n ≫ natIntX n =
      (intTensorDouble).d₁ (.down ℤ) (i:ℤ) (j:ℤ) (n:ℤ) := by
  cases i with
  | zero =>
    erw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by change ¬ _+1=0; omega), zero_comp,
      HomologicalComplex₂.d₁_eq' _ _ (show (ComplexShape.down ℤ).Rel 0 (-1) from rfl)]
    change 0 = (1:ℤˣ) • (((OuterTensor.bifunctor ℚ T T).map
      (inducedForward.d 0 (-1) )).app (inducedForward.X (j:ℤ))) ≫ _
    erw [inducedForward_d_bottom, Functor.map_zero, NatTrans.app_zero, zero_comp, smul_zero]
  | succ i =>
    rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.down ℕ).Rel (i+1) i from rfl)
        j n (by change i+j=n; omega),
      HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.down ℤ).Rel ((i+1:ℕ):ℤ) (i:ℤ) from rfl)
        (j:ℤ) (n:ℤ) (by change (i:ℤ)+(j:ℤ)=(n:ℤ); omega)]
    change ((1:ℤˣ) • (((OuterTensor.bifunctor ℚ T T).map
      (natForward.d (i+1) i)).app (natForward.X j)) ≫ _) ≫ _ =
      (1:ℤˣ) • (((OuterTensor.bifunctor ℚ T T).map
      (inducedForward.d ((i:ℤ)+1) (i:ℤ) )).app (inducedForward.X (j:ℤ))) ≫ _
    erw [one_smul, one_smul, Category.assoc, ι_natIntX,
      natForward_d, inducedForward_d_nat]
    rfl

theorem natIntSign (i : ℕ) : (i:ℤ).negOnePow = (-1:ℤˣ)^i := by
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using Int.coe_negOnePow_natCast i

theorem natInt_d₂ (i j n : ℕ) (h : i+j=n+1) :
    (natTensorDouble).d₂ (.down ℕ) i j n ≫ natIntX n =
      (intTensorDouble).d₂ (.down ℤ) (i:ℤ) (j:ℤ) (n:ℤ) := by
  cases j with
  | zero =>
    erw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by change ¬ _+1=0; omega), zero_comp,
      HomologicalComplex₂.d₂_eq' _ _ (i:ℤ) (show (ComplexShape.down ℤ).Rel 0 (-1) from rfl)]
    change 0 = (i:ℤ).negOnePow • (((OuterTensor.bifunctor ℚ T T).obj
      (inducedForward.X (i:ℤ) )).map (inducedForward.d 0 (-1))) ≫ _
    erw [inducedForward_d_bottom, Functor.map_zero, zero_comp, smul_zero]
  | succ j =>
    rw [HomologicalComplex₂.d₂_eq _ _ i (show (ComplexShape.down ℕ).Rel (j+1) j from rfl)
        n (by change i+j=n; omega),
      HomologicalComplex₂.d₂_eq _ _ (i:ℤ) (show (ComplexShape.down ℤ).Rel ((j+1:ℕ):ℤ) (j:ℤ) from rfl)
        (n:ℤ) (by change (i:ℤ)+(j:ℤ)=(n:ℤ); omega)]
    change (((-1:ℤˣ)^i) • (((OuterTensor.bifunctor ℚ T T).obj
      (natForward.X i)).map (natForward.d (j+1) j)) ≫ _) ≫ _ =
      (i:ℤ).negOnePow • (((OuterTensor.bifunctor ℚ T T).obj
      (inducedForward.X (i:ℤ) )).map (inducedForward.d ((j:ℤ)+1) (j:ℤ))) ≫ _
    erw [Linear.units_smul_comp, Category.assoc, ι_natIntX,
      natForward_d, inducedForward_d_nat, natIntSign]
    rfl

theorem natInt_d (n : ℕ) :
    natIntX (n+1) ≫ forwardTensor.d ((n+1:ℕ):ℤ) (n:ℤ) =
      natTensor.d (n+1) n ≫ natIntX n := by
  apply total.hom_ext
  intro i j h
  rw [ι_natIntX_assoc]
  simp only [total_d, Preadditive.comp_add, Preadditive.add_comp,
    ι_D₁_assoc, ι_D₂_assoc]
  rw [natInt_d₁ i j n h, natInt_d₂ i j n h]
  erw [Preadditive.comp_add, ι_D₁, ι_D₂]

def natIntCokerEquiv (n : ℕ) :
    (natTensor.X (n+1) ⧸ LinearMap.range (natTensor.d (n+2) (n+1)).hom) ≃ₗ[E]
      CokerAt forwardTensor ((n+1:ℕ):ℤ) :=
  cokerLinearEquiv _ _ (natIntIso (n+2)).toLinearEquiv
    (natIntIso (n+1)).toLinearEquiv
    (ModuleCat.hom_ext_iff.mp (natInt_d (n+1)).symm)


def balancedNatForwardIso : InducedTensorComparison.balancedInducedChain ≅ natForward := by
  let (i : ℕ) : FiniteDimensional ℚ (Resolution.projectiveResolution.complex.X i) :=
    forward_term_finite (i:ℤ)
  exact TrivialInduction.tensorComplexIso Resolution.projectiveResolution.complex

def natCornerIso : natForward ≅ Induced.complex :=
  balancedNatForwardIso.symm ≪≫ InducedTensorComparison.cornerChainIso

def natCornerTensorIso : natTensor ≅ InducedTensorComparison.cornerTensorChain := by
  let F := (OuterTensor.bifunctor ℚ T T).map₂HomologicalComplex
    (.down ℕ) (.down ℕ) (.down ℕ)
  exact ((F.mapIso natCornerIso).app natForward) ≪≫
    ((F.obj Induced.complex).mapIso natCornerIso)

def natCornerCokerEquiv (n : ℕ) : NatCoker.C natTensor n ≃ₗ[E]
    NatCoker.C InducedTensorComparison.cornerTensorChain n :=
  cokerLinearEquiv _ _
    ((HomologicalComplex.eval (ModuleCat E) (.down ℕ) (n+2)).mapIso
      natCornerTensorIso).toLinearEquiv
    ((HomologicalComplex.eval (ModuleCat E) (.down ℕ) (n+1)).mapIso
      natCornerTensorIso).toLinearEquiv
    (ModuleCat.hom_ext_iff.mp (natCornerTensorIso.hom.comm (n+2) (n+1)).symm)

def cornerFiveFiberEquiv : CornerTensorModel.cokerFive.obj ≃ₗ[E] CokerAt tensorFiber 5 :=
  (natCornerCokerEquiv 4).symm.trans
    ((natIntCokerEquiv 4).trans (fiberHighCokerEquiv 5 (by omega)).symm)

def cornerYFiberComparison : StableEquiv (k:=ℚ) CornerTensorModel.Y.obj
    (ModuleCat.of E (CokerAt tensorFiber 1)) :=
  negativeCokerStableEquiv E_form tensorFiber tensorFiber_exact
    tensorFiber_term_finite tensorFiber_term_projective CornerTensorModel.cokerFive 5
    (StableEquiv.ofLinearEquiv cornerFiveFiberEquiv) 4

def fiberY : FiniteModule ℚ E where
  obj := ModuleCat.of E (CokerAt tensorFiber 1)
  finite := by
    let := tensorFiber_term_finite 1
    exact Module.Finite.quotient E (LinearMap.range (tensorFiber.d 2 1).hom)

def fiberLift : SocleBimodule.X ⟶ fiberY.obj :=
  ModuleCat.ofHom (cornerYFiberComparison.hom.comp
    (CornerTensorModel.lift 2 (by norm_num)).hom)

theorem fiberLift_stable_ne_zero : stableClass (k:=ℚ) fiberLift.hom ≠ 0 := by
  intro hz
  apply CornerTensorModel.lift_stable_ne_zero 2 (by norm_num)
  apply (cornerYFiberComparison.post SocleBimodule.X).injective
  change stableClass (k:=ℚ) fiberLift.hom = _
  simpa only [map_zero] using hz

theorem fiberY_nonprojective : ¬ Module.Projective E fiberY.obj := by
  intro hp
  apply fiberLift_stable_ne_zero
  apply (stableClass_eq_zero_iff _).mpr
  exact ⟨fiberY.obj,fiberY.finite,hp,fiberLift.hom,LinearMap.id,rfl⟩

end
end TachikawaCharZero.ReverseCorner
