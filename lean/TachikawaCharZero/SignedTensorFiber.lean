import TachikawaCharZero.SignedReverseInduction
import TachikawaCharZero.StartingSymmetric
import OAI.RingTheory.Tachikawa.IntegerTensorSupport
import OAI.RingTheory.Tachikawa.ModuleFiber
import OAI.RingTheory.Tachikawa.CokerComparison

/-! The actual rational signed tensor comparison and its complete fiber.
The construction is over the 400-dimensional symmetric algebra E. -/
namespace TachikawaCharZero.ReverseCorner
noncomputable section
open TachikawaCharZero.Resolution TachikawaCharZero.Starting
open OAI.Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra

theorem inducedForward_term_finiteT (j : ℤ) : Module.Finite T (inducedForward.X j) := by
  let := inducedForward_term_finite j
  exact Module.Finite.of_restrictScalars_finite ℚ T _

theorem inducedReverse_term_finiteT (j : ℤ) : Module.Finite T (inducedReverse.X j) := by
  let := inducedReverse_term_finite j
  exact Module.Finite.of_restrictScalars_finite ℚ T _

theorem inducedForward_term_moduleProjective (j : ℤ) :
    Module.Projective T (inducedForward.X j) := by
  let := inducedForward_term_projective j
  infer_instance

theorem inducedReverse_term_moduleProjective (j : ℤ) :
    Module.Projective T (inducedReverse.X j) := by
  let := inducedReverse_term_projective j
  infer_instance

theorem inducedForward_below (j : ℤ) (hj : j < 0) : IsZero (inducedForward.X j) := by
  cases j with
  | ofNat n =>
    change (n:ℤ) < 0 at hj
    omega
  | negSucc n =>
    exact (TrivialInduction.functor (k:=ℚ)).map_isZero
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of A PUnit))

theorem inducedReverse_above (j : ℤ) (hj : 2 < j) : IsZero (inducedReverse.X j) := by
  cases j with
  | ofNat n =>
    rcases n with _ | _ | _ | n
    · norm_num at hj
    · norm_num at hj
    · norm_num at hj
    · exact (TrivialInduction.functor (k:=ℚ)).map_isZero
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of A PUnit))
  | negSucc n => omega

def forwardTensor : ChainComplex (ModuleCat E) ℤ :=
  mapBifunctor inducedForward inducedForward (OuterTensor.bifunctor ℚ T T) (.down ℤ)

def reverseTensor : ChainComplex (ModuleCat E) ℤ :=
  mapBifunctor inducedReverse inducedReverse (OuterTensor.bifunctor ℚ T T) (.down ℤ)

def tensorComparison : forwardTensor ⟶ reverseTensor :=
  mapBifunctorMap inducedComparison inducedComparison (OuterTensor.bifunctor ℚ T T) (.down ℤ)

theorem tensorComparison_quasiIso : QuasiIso tensorComparison := by
  let := inducedComparison_quasiIso
  exact OuterTensor.quasiIso_int ℚ T T inducedComparison inducedComparison

theorem forwardTensor_term_finite (j : ℤ) : Module.Finite E (forwardTensor.X j) :=
  OuterTensor.total_finite_below_int inducedForward inducedForward 0 0
    inducedForward_term_finite inducedForward_term_finite
    inducedForward_below inducedForward_below j

theorem reverseTensor_term_finite (j : ℤ) : Module.Finite E (reverseTensor.X j) :=
  OuterTensor.total_finite_above_int inducedReverse inducedReverse 2 2
    inducedReverse_term_finite inducedReverse_term_finite
    inducedReverse_above inducedReverse_above j

theorem forwardTensor_term_projective (j : ℤ) : Projective (forwardTensor.X j) :=
  OuterTensor.total_projective_int inducedForward inducedForward
    inducedForward_term_finiteT inducedForward_term_finiteT
    inducedForward_term_moduleProjective inducedForward_term_moduleProjective j

theorem reverseTensor_term_projective (j : ℤ) : Projective (reverseTensor.X j) :=
  OuterTensor.total_projective_int inducedReverse inducedReverse
    inducedReverse_term_finiteT inducedReverse_term_finiteT
    inducedReverse_term_moduleProjective inducedReverse_term_moduleProjective j

theorem forwardTensor_below (j : ℤ) (hj : j < 0) : IsZero (forwardTensor.X j) :=
  OuterTensor.total_isZero_below_int inducedForward inducedForward 0 0
    inducedForward_below inducedForward_below j (by simpa using hj)

theorem reverseTensor_above (j : ℤ) (hj : 4 < j) : IsZero (reverseTensor.X j) :=
  OuterTensor.total_isZero_above_int inducedReverse inducedReverse 2 2
    inducedReverse_above inducedReverse_above j (by simpa using hj)

def tensorFiber : ChainComplex (ModuleCat E) ℤ := ModuleFiber.complex tensorComparison

theorem tensorFiber_exact : ComplexExact tensorFiber := by
  let := tensorComparison_quasiIso
  exact ModuleFiber.exact tensorComparison

theorem tensorFiber_totallyAcyclic : TotallyAcyclic tensorFiber := by
  let := tensorComparison_quasiIso
  let := E_injective
  exact ModuleFiber.totallyAcyclic tensorComparison

theorem tensorFiber_term_finite (j : ℤ) : Module.Finite E (tensorFiber.X j) := by
  let := reverseTensor_term_finite (j+1)
  let := forwardTensor_term_finite j
  change Module.Finite E (reverseTensor.X (j+1) × forwardTensor.X j)
  infer_instance

theorem tensorFiber_term_projective (j : ℤ) : Module.Projective E (tensorFiber.X j) := by
  let : Module.Projective E (reverseTensor.X (j+1)) := by
    let := reverseTensor_term_projective (j+1)
    infer_instance
  let : Module.Projective E (forwardTensor.X j) := by
    let := forwardTensor_term_projective j
    infer_instance
  change Module.Projective E (reverseTensor.X (j+1) × forwardTensor.X j)
  infer_instance

def fiberHighEquiv (j : ℤ) (hj : 4 ≤ j) : tensorFiber.X j ≃ₗ[E] forwardTensor.X j := by
  let : Subsingleton (reverseTensor.X (j+1)) :=
    ModuleCat.subsingleton_of_isZero (reverseTensor_above (j+1) (by omega))
  exact LinearEquiv.ofBijective (LinearMap.snd E (reverseTensor.X (j+1)) _) ⟨
    fun x y h => Prod.ext (Subsingleton.elim _ _) h, fun y => ⟨(0,y),rfl⟩⟩

theorem fiberHighEquiv_apply (j : ℤ) (hj : 4 ≤ j) (x : tensorFiber.X j) :
    fiberHighEquiv j hj x = x.2 := rfl

def fiberHighCokerEquiv (j : ℤ) (hj : 4 ≤ j) :
    CokerAt tensorFiber j ≃ₗ[E] CokerAt forwardTensor j := by
  apply cokerLinearEquiv _ _
    ((fiberHighEquiv (j+1) (by omega)).trans (LinearEquiv.neg E)) (fiberHighEquiv j hj)
  apply LinearMap.ext
  intro x
  change (tensorFiber.d (j+1) j x).2 = forwardTensor.d (j+1) j (-x.2)
  rw [show tensorFiber.d (j+1) j = ModuleFiber.differential tensorComparison j from
    ModuleFiber.complex_d _ j]
  change -forwardTensor.d (j+1) j x.2 = forwardTensor.d (j+1) j (-x.2)
  rw [map_neg]

end
end TachikawaCharZero.ReverseCorner
