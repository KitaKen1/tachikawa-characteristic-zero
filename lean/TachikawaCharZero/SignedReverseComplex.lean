import TachikawaCharZero.ReverseCorner

/-! Actual integer-indexed signed comparison over the rational starting
algebra C. This is the C-level comparison; induction to the symmetric
algebra and the complete tensor fiber are subsequent obligations. -/
namespace TachikawaCharZero.ReverseCorner
noncomputable section
open TachikawaCharZero.Resolution
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

def forwardObj : ℤ → ModuleCat A
  | .ofNat n => resObj n
  | .negSucc _ => ModuleCat.of A PUnit

def forwardD : ∀ j : ℤ, forwardObj (j+1) ⟶ forwardObj j
  | .ofNat n => resD n
  | .negSucc 0 => 0
  | .negSucc (_+1) => 0

theorem forwardD_comp (j : ℤ) : forwardD (j+1) ≫ forwardD j = 0 := by
  cases j with
  | ofNat n => exact ModuleCat.hom_ext <| LinearMap.ext <|
      (resD_exact n).apply_apply_eq_zero
  | negSucc n =>
    cases n with
    | zero => exact comp_zero
    | succ n => exact comp_zero

def forwardComplex : ChainComplex (ModuleCat A) ℤ :=
  ChainComplex.of forwardObj forwardD forwardD_comp

def reverseObj : ℤ → ModuleCat A
  | .ofNat 0 => ModuleCat.of A Ce
  | .ofNat 1 => ModuleCat.of A Ce
  | .ofNat 2 => ModuleCat.of A Cf
  | .ofNat (_+3) => ModuleCat.of A PUnit
  | .negSucc _ => ModuleCat.of A Ce

def reverseD : ∀ j : ℤ, reverseObj (j+1) ⟶ reverseObj j
  | .ofNat 0 => ModuleCat.ofHom (ceDiff (reverseCoeff 0))
  | .ofNat 1 => ModuleCat.ofHom rhoT
  | .ofNat (_+2) => 0
  | .negSucc 0 => ModuleCat.ofHom (ceDiff (reverseCoeff 1))
  | .negSucc (n+1) => ModuleCat.ofHom (ceDiff (reverseCoeff (n+2)))

theorem reverseD_comp_zero (j : ℤ) : reverseD (j+1) ≫ reverseD j = 0 := by
  cases j with
  | ofNat n =>
    rcases n with _ | _ | n
    · change ModuleCat.ofHom rhoT ≫ ModuleCat.ofHom (ceDiff (reverseCoeff 0)) = 0
      rw [reverseCoeff_zero]
      exact ModuleCat.hom_ext <| LinearMap.ext <| rhoT_exact.apply_apply_eq_zero
    · exact zero_comp
    · exact zero_comp
  | negSucc n =>
    rcases n with _ | _ | n
    · exact ModuleCat.hom_ext <| LinearMap.ext <| reverseD_comp 0
    · exact ModuleCat.hom_ext <| LinearMap.ext <| reverseD_comp 1
    · exact ModuleCat.hom_ext <| LinearMap.ext <| reverseD_comp (n+2)

def reverseComplex : ChainComplex (ModuleCat A) ℤ :=
  ChainComplex.of reverseObj reverseD reverseD_comp_zero

def comparisonComponent : ∀ j, forwardObj j ⟶ reverseObj j
  | .ofNat 0 => ModuleCat.ofHom rhoJ
  | .ofNat 1 => ModuleCat.ofHom ((-2:ℚ) • rhoX)
  | .ofNat 2 => ModuleCat.ofHom rhoV
  | .ofNat (_+3) => 0
  | .negSucc _ => 0

theorem comparison_comm (j : ℤ) : comparisonComponent (j+1) ≫ reverseD j =
    forwardD j ≫ comparisonComponent j := by
  cases j with
  | ofNat n =>
    rcases n with _ | _ | _ | n
    · exact ModuleCat.hom_ext comparison_one
    · change ModuleCat.ofHom rhoV ≫ ModuleCat.ofHom rhoT =
        ModuleCat.ofHom (ceDiff ((-2:ℚ)^0)) ≫ ModuleCat.ofHom ((-2:ℚ) • rhoX)
      simp only [pow_zero]
      exact ModuleCat.hom_ext comparison_two
    · change (0 : ModuleCat.of A Ce ⟶ ModuleCat.of A PUnit) ≫ 0 =
        ModuleCat.ofHom (ceDiff ((-2:ℚ)^1)) ≫ ModuleCat.ofHom rhoV
      rw [zero_comp]
      exact (ModuleCat.hom_ext (comparison_top _)).symm
    · change (0 : ModuleCat.of A Ce ⟶ ModuleCat.of A PUnit) ≫ 0 = _ ≫ 0
      erw [zero_comp]
  | negSucc n =>
    cases n with
    | zero =>
      change ModuleCat.ofHom rhoJ ≫ ModuleCat.ofHom (ceDiff (reverseCoeff 1)) = 0 ≫ 0
      rw [zero_comp]
      exact ModuleCat.hom_ext comparison_bottom
    | succ n =>
      change 0 ≫ _ = 0 ≫ 0
      rw [zero_comp,zero_comp]

def reverseComparison : forwardComplex ⟶ reverseComplex where
  f := comparisonComponent
  comm' i j hij := by
    have h : i = j+1 := by simpa [eq_comm] using hij
    subst i
    change comparisonComponent (j+1) ≫ ChainComplex.of.d _ reverseD (j+1) j =
      ChainComplex.of.d _ forwardD (j+1) j ≫ comparisonComponent j
    simp only [ChainComplex.of_d]
    exact comparison_comm j

theorem comparison_injective_cycles (x : Cf)
    (h : ∃ z : Ce, ceDiff (reverseCoeff 0) z = rhoJ x) : ∃ a : Ce, initialMap a = x := by
  obtain ⟨x,rfl⟩ := cfIso.surjective x
  obtain ⟨z,hz⟩ := h
  obtain ⟨z,rfl⟩ := ceIso.surjective z
  rw [ceDiff_iso,rhoJ_iso] at hz
  have he := congrFun (ceIso.injective hz) 5
  have hx : x 0 = 0 := by simpa [rightD,reverseCoeff_zero] using he.symm
  exact (characterAug_exact (cfIso x)).mp hx

theorem comparison_surjective_cycles (y : Ce) (h : ceDiff (reverseCoeff 1) y = 0) :
    ∃ x : Cf, ∃ z : Ce, ceDiff (reverseCoeff 0) z = rhoJ x-y := by
  obtain ⟨y,rfl⟩ := ceIso.surjective y
  rw [ceDiff_iso,← ceIso.map_zero] at h
  have hh := ceIso.injective h
  have h0 : y 0=0 := by have hi:=congrFun hh 1; simpa [rightD] using hi
  have h2 : y 2= -(1/4)*y 1 := by
    have hi:=congrFun hh 3
    norm_num [rightD,reverseCoeff_one] at hi
    linarith
  have h4 : y 4=0 := by
    have hi:=congrFun hh 5
    norm_num [rightD,reverseCoeff_one] at hi
    exact hi
  refine ⟨cfIso ![y 5,0,0,0],ceIso ![-y 1,0,-y 3,0,0,0], ?_⟩
  rw [ceDiff_iso,rhoJ_iso]
  apply Subtype.ext
  ext i
  cases i <;> norm_num [ceIso,ceEmbed,rightD,reverseCoeff_zero,h0,h2,h4,
    sub_eq_add_neg]

theorem forwardComplex_exactAt (j : ℤ) (hj : j ≠ 0) : forwardComplex.ExactAt j := by
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j=i+1 := ⟨j-1,by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x, ChainComplex.of.d _ forwardD (i+1) i x=0 →
    ∃ y, ChainComplex.of.d _ forwardD (i+1+1) (i+1) y=x
  simp only [ChainComplex.of_d]
  cases i with
  | ofNat n => exact fun x hx => (resD_exact n x).mp hx
  | negSucc n =>
    cases n with
    | zero => exact (hj rfl).elim
    | succ n =>
      intro x _
      exact ⟨0,@Subsingleton.elim PUnit inferInstance _ _⟩

theorem reverseComplex_exactAt (j : ℤ) (hj : j ≠ 0) : reverseComplex.ExactAt j := by
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j=i+1 := ⟨j-1,by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x, ChainComplex.of.d _ reverseD (i+1) i x=0 →
    ∃ y, ChainComplex.of.d _ reverseD (i+1+1) (i+1) y=x
  simp only [ChainComplex.of_d]
  cases i with
  | ofNat n =>
    rcases n with _ | _ | n
    · change ∀ x, ceDiff (reverseCoeff 0) x=0 → ∃ y, rhoT y=x
      rw [reverseCoeff_zero]
      exact fun x hx => (rhoT_exact x).mp hx
    · intro x hx
      refine ⟨0, ?_⟩
      exact (rhoT_injective (hx.trans (map_zero rhoT).symm)).symm
    · intro x _
      exact ⟨0,@Subsingleton.elim PUnit inferInstance _ _⟩
  | negSucc n =>
    rcases n with _ | _ | n
    · exact (hj rfl).elim
    · exact fun x hx => (reverseD_exact 0 x).mp hx
    · exact fun x hx => (reverseD_exact (n+1) x).mp hx

theorem reverseComparison_quasiIso : QuasiIso reverseComparison := by
  constructor
  intro j
  by_cases hj : j=0
  · subst j
    rw [quasiIsoAt_iff' _ 1 0 (-1) (by simp) (by simp)]
    apply OAI.Tachikawa.shortComplex_quasiIso_of_cycles
    · intro x _ hx
      exact comparison_injective_cycles x hx
    · intro y hy
      obtain ⟨x,z,hz⟩ := comparison_surjective_cycles y hy
      exact ⟨x,rfl,z,hz⟩
  · exact (quasiIsoAt_iff_exactAt reverseComparison j
      (forwardComplex_exactAt j hj)).mpr (reverseComplex_exactAt j hj)

theorem forward_term_projective (j : ℤ) : Projective (forwardComplex.X j) := by
  cases j with
  | ofNat n =>
    change Projective (resObj n)
    cases n <;> dsimp [resObj] <;> infer_instance
  | negSucc n => change Projective (ModuleCat.of A PUnit); infer_instance

theorem reverse_term_projective (j : ℤ) : Projective (reverseComplex.X j) := by
  cases j with
  | ofNat n =>
    change Projective (reverseObj (Int.ofNat n))
    rcases n with _ | _ | _ | n
    · exact inferInstanceAs (Projective (ModuleCat.of A Ce))
    · exact inferInstanceAs (Projective (ModuleCat.of A Ce))
    · exact inferInstanceAs (Projective (ModuleCat.of A Cf))
    · exact inferInstanceAs (Projective (ModuleCat.of A PUnit))
  | negSucc n => change Projective (ModuleCat.of A Ce); infer_instance

theorem forward_term_finiteA (j : ℤ) : Module.Finite A (forwardComplex.X j) := by
  cases j with
  | ofNat n =>
    change Module.Finite A (resObj n)
    cases n with
    | zero => exact cfFiniteA
    | succ n => exact ceFiniteA
  | negSucc n => change Module.Finite A PUnit; infer_instance

theorem reverse_term_finiteA (j : ℤ) : Module.Finite A (reverseComplex.X j) := by
  cases j with
  | ofNat n =>
    change Module.Finite A (reverseObj (Int.ofNat n))
    rcases n with _ | _ | _ | n
    · exact inferInstanceAs (Module.Finite A Ce)
    · exact inferInstanceAs (Module.Finite A Ce)
    · exact inferInstanceAs (Module.Finite A Cf)
    · exact inferInstanceAs (Module.Finite A PUnit)
  | negSucc n => change Module.Finite A Ce; infer_instance

theorem forward_term_finite (j : ℤ) : Module.Finite ℚ (forwardComplex.X j) := by
  let := forward_term_finiteA j
  exact Module.Finite.trans A _

theorem reverse_term_finite (j : ℤ) : Module.Finite ℚ (reverseComplex.X j) := by
  let := reverse_term_finiteA j
  exact Module.Finite.trans A _

end
end TachikawaCharZero.ReverseCorner
