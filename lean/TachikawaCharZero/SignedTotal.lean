import OAI.RingTheory.Tachikawa.Coresolution

/-! Signed comparison of a total cochain complex with Hom from a total
chain complex, over any field. The degreewise and horizontal arguments
are adapted from OpenAI Math's Tachikawa/OuterExt.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
The vertical comparison retains (-1)^i on both sides; no characteristic-two
assumption or cancellation of signs is used. -/
open OAI.Tachikawa
noncomputable section

namespace TachikawaCharZero
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {I : Type} (F : I → ModuleCat R) (N : ModuleCat R)

def coproductHomEquiv : (∐ F ⟶ N) ≃ₗ[k] (∀ i, F i ⟶ N) where
  toFun f i := Sigma.ι F i ≫ f
  invFun f := Sigma.desc f
  left_inv f := Sigma.hom_ext _ _ (fun i => by simp)
  right_inv f := funext fun i => by simp
  map_add' f g := funext fun i => by simp only [Pi.add_apply, Preadditive.comp_add]
  map_smul' r f := funext fun i => by simp only [Pi.smul_apply, RingHom.id_apply, CategoryTheory.Linear.comp_smul]

variable {J : Type} [Finite J] (G : J → ModuleCat k)

def coproductPiEquiv : (∐ G : ModuleCat k) ≃ₗ[k] (∀ i, G i) :=
  ((biproduct.isoCoproduct G).symm ≪≫ ModuleCat.biproductIsoPi G).toLinearEquiv

theorem coproductPiEquiv_ι (i j : J) (x : G i) :
    coproductPiEquiv G (Sigma.ι G i x) j =
      (biproduct.ι G i ≫ biproduct.π G j) x := by
  have h : Sigma.ι G i ≫ (biproduct.isoCoproduct G).inv = biproduct.ι G i := by simp
  have h' : (ModuleCat.biproductIsoPi G).hom ≫
      ModuleCat.ofHom (LinearMap.proj j) = biproduct.π G j := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π, Iso.hom_inv_id_assoc]
  change ((Sigma.ι G i ≫ (biproduct.isoCoproduct G).inv ≫
    (ModuleCat.biproductIsoPi G).hom ≫ ModuleCat.ofHom (LinearMap.proj j)) x) = _
  rw [h', ← Category.assoc, h]

theorem coproductPiEquiv_ι_self (i : J) (x : G i) :
    coproductPiEquiv G (Sigma.ι G i x) i = x := by
  rw [coproductPiEquiv_ι, biproduct.ι_π_self]
  rfl

theorem coproductPiEquiv_ι_ne {i j : J} (h : i ≠ j) (x : G i) :
    coproductPiEquiv G (Sigma.ι G i x) j = 0 := by
  rw [coproductPiEquiv_ι, biproduct.ι_π_ne _ h]
  rfl

end TachikawaCharZero

namespace TachikawaCharZero.SignedTotalPairing
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

instance : ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun (i : Multiplicative ℕ) => (-1 : ℤˣ)^i.toAdd)
    (fun i j => pow_add (-1 : ℤˣ) i.toAdd j.toAdd)
  rel_add p q r (h : p+1=q) := by change p+r+1=q+r; omega
  add_rel p q r (h : p+1=q) := by change r+p+1=r+q; omega
  ε'_succ := by
    intro p q h
    change p+1=q at h
    change (-1 : ℤˣ)^q = -(-1 : ℤˣ)^p
    subst q
    rw [pow_succ, mul_neg, mul_one]

abbrev Diag (n : ℕ) := {ij : ℕ × ℕ // ij.1 + ij.2 = n}
variable (K : HomologicalComplex₂ (ModuleCat R) (.down ℕ) (.down ℕ))
  (G : HomologicalComplex₂ (ModuleCat k) (.up ℕ) (.up ℕ)) (N : ModuleCat R)
  (p : ∀ i j, (G.X i).X j ≃ₗ[k] ((K.X i).X j ⟶ N))

abbrev chainFamily (n : ℕ) (t : Diag n) : ModuleCat R := (K.X t.val.1).X t.val.2
abbrev cochainFamily (n : ℕ) (t : Diag n) : ModuleCat k := (G.X t.val.1).X t.val.2

instance (n : ℕ) : Finite (Diag n) := by
  let f : Diag n → Fin (n+1) × Fin (n+1) := fun t =>
    (⟨t.val.1, by have := t.property; omega⟩, ⟨t.val.2, by have := t.property; omega⟩)
  apply Finite.of_injective f
  intro t u h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z : Fin (n+1) × Fin (n+1) => z.1.val) h)
    (congrArg (fun z : Fin (n+1) × Fin (n+1) => z.2.val) h)

def equiv (n : ℕ) : (G.total (.up ℕ)).X n ≃ₗ[k] ((K.total (.down ℕ)).X n ⟶ N) :=
  (coproductPiEquiv (cochainFamily G n)).trans
    ((LinearEquiv.piCongrRight (fun t : Diag n => p t.val.1 t.val.2)).trans
      (coproductHomEquiv (k := k) (chainFamily K n) N).symm)

theorem evaluate (n i j : ℕ) (h : i+j=n) (z : (G.total (.up ℕ)).X n) :
    K.ιTotal (.down ℕ) i j n h ≫ equiv K G N p n z =
      p i j (coproductPiEquiv (cochainFamily G n) z ⟨(i,j),h⟩) := by
  exact congrFun ((coproductHomEquiv (k := k) (chainFamily K n) N).apply_symm_apply
    (fun t : Diag n => p t.val.1 t.val.2 (coproductPiEquiv (cochainFamily G n) z t))) ⟨(i,j),h⟩

theorem evaluate_ι_self (n i j : ℕ) (h : i+j=n) (x : (G.X i).X j) :
    K.ιTotal (.down ℕ) i j n h ≫
      equiv K G N p n (G.ιTotal (.up ℕ) i j n h x) = p i j x := by
  rw [evaluate]
  change p i j (coproductPiEquiv (cochainFamily G n)
    (Sigma.ι (cochainFamily G n) ⟨(i,j),h⟩ x) ⟨(i,j),h⟩) = _
  rw [coproductPiEquiv_ι_self]

theorem evaluate_ι_ne (n i j a b : ℕ) (h : i+j=n) (h' : a+b=n)
    (hne : (a,b) ≠ (i,j)) (x : (G.X i).X j) :
    K.ιTotal (.down ℕ) a b n h' ≫
      equiv K G N p n (G.ιTotal (.up ℕ) i j n h x) = 0 := by
  rw [evaluate]
  change p a b (coproductPiEquiv (cochainFamily G n)
    (Sigma.ι (cochainFamily G n) ⟨(i,j),h⟩ x) ⟨(a,b),h'⟩) = _
  rw [coproductPiEquiv_ι_ne _ (show (⟨(i,j),h⟩ : Diag n) ≠ ⟨(a,b),h'⟩ by
    intro he; exact hne (congrArg Subtype.val he).symm), map_zero]

end TachikawaCharZero.SignedTotalPairing



namespace TachikawaCharZero.SignedTotalPairing
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

variable (K : HomologicalComplex₂ (ModuleCat R) (.down ℕ) (.down ℕ))
  (G : HomologicalComplex₂ (ModuleCat k) (.up ℕ) (.up ℕ)) (N : ModuleCat R)
  (p : ∀ i j, (G.X i).X j ≃ₗ[k] ((K.X i).X j ⟶ N))

theorem up_d₁ (i j n : ℕ) (h : i+1+j=n) :
    G.d₁ (.up ℕ) i j n =
      (G.d i (i+1)).f j ≫ G.ιTotal (.up ℕ) (i+1) j n h := by
  rw [G.d₁_eq (.up ℕ) (show (ComplexShape.up ℕ).Rel i (i+1) from rfl) j n h]
  change (1 : ℤˣ) • _ = _
  exact one_smul _ _

theorem up_d₂ (i j n : ℕ) (h : i+(j+1)=n) :
    G.d₂ (.up ℕ) i j n =
      ((-1 : ℤˣ)^i) • ((G.X i).d j (j+1) ≫ G.ιTotal (.up ℕ) i (j+1) n h) := by
  rw [G.d₂_eq (.up ℕ) i (show (ComplexShape.up ℕ).Rel j (j+1) from rfl) n h]
  rfl

theorem down_d₁ (i j n : ℕ) (h : i+j=n) :
    K.d₁ (.down ℕ) (i+1) j n =
      (K.d (i+1) i).f j ≫ K.ιTotal (.down ℕ) i j n h := by
  rw [K.d₁_eq (.down ℕ) (show (ComplexShape.down ℕ).Rel (i+1) i from rfl) j n h]
  change (1 : ℤˣ) • _ = _
  exact one_smul _ _

theorem down_d₂ (i j n : ℕ) (h : i+j=n) :
    K.d₂ (.down ℕ) i (j+1) n =
      ((-1 : ℤˣ)^i) • ((K.X i).d (j+1) j ≫ K.ιTotal (.down ℕ) i j n h) := by
  rw [K.d₂_eq (.down ℕ) i (show (ComplexShape.down ℕ).Rel (j+1) j from rfl) n h]
  rfl

theorem equiv_units_smul (n : ℕ) (u : ℤˣ) (x : (G.total (.up ℕ)).X n) :
    equiv K G N p n (u • x)=u • equiv K G N p n x := by
  rcases Int.units_eq_one_or u with h | h
  · rw [h]; simp
  · rw [h]; simp only [Units.neg_smul,one_smul,map_neg]

theorem down_d₁_zero (j n : ℕ) : K.d₁ (.down ℕ) 0 j n = 0 :=
  K.d₁_eq_zero (.down ℕ) 0 j n (by change ¬ _+1=0; omega)

theorem down_d₂_zero (i n : ℕ) : K.d₂ (.down ℕ) i 0 n = 0 :=
  K.d₂_eq_zero (.down ℕ) i 0 n (by change ¬ _+1=0; omega)

variable (hp₁ : ∀ i j (x : (G.X i).X j),
  p (i+1) j ((G.d i (i+1)).f j x) = (K.d (i+1) i).f j ≫ p i j x)
variable (hp₂ : ∀ i j (x : (G.X i).X j),
  p i (j+1) ((G.X i).d j (j+1) x) = (K.X i).d (j+1) j ≫ p i j x)

include hp₁ in
theorem horizontal (n i j a b : ℕ) (h : i+j=n) (h' : a+b=n+1) (x : (G.X i).X j) :
    K.ιTotal (.down ℕ) a b (n+1) h' ≫
      equiv K G N p (n+1) (G.d₁ (.up ℕ) i j (n+1) x) =
    K.d₁ (.down ℕ) a b n ≫
      equiv K G N p n (G.ιTotal (.up ℕ) i j n h x) := by
  rw [up_d₁ G i j (n+1) (by omega)]
  change K.ιTotal (.down ℕ) a b (n+1) h' ≫
      equiv K G N p (n+1) (G.ιTotal (.up ℕ) (i+1) j (n+1) _ ((G.d i (i+1)).f j x)) = _
  cases a with
  | zero =>
    rw [down_d₁_zero, zero_comp]
    exact evaluate_ι_ne K G N p _ _ _ _ _ _ _ (by
      intro he
      have hc := congrArg (fun t : ℕ × ℕ => t.1) he
      dsimp at hc
      omega) _
  | succ a =>
    rw [down_d₁ K a b n (by omega), Category.assoc]
    by_cases hab : (a,b) = (i,j)
    · have ha := congrArg Prod.fst hab
      have hb := congrArg Prod.snd hab
      dsimp at ha hb
      subst a b
      rw [evaluate_ι_self, evaluate_ι_self]
      exact hp₁ i j x
    · rw [evaluate_ι_ne K G N p _ _ _ _ _ _ _ hab, comp_zero]
      exact evaluate_ι_ne K G N p _ _ _ _ _ _ _ (by
        intro he
        apply hab
        have h1 := congrArg (fun t : ℕ × ℕ => t.1) he
        have h2 := congrArg (fun t : ℕ × ℕ => t.2) he
        apply Prod.ext <;> dsimp at * <;> omega) _

include hp₂ in
theorem vertical (n i j a b : ℕ) (h : i+j=n) (h' : a+b=n+1) (x : (G.X i).X j) :
    K.ιTotal (.down ℕ) a b (n+1) h' ≫
      equiv K G N p (n+1) (G.d₂ (.up ℕ) i j (n+1) x) =
    K.d₂ (.down ℕ) a b n ≫
      equiv K G N p n (G.ιTotal (.up ℕ) i j n h x) := by
  rw [up_d₂ G i j (n+1) (by omega)]
  change K.ιTotal (.down ℕ) a b (n+1) h' ≫
      equiv K G N p (n+1) (((-1 : ℤˣ)^i) •
        (G.ιTotal (.up ℕ) i (j+1) (n+1) _ ((G.X i).d j (j+1) x))) = _
  rw [equiv_units_smul,CategoryTheory.Linear.comp_units_smul]
  cases b with
  | zero =>
    rw [down_d₂_zero,zero_comp]
    rw [evaluate_ι_ne K G N p _ _ _ _ _ _ _ (by
      intro he
      have hc := congrArg (fun t : ℕ × ℕ => t.2) he
      dsimp at hc
      omega) _,smul_zero]
  | succ b =>
    rw [down_d₂ K a b n (by omega),CategoryTheory.Linear.units_smul_comp,Category.assoc]
    by_cases hab : (a,b)=(i,j)
    · have ha := congrArg Prod.fst hab
      have hb := congrArg Prod.snd hab
      dsimp at ha hb
      subst a b
      rw [evaluate_ι_self,evaluate_ι_self,hp₂]
    · rw [evaluate_ι_ne K G N p _ _ _ _ _ _ _ hab,comp_zero,smul_zero]
      rw [evaluate_ι_ne K G N p _ _ _ _ _ _ _ (by
        intro he
        apply hab
        have h1 := congrArg (fun t : ℕ × ℕ => t.1) he
        have h2 := congrArg (fun t : ℕ × ℕ => t.2) he
        apply Prod.ext <;> dsimp at * <;> omega) _,smul_zero]

end TachikawaCharZero.SignedTotalPairing



namespace TachikawaCharZero.SignedTotalPairing
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (K : HomologicalComplex₂ (ModuleCat R) (.down ℕ) (.down ℕ))
  (G : HomologicalComplex₂ (ModuleCat k) (.up ℕ) (.up ℕ)) (N : ModuleCat R)
  (p : ∀ i j, (G.X i).X j ≃ₗ[k] ((K.X i).X j ⟶ N))
  (hp₁ : ∀ i j (x : (G.X i).X j),
    p (i+1) j ((G.d i (i+1)).f j x) = (K.d (i+1) i).f j ≫ p i j x)
  (hp₂ : ∀ i j (x : (G.X i).X j),
    p i (j+1) ((G.X i).d j (j+1) x) = (K.X i).d (j+1) j ≫ p i j x)

include hp₁ hp₂ in
theorem comm (n : ℕ) :
    (G.total (.up ℕ)).d n (n+1) ≫ ModuleCat.ofHom (equiv K G N p (n+1)).toLinearMap =
    ModuleCat.ofHom (equiv K G N p n).toLinearMap ≫
      (resolutionHom k R (K.total (.down ℕ)) N).d n (n+1) := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  erw [← Category.assoc, total_d, Preadditive.comp_add, ι_D₁, ι_D₂,
    Preadditive.add_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (equiv K G N p (n+1) (G.d₁ (.up ℕ) i j (n+1) x)) +
    (equiv K G N p (n+1) (G.d₂ (.up ℕ) i j (n+1) x)) =
    (K.total (.down ℕ)).d (n+1) n ≫
      (equiv K G N p n (G.ιTotal (.up ℕ) i j n h x))
  apply HomologicalComplex₂.total.hom_ext
  intro a b h'
  erw [Preadditive.comp_add, horizontal K G N p hp₁ n i j a b h h' x,
    vertical K G N p hp₂ n i j a b h h' x, ← Category.assoc,
    total_d, Preadditive.comp_add, ι_D₁, ι_D₂, Preadditive.add_comp]

def comparison : G.total (.up ℕ) ⟶ resolutionHom k R (K.total (.down ℕ)) N where
  f n := ModuleCat.ofHom (equiv K G N p n).toLinearMap
  comm' n n' h := by
    change n+1=n' at h
    subst n'
    exact (comm K G N p hp₁ hp₂ n).symm

instance : IsIso (comparison K G N p hp₁ hp₂) := by
  have (n : ℕ) : IsIso ((comparison K G N p hp₁ hp₂).f n) :=
    (equiv K G N p n).toModuleIso.isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components _

def iso : G.total (.up ℕ) ≅ resolutionHom k R (K.total (.down ℕ)) N :=
  asIso (comparison K G N p hp₁ hp₂)

end TachikawaCharZero.SignedTotalPairing



