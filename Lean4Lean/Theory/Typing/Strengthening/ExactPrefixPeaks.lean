import Lean4Lean.Theory.Typing.Strengthening.ExactPrefixCoreDiamond

/-! # Prefix parallel peaks with only core residuals

Two actual prefix/projection parallel developments meet after one further
prefix/projection development and finite core computation on each side.
The common output is literal syntax; no normal comparison is included.
-/
namespace Lean4Lean.VEnv.Strengthening.ExactPrefix
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

private theorem core_congrRel : CongrRel ParRedS where
  rfl := .rfl
  app := ParRedS.app
  proj := ParRedS.proj
  lam := ParRedS.lam
  forallE := ParRedS.forallE
  weakN := ParRedS.weakN

private theorem core_mkApps (hf : ParRedS Γ f f')
    (ha : List.Forall₂ (ParRedS Γ) args args') :
    ParRedS Γ (VExpr.mkApps f args) (VExpr.mkApps f' args') :=
  core_congrRel.mkApps hf ha

private theorem SpineRule.congr_delta_exact (hΓ : OnCtx Γ (env.IsType univs))
    (H : SpineRule Γ name ls xs rhs) (ha : List.Forall₂ (DeltaPar Γ) xs ys) :
    ∃ rhs', SpineRule Γ name ls ys rhs' ∧ DeltaPar Γ rhs rhs' := by
  rcases H with H | ⟨rfl, H⟩
  · obtain ⟨r, hr, h⟩ := singleton_prefix_congr DeltaPar.congrRel DeltaPar.argRel hΓ H ha
    exact ⟨r, .inl hr, h⟩
  · obtain ⟨r, hr, h⟩ := quotient_prefix_congr DeltaPar.congrRel DeltaPar.argRel hΓ H ha
    exact ⟨r, .inr ⟨rfl, hr⟩, h⟩

private theorem SpineRule.chain_exact (hΓ : OnCtx Γ (env.IsType univs))
    (H : SpineRule Γ name ls xs rhs) (ha : List.Forall₂ (ParRedS Γ) xs ys) :
    ∃ rhs', SpineRule Γ name ls ys rhs' ∧ ParRedS Γ rhs rhs' := by
  have J : ArgRel ParRedS := core_congrRel.argRel (fun hΓ H ht => ParRedS.defeq hΓ H ht)
  rcases H with H | ⟨rfl, H⟩
  · obtain ⟨r, hr, h⟩ := singleton_prefix_congr core_congrRel J hΓ H ha
    exact ⟨r, .inl hr, h⟩
  · obtain ⟨r, hr, h⟩ := quotient_prefix_congr core_congrRel J hΓ H ha
    exact ⟨r, .inr ⟨rfl, hr⟩, h⟩

/-- A common endpoint reached on each side by one prefix/projection parallel
step followed only by finite core computation. -/
def Join (Γ : List VExpr) (b c : VExpr) : Prop :=
  ∃ d, (∃ b₁, DeltaPar Γ b b₁ ∧ ParRedS Γ b₁ d) ∧
    (∃ c₁, DeltaPar Γ c c₁ ∧ ParRedS Γ c₁ d)

private theorem Join.app (hf : Join Γ f₁ f₂) (hx : Join Γ x₁ x₂) :
    Join Γ (.app f₁ x₁) (.app f₂ x₂) := by
  obtain ⟨df, ⟨F₁, pF₁, cF₁⟩, ⟨F₂, pF₂, cF₂⟩⟩ := hf
  obtain ⟨dx, ⟨X₁, pX₁, cX₁⟩, ⟨X₂, pX₂, cX₂⟩⟩ := hx
  exact ⟨_, ⟨_, .app pF₁ pX₁, ParRedS.app cF₁ cX₁⟩,
    ⟨_, .app pF₂ pX₂, ParRedS.app cF₂ cX₂⟩⟩

private theorem Join.proj (hm : Join Γ m₁ m₂) : Join Γ (.proj s i m₁) (.proj s i m₂) := by
  obtain ⟨dm, ⟨M₁, pM₁, cM₁⟩, ⟨M₂, pM₂, cM₂⟩⟩ := hm
  exact ⟨_, ⟨_, .proj pM₁, ParRedS.proj cM₁⟩, ⟨_, .proj pM₂, ParRedS.proj cM₂⟩⟩

private theorem Join.symm (H : Join Γ b c) : Join Γ c b :=
  let ⟨d, h1, h2⟩ := H; ⟨d, h2, h1⟩

private theorem DeltaPar.side_contr {X Y E : List VExpr} (hΓ : OnCtx Γ (env.IsType univs))
    (hrule : SpineRule Γ name ls (X.take k) r) (hX : List.Forall₂ (DeltaPar Γ) X Y)
    (hYE : List.Forall₂ (ParRedS Γ) Y E)
    (_hb : Γ ⊢ VExpr.mkApps r (X.drop k) : T) :
    ∃ rE, SpineRule Γ name ls (E.take k) rE ∧
      ∃ b₁, DeltaPar Γ (VExpr.mkApps r (X.drop k)) b₁ ∧
        ParRedS Γ b₁ (VExpr.mkApps rE (E.drop k)) := by
  obtain ⟨rY, hrY, pX⟩ := SpineRule.congr_delta_exact hΓ hrule (List.forall₂_take hX k)
  obtain ⟨rE, hrE, cE⟩ := SpineRule.chain_exact hΓ hrY (List.forall₂_take hYE k)
  exact ⟨rE, hrE, _, DeltaPar.mkApps pX (Lean4Lean.List.forall₂_drop hX k),
    core_mkApps cE (Lean4Lean.List.forall₂_drop hYE k)⟩

private theorem DeltaPar.side_cong {Z X Y E : List VExpr} (hΓ : OnCtx Γ (env.IsType univs))
    (hrule : SpineRule Γ name ls (Z.take k) rZ)
    (hdef : List.Forall₂ (IsDefEqU env univs Γ) (Z.take k) (Y.take k))
    (hX : List.Forall₂ (DeltaPar Γ) X Y)
    (hYE : List.Forall₂ (ParRedS Γ) Y E)
    (_hb : Γ ⊢ VExpr.mkApps (.const name ls) X : T) :
    ∃ rE, SpineRule Γ name ls (E.take k) rE ∧
      ∃ b₁, DeltaPar Γ (VExpr.mkApps (.const name ls) X) b₁ ∧
        ParRedS Γ b₁ (VExpr.mkApps rE (E.drop k)) := by
  obtain ⟨rY, hrY⟩ := hrule.congr_defeq hΓ hdef
  obtain ⟨rE, hrE, cE⟩ := SpineRule.chain_exact hΓ hrY (List.forall₂_take hYE k)
  have hstep : DeltaPar Γ (VExpr.mkApps (.const name ls) X) (VExpr.mkApps rY (Y.drop k)) := by
    rw [← List.take_append_drop k X, VExpr.mkApps_append]
    exact DeltaPar.mkApps (hrY.step (List.forall₂_take hX k)) (Lean4Lean.List.forall₂_drop hX k)
  refine ⟨rE, hrE, _, hstep, ?_⟩
  exact core_mkApps cE (Lean4Lean.List.forall₂_drop hYE k)

private theorem DeltaPar.side_extend {E : List VExpr} {k₁ k₂ : Nat}
    (hk : k₁ ≤ k₂)
    (H₁ : SpineRule Γ name ls (E.take k₁) r₁) (H₂ : SpineRule Γ name ls (E.take k₂) r₂) :
    ParRedS Γ (VExpr.mkApps r₁ (E.drop k₁)) (VExpr.mkApps r₂ (E.drop k₂)) := by
  have he : E.take k₂ = E.take k₁ ++ (E.drop k₁).take (k₂ - k₁) := by
    rw [List.take_drop]; rw [show k₁ + (k₂ - k₁) = k₂ by omega]
    exact (List.take_append_drop k₁ (E.take k₂) |>.symm.trans (by
      rw [List.take_take, Nat.min_eq_left hk, List.drop_take]))
  rw [he] at H₂
  have hs := H₁.supply_many H₂
  have hd : E.drop k₁ = (E.drop k₁).take (k₂ - k₁) ++ E.drop k₂ := by
    have := List.take_append_drop (k₂ - k₁) (E.drop k₁)
    rw [List.drop_drop] at this
    first
      | rw [show k₁ + (k₂ - k₁) = k₂ by omega] at this; exact this.symm
      | rw [show k₂ - k₁ + k₁ = k₂ by omega] at this; exact this.symm
  rw [hd, VExpr.mkApps_append]
  exact ParRedS.mkApps_head hs _

private theorem Join.lam (hΓ : OnCtx Γ (env.IsType univs)) (tD : Γ ⊢ D : .sort u)
    (hD : Join Γ D₁ D₂) (ht : Join (D :: Γ) t₁ t₂)
    (e₁ : Γ ⊢ D ≡ D₁ : .sort u) (e₂ : Γ ⊢ D ≡ D₂ : .sort u)
    (tt₁ : D :: Γ ⊢ t₁ : B₁) (tt₂ : D :: Γ ⊢ t₂ : B₂)
    (_h₁ : Γ ⊢ .lam D₁ t₁ : T₁) (_h₂ : Γ ⊢ .lam D₂ t₂ : T₂) :
    Join Γ (.lam D₁ t₁) (.lam D₂ t₂) := by
  obtain ⟨dD, ⟨X₁, pX₁, cX₁⟩, ⟨X₂, pX₂, cX₂⟩⟩ := hD
  obtain ⟨dt, ⟨S₁, pS₁, cS₁⟩, ⟨S₂, pS₂, cS₂⟩⟩ := ht
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, tD⟩
  have tS₁ := (DeltaPar.full pS₁).hasType hΓD tt₁
  have tS₂ := (DeltaPar.full pS₂).hasType hΓD tt₂
  have eX₁ := e₁.trans ((DeltaPar.full pX₁).defeq hΓ e₁.hasType.2)
  have eX₂ := e₂.trans ((DeltaPar.full pX₂).defeq hΓ e₂.hasType.2)
  have s₁ : DeltaPar Γ (.lam D₁ t₁) (.lam X₁ S₁) := .lam pX₁ (pS₁.defeqDFC hΓ (.succ .zero e₁) tt₁)
  have s₂ : DeltaPar Γ (.lam D₂ t₂) (.lam X₂ S₂) := .lam pX₂ (pS₂.defeqDFC hΓ (.succ .zero e₂) tt₂)
  exact ⟨_, ⟨_, s₁, ParRedS.lam cX₁ (ParRedS.defeqDFC hΓ (.succ .zero eX₁) tS₁ cS₁)⟩,
    ⟨_, s₂, ParRedS.lam cX₂ (ParRedS.defeqDFC hΓ (.succ .zero eX₂) tS₂ cS₂)⟩⟩

private theorem Join.forallE (hΓ : OnCtx Γ (env.IsType univs)) (tD : Γ ⊢ D : .sort u)
    (hD : Join Γ D₁ D₂) (ht : Join (D :: Γ) t₁ t₂)
    (e₁ : Γ ⊢ D ≡ D₁ : .sort u) (e₂ : Γ ⊢ D ≡ D₂ : .sort u)
    (tt₁ : D :: Γ ⊢ t₁ : B₁) (tt₂ : D :: Γ ⊢ t₂ : B₂)
    (_h₁ : Γ ⊢ .forallE D₁ t₁ : T₁) (_h₂ : Γ ⊢ .forallE D₂ t₂ : T₂) :
    Join Γ (.forallE D₁ t₁) (.forallE D₂ t₂) := by
  obtain ⟨dD, ⟨X₁, pX₁, cX₁⟩, ⟨X₂, pX₂, cX₂⟩⟩ := hD
  obtain ⟨dt, ⟨S₁, pS₁, cS₁⟩, ⟨S₂, pS₂, cS₂⟩⟩ := ht
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, tD⟩
  have tS₁ := (DeltaPar.full pS₁).hasType hΓD tt₁
  have tS₂ := (DeltaPar.full pS₂).hasType hΓD tt₂
  have eX₁ := e₁.trans ((DeltaPar.full pX₁).defeq hΓ e₁.hasType.2)
  have eX₂ := e₂.trans ((DeltaPar.full pX₂).defeq hΓ e₂.hasType.2)
  have s₁ : DeltaPar Γ (.forallE D₁ t₁) (.forallE X₁ S₁) :=
    .forallE pX₁ (pS₁.defeqDFC hΓ (.succ .zero e₁) tt₁)
  have s₂ : DeltaPar Γ (.forallE D₂ t₂) (.forallE X₂ S₂) :=
    .forallE pX₂ (pS₂.defeqDFC hΓ (.succ .zero e₂) tt₂)
  exact ⟨_, ⟨_, s₁, ParRedS.forallE cX₁ (ParRedS.defeqDFC hΓ (.succ .zero eX₁) tS₁ cS₁)⟩,
    ⟨_, s₂, ParRedS.forallE cX₂ (ParRedS.defeqDFC hΓ (.succ .zero eX₂) tS₂ cS₂)⟩⟩

/-- Peaks of parallel prefix steps below a size. -/
private abbrev DDBelow (s : Nat) : Prop :=
  ∀ {Γ a b c A}, sizeOf a < s → OnCtx Γ (env.IsType univs) → DeltaPar Γ a b → DeltaPar Γ a c →
    Γ ⊢ a : A → Join Γ b c

private theorem DeltaPar.join_args (hΓ : OnCtx Γ (env.IsType univs)) (IH : DDBelow s)
    (hsub : ∀ x ∈ args, sizeOf x < s) (htyped : ∀ x ∈ args, ∃ T, Γ ⊢ x : T)
    (h₁ : List.Forall₂ (DeltaPar Γ) args args₁) (h₂ : List.Forall₂ (DeltaPar Γ) args args₂) :
    ∃ B C E, List.Forall₂ (DeltaPar Γ) args₁ B ∧ List.Forall₂ (ParRedS Γ) B E ∧
      List.Forall₂ (DeltaPar Γ) args₂ C ∧ List.Forall₂ (ParRedS Γ) C E := by
  obtain ⟨us, vs, hus, hvs, heq⟩ := List.Forall₂.exists_join
    (S := fun y e => ∃ y', DeltaPar Γ y y' ∧ ParRedS Γ y' e)
    (T := fun z e => ∃ z', DeltaPar Γ z z' ∧ ParRedS Γ z' e) (U := Eq) h₁ h₂
    fun x _ _ hx p q => by
      obtain ⟨d, hb, hc⟩ := IH (hsub x hx) hΓ p q (htyped x hx).choose_spec
      exact ⟨d, d, hb, hc, rfl⟩
  cases forall₂_eq_imp heq
  obtain ⟨B, hB, hBE⟩ := List.forall₂_snoc_right hus
  obtain ⟨C, hC, hCE⟩ := List.forall₂_snoc_right hvs
  exact ⟨B, C, us, hB, hBE, hC, hCE⟩

private theorem DeltaPar.peak_spine (hΓ : OnCtx Γ (env.IsType univs))
    (IH : DDBelow (sizeOf (VExpr.mkApps (.const name ls) args)))
    (ha : Γ ⊢ VExpr.mkApps (.const name ls) args : A)
    (H1 : DeltaPar Γ (VExpr.mkApps (.const name ls) args) b)
    (H2 : DeltaPar Γ (VExpr.mkApps (.const name ls) args) c) : Join Γ b c := by
  have hb := (DeltaPar.full H1).hasType hΓ ha
  have hc := (DeltaPar.full H2).hasType hΓ ha
  obtain ⟨args₁, h₁, cb⟩ := DeltaPar.const_spine_cases H1
  obtain ⟨args₂, h₂, cc⟩ := DeltaPar.const_spine_cases H2
  have targs := HasType.mkApps_args_typed hΓ ha
  obtain ⟨B, C, E, hB, hBE, hC, hCE⟩ := DeltaPar.join_args hΓ IH
    (fun _ hx => sizeOf_mkApps_arg hx) targs h₁ h₂
  have targs₁ := forall₂_typed_of_deltaPar hΓ targs h₁
  have targs₂ := forall₂_typed_of_deltaPar hΓ targs h₂
  have d₁ := forall₂_deltaPar_defeq hΓ targs h₁
  have d₂ := forall₂_deltaPar_defeq hΓ targs h₂
  have dB := forall₂_deltaPar_defeq hΓ targs₁ hB
  have dC := forall₂_deltaPar_defeq hΓ targs₂ hC
  -- definitional equality between the two developments of the arguments
  have d₂B : List.Forall₂ (IsDefEqU env univs Γ) args₂ B :=
    forall₂_defeq_trans hΓ (forall₂_defeq_trans hΓ (forall₂_defeq_symm d₂) d₁) dB
  have d₁C : List.Forall₂ (IsDefEqU env univs Γ) args₁ C :=
    forall₂_defeq_trans hΓ (forall₂_defeq_trans hΓ (forall₂_defeq_symm d₁) d₂) dC
  rcases cb with rfl | ⟨k₁, r₁, hk₁, hr₁, rfl⟩ <;> rcases cc with rfl | ⟨k₂, r₂, hk₂, hr₂, rfl⟩
  · have s₁ := DeltaPar.mkApps_args (f := .const name ls) hB
    have s₂ := DeltaPar.mkApps_args (f := .const name ls) hC
    exact ⟨_, ⟨_, s₁, core_mkApps .rfl hBE⟩,
      ⟨_, s₂, core_mkApps .rfl hCE⟩⟩
  · obtain ⟨rE, hrE, b₁, pb, cb⟩ := DeltaPar.side_cong hΓ hr₂ (List.forall₂_take d₂B k₂) hB hBE hb
    obtain ⟨rE', hrE', c₁, pc, cc⟩ := DeltaPar.side_contr hΓ hr₂ hC hCE hc
    cases hrE.unique hrE'
    exact ⟨_, ⟨_, pb, cb⟩, ⟨_, pc, cc⟩⟩
  · obtain ⟨rE, hrE, b₁, pb, cb⟩ := DeltaPar.side_contr hΓ hr₁ hB hBE hb
    obtain ⟨rE', hrE', c₁, pc, cc⟩ := DeltaPar.side_cong hΓ hr₁ (List.forall₂_take d₁C k₁) hC hCE hc
    cases hrE.unique hrE'
    exact ⟨_, ⟨_, pb, cb⟩, ⟨_, pc, cc⟩⟩
  · obtain ⟨rE₁, hrE₁, b₁, pb, cb⟩ := DeltaPar.side_contr hΓ hr₁ hB hBE hb
    obtain ⟨rE₂, hrE₂, c₁, pc, cc⟩ := DeltaPar.side_contr hΓ hr₂ hC hCE hc
    rcases Nat.le_total k₁ k₂ with hk | hk
    · exact ⟨_, ⟨_, pb, cb.trans (DeltaPar.side_extend hk hrE₁ hrE₂)⟩, ⟨_, pc, cc⟩⟩
    · exact ⟨_, ⟨_, pb, cb⟩, ⟨_, pc, cc.trans (DeltaPar.side_extend hk hrE₂ hrE₁)⟩⟩

private theorem DeltaPar.peak_cong_iota (hΓ : OnCtx Γ (env.IsType univs))
    (IH : DDBelow (sizeOf (VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args))))
    (ha : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args) : A)
    (hm₁ : DeltaPar Γ (VExpr.mkApps (.const info.ctorName ls) args) m₁)
    (hlen : args.length = args₂.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args₂.length), DeltaPar Γ args[i] args₂[i])
    (hl : env.projections family info)
    (hs : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args₂) : fieldType)
    (hi : args₂[info.nparams + index]? = some field) (ht : Γ ⊢ field : fieldType) :
    Join Γ (.proj family index m₁) field := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
  obtain ⟨args₁, rfl, h₁⟩ := DeltaPar.rigid_spine (projection_ctor_rigid hl) hm₁
  have h₂ := List.forall₂_of_getElem hlen hargs
  have hb := (DeltaPar.full (.proj hm₁)).hasType hΓ ha
  have hc := (DeltaPar.full (.projIota hlen hargs hl hs hi ht)).hasType hΓ ha
  have targs := HasType.mkApps_args_typed hΓ lm.hasType.2
  obtain ⟨B, C, E, hB, hBE, hC, hCE⟩ := DeltaPar.join_args hΓ IH
    (fun _ hx => by have := sizeOf_mkApps_arg (f := .const info.ctorName ls) hx; simp; omega)
    targs h₁ h₂
  have targs₁ := forall₂_typed_of_deltaPar hΓ targs h₁
  have targs₂ := forall₂_typed_of_deltaPar hΓ targs h₂
  have d₁ := forall₂_deltaPar_defeq hΓ targs h₁
  have d₂ := forall₂_deltaPar_defeq hΓ targs h₂
  have dB := forall₂_deltaPar_defeq hΓ targs₁ hB
  have d₂B : List.Forall₂ (IsDefEqU env univs Γ) args₂ B :=
    forall₂_defeq_trans hΓ (forall₂_defeq_trans hΓ (forall₂_defeq_symm d₂) d₁) dB
  obtain ⟨bk, hbk, ebk⟩ := forall₂_getElem?_left d₂B hi
  obtain ⟨ek, hek, cbk⟩ := forall₂_getElem?_left hBE hbk
  obtain ⟨ck, hck, pck⟩ := forall₂_getElem?_left hC hi
  obtain ⟨ek', hek', cck⟩ := forall₂_getElem?_left hCE hck
  cases hek.symm.trans hek'
  have hcong : DeltaPar Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls) args₁))
      (.proj family index (VExpr.mkApps (.const info.ctorName ls) B)) :=
    .proj (DeltaPar.mkApps_args hB)
  have hT := (DeltaPar.full hcong).hasType hΓ hb
  have hbkT := hc.defeqU_l henv hΓ ebk
  have ⟨hl₂, hx₂⟩ := getElem_of_forall₂ hB
  exact ⟨ek, ⟨bk, .projIota hl₂ hx₂ hl hT hbk hbkT, cbk⟩, ⟨ck, pck, cck⟩⟩

private theorem DeltaPar.peak_iota (hΓ : OnCtx Γ (env.IsType univs))
    (IH : DDBelow (sizeOf (VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args))))
    (ha : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args) : A)
    (hlen : args.length = args₁.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args₁.length), DeltaPar Γ args[i] args₁[i])
    (hl : env.projections family info)
    (hs : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args₁) : fieldType)
    (hi : args₁[info.nparams + index]? = some field) (ht : Γ ⊢ field : fieldType)
    (H2 : DeltaPar Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls) args)) c) :
    Join Γ field c := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
  generalize hE : VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args) = E at H2
  cases H2 with
  | proj hm₂ =>
    cases hE
    exact (DeltaPar.peak_cong_iota hΓ IH ha hm₂ hlen hargs hl hs hi ht).symm
  | projIota hlen' hargs' hl' hs' hi' ht' =>
    injection hE with hf hidx hM
    subst hf hidx
    obtain ⟨hc', rfl, rfl⟩ := VExpr.mkApps_const_inj hM
    cases henv.ordered.projections_unique hl hl'
    have targs := HasType.mkApps_args_typed hΓ lm.hasType.2
    have h₁ := List.forall₂_of_getElem hlen hargs
    have h₂ := List.forall₂_of_getElem hlen' hargs'
    obtain ⟨x, hx, hx₁⟩ := forall₂_getElem?_right h₁ hi
    obtain ⟨y, hy, hy₂⟩ := forall₂_getElem?_left h₂ hx
    rw [hi'] at hy
    cases hy
    have hxmem : x ∈ args := List.mem_of_getElem? hx
    exact IH (by have := sizeOf_mkApps_arg (f := .const info.ctorName ls) hxmem; simp; omega)
      hΓ hx₁ hy₂ (targs x hxmem).choose_spec
  | delta => exact absurd hE.symm mkApps_const_ne_proj
  | quotDelta => exact absurd hE.symm mkApps_const_ne_proj
  | _ => cases hE

private theorem DeltaPar.peak_aux : ∀ n, DDBelow n := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
  intro Γ a b c A hsz hΓ H1 H2 ha
  have hb := (DeltaPar.full H1).hasType hΓ ha
  have hc := (DeltaPar.full H2).hasType hΓ ha
  have IH : DDBelow (sizeOf a) := fun h => ih (by omega)
  obtain ⟨h, as, rfl, hh⟩ := exists_spine a
  rcases List.eq_nil_or_snoc as with rfl | ⟨as₀, x, rfl⟩
  · change Γ ⊢ h : A at ha
    change DeltaPar Γ h b at H1
    change DeltaPar Γ h c at H2
    change DDBelow (sizeOf h) at IH
    cases h with
    | const name ls => exact DeltaPar.peak_spine (args := []) hΓ IH ha H1 H2
    | app => exact absurd rfl (hh _ _)
    | proj s i m =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
      generalize hE : VExpr.proj s i m = E at H1
      cases H1 with
      | proj hm₁ =>
        cases hE
        generalize hE₂ : VExpr.proj s i m = E₂ at H2
        cases H2 with
        | proj hm₂ =>
          cases hE₂
          exact Join.proj (IH (by simp; omega) hΓ hm₁ hm₂ lm.hasType.2)
        | projIota hlen hargs hl hs hi ht =>
          injection hE₂ with hf hidx hM
          subst hf hidx hM
          exact DeltaPar.peak_cong_iota hΓ IH ha hm₁ hlen hargs hl hs hi ht
        | delta => exact absurd hE₂.symm mkApps_const_ne_proj
        | quotDelta => exact absurd hE₂.symm mkApps_const_ne_proj
        | _ => cases hE₂
      | projIota hlen hargs hl hs hi ht =>
        injection hE with hf hidx hM
        subst hf hidx hM
        exact DeltaPar.peak_iota hΓ IH ha hlen hargs hl hs hi ht H2
      | delta => exact absurd hE.symm mkApps_const_ne_proj
      | quotDelta => exact absurd hE.symm mkApps_const_ne_proj
      | _ => cases hE
    | lam D t =>
      obtain ⟨⟨_, tD⟩, _, tt⟩ := ha.lam_inv henv hΓ
      have hΓ' : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, tD⟩
      obtain ⟨D₁, t₁, hD₁, ht₁, rfl⟩ := DeltaPar.lam_inv H1
      obtain ⟨D₂, t₂, hD₂, ht₂, rfl⟩ := DeltaPar.lam_inv H2
      exact Join.lam hΓ tD (IH (by simp; omega) hΓ hD₁ hD₂ tD) (IH (by simp; omega) hΓ' ht₁ ht₂ tt)
        ((DeltaPar.full hD₁).defeq hΓ tD) ((DeltaPar.full hD₂).defeq hΓ tD)
        ((DeltaPar.full ht₁).hasType hΓ' tt) ((DeltaPar.full ht₂).hasType hΓ' tt) hb hc
    | forallE D t =>
      obtain ⟨⟨_, tD⟩, _, tt⟩ := ha.forallE_inv henv
      have hΓ' : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, tD⟩
      obtain ⟨D₁, t₁, hD₁, ht₁, rfl⟩ := DeltaPar.forallE_inv H1
      obtain ⟨D₂, t₂, hD₂, ht₂, rfl⟩ := DeltaPar.forallE_inv H2
      exact Join.forallE hΓ tD (IH (by simp; omega) hΓ hD₁ hD₂ tD)
        (IH (by simp; omega) hΓ' ht₁ ht₂ tt)
        ((DeltaPar.full hD₁).defeq hΓ tD) ((DeltaPar.full hD₂).defeq hΓ tD)
        ((DeltaPar.full ht₁).hasType hΓ' tt) ((DeltaPar.full ht₂).hasType hΓ' tt) hb hc
    | bvar | sort =>
      rw [DeltaPar.atom_inv (by intros; intro h; cases h) (by intros; intro h; cases h)
        (by intros; intro h; cases h) (by intros; intro h; cases h) (by intros; intro h; cases h) H1,
        DeltaPar.atom_inv (by intros; intro h; cases h) (by intros; intro h; cases h)
        (by intros; intro h; cases h) (by intros; intro h; cases h) (by intros; intro h; cases h) H2]
      exact ⟨_, ⟨_, .rfl, .rfl⟩, ⟨_, .rfl, .rfl⟩⟩
  · by_cases hconst : ∃ c ls, h = .const c ls
    · obtain ⟨c, ls, rfl⟩ := hconst
      exact DeltaPar.peak_spine hΓ IH ha H1 H2
    · have hnc : ∀ c ls, h ≠ .const c ls := fun c ls he => hconst ⟨c, ls, he⟩
      rw [VExpr.mkApps_snoc] at ha H1 H2 IH
      obtain ⟨_, _, tf, tx⟩ := ha.app_inv henv hΓ
      obtain ⟨f₁, x₁, rfl, hf₁, hx₁⟩ := DeltaPar.app_inv_head hnc hh H1
      obtain ⟨f₂, x₂, rfl, hf₂, hx₂⟩ := DeltaPar.app_inv_head hnc hh H2
      exact Join.app (IH (by simp; omega) hΓ hf₁ hf₂ tf) (IH (by simp; omega) hΓ hx₁ hx₂ tx)

/-- Two prefix/projection parallel steps from a typed source have exact
residual joins: one further prefix/projection step and only core computation
on each side. Differing contraction arities are joined by beta supply. -/
theorem parallel_peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : DeltaPar Γ a b) (H2 : DeltaPar Γ a c) (ha : Γ ⊢ a : A) : Join Γ b c :=
  DeltaPar.peak_aux _ (Nat.lt_succ_self _) hΓ H1 H2 ha

end Lean4Lean.VEnv.Strengthening.ExactPrefix
