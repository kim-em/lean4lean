import Lean4Lean.Theory.Typing.Strengthening.EtaStep

/-! # Exact diamond for typed parallel eta expansion

The eta/eta peak proof can retain only parallel eta on both outgoing sides.
Root expansions are replayed at the other endpoint and copied beneath the
first expansion; binder bodies are transported through their original domains.
Neither computation nor ordinary normal comparison is needed in this diamond.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A

/-- One parallel eta step from each endpoint reaches literally the same term. -/
def ParallelEtaJoin (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ out, EtaPar Γ a out ∧ EtaPar Γ b out

private theorem ParallelEtaJoin.symm (H : ParallelEtaJoin Γ a b) : ParallelEtaJoin Γ b a :=
  let ⟨out, RA, RB⟩ := H; ⟨out, RB, RA⟩

private theorem ParallelEtaJoin.fun_left (_hΓ : OnCtx Γ (env.IsType univs))
    (J : ParallelEtaJoin Γ b₀ c) (HD : EtaPar Γ D D') (hc : Γ ⊢ c : .forallE D B)
    (_hb : Γ ⊢ .lam D' (.app b₀.lift (.bvar 0)) : T) :
    ParallelEtaJoin Γ (.lam D' (.app b₀.lift (.bvar 0))) c := by
  obtain ⟨out, RB, RC⟩ := J
  exact ⟨_, .lam .rfl (.app (RB.weakN .one) .rfl), .funEta RC HD hc⟩

private theorem ParallelEtaJoin.struct_left (_hΓ : OnCtx Γ (env.IsType univs))
    (J : ParallelEtaJoin Γ b₀ c)
    (hl : env.projections family info) (hp : ps.length = info.nparams) (hi : info.nindices = 0)
    (hlen : ps.length = ps'.length)
    (hps : ∀ i (h : i < ps.length) (h' : i < ps'.length), EtaPar Γ ps[i] ps'[i])
    (hc : Γ ⊢ c : mkApps (.const family levels) ps)
    (hcexp : Γ ⊢ structExpand family info levels ps c : mkApps (.const family levels) ps)
    (_hb : Γ ⊢ structExpand family info levels ps' b₀ : T) :
    ParallelEtaJoin Γ (structExpand family info levels ps' b₀) c := by
  obtain ⟨out, RB, RC⟩ := J
  exact ⟨_, RB.expand_congr, .structEta RC hlen hps hl hp hi hc hcexp⟩

private theorem ParallelEtaJoin.app (_hΓ : OnCtx Γ (env.IsType univs))
    (HF : ParallelEtaJoin Γ f₁ f₂) (HA : ParallelEtaJoin Γ a₁ a₂)
    (_h₁ : Γ ⊢ .app f₁ a₁ : T) (_h₂ : Γ ⊢ .app f₂ a₂ : T) :
    ParallelEtaJoin Γ (.app f₁ a₁) (.app f₂ a₂) := by
  obtain ⟨f, RF1, RF2⟩ := HF
  obtain ⟨a, RA1, RA2⟩ := HA
  exact ⟨_, .app RF1 RA1, .app RF2 RA2⟩

private theorem ParallelEtaJoin.proj (_hΓ : OnCtx Γ (env.IsType univs))
    (HM : ParallelEtaJoin Γ m₁ m₂)
    (_h₁ : Γ ⊢ .proj s i m₁ : T) (_h₂ : Γ ⊢ .proj s i m₂ : T) :
    ParallelEtaJoin Γ (.proj s i m₁) (.proj s i m₂) := by
  obtain ⟨m, R1, R2⟩ := HM
  exact ⟨_, .proj R1, .proj R2⟩

private theorem ParallelEtaJoin.lam (hΓ : OnCtx Γ (env.IsType univs)) (_tD : Γ ⊢ D : .sort u)
    (HD : ParallelEtaJoin Γ D₁ D₂) (HB : ParallelEtaJoin (D :: Γ) t₁ t₂)
    (e₁ : Γ ⊢ D ≡ D₁ : .sort u) (e₂ : Γ ⊢ D ≡ D₂ : .sort u)
    (tt₁ : D :: Γ ⊢ t₁ : B₁) (tt₂ : D :: Γ ⊢ t₂ : B₂)
    (_h₁ : Γ ⊢ .lam D₁ t₁ : T₁) (_h₂ : Γ ⊢ .lam D₂ t₂ : T₂) :
    ParallelEtaJoin Γ (.lam D₁ t₁) (.lam D₂ t₂) := by
  obtain ⟨domain, RD1, RD2⟩ := HD
  obtain ⟨body, RB1, RB2⟩ := HB
  exact ⟨_, .lam RD1 (RB1.defeqDFC hΓ (.succ .zero e₁) tt₁),
    .lam RD2 (RB2.defeqDFC hΓ (.succ .zero e₂) tt₂)⟩

private theorem ParallelEtaJoin.forallE (hΓ : OnCtx Γ (env.IsType univs)) (_tD : Γ ⊢ D : .sort u)
    (HD : ParallelEtaJoin Γ D₁ D₂) (HB : ParallelEtaJoin (D :: Γ) t₁ t₂)
    (e₁ : Γ ⊢ D ≡ D₁ : .sort u) (e₂ : Γ ⊢ D ≡ D₂ : .sort u)
    (tt₁ : D :: Γ ⊢ t₁ : B₁) (tt₂ : D :: Γ ⊢ t₂ : B₂)
    (_h₁ : Γ ⊢ .forallE D₁ t₁ : T₁) (_h₂ : Γ ⊢ .forallE D₂ t₂ : T₂) :
    ParallelEtaJoin Γ (.forallE D₁ t₁) (.forallE D₂ t₂) := by
  obtain ⟨domain, RD1, RD2⟩ := HD
  obtain ⟨body, RB1, RB2⟩ := HB
  exact ⟨_, .forallE RD1 (RB1.defeqDFC hΓ (.succ .zero e₁) tt₁),
    .forallE RD2 (RB2.defeqDFC hΓ (.succ .zero e₂) tt₂)⟩

private abbrev EtaDiamondBelow (s : Nat) : Prop :=
  ∀ {Γ a b c A}, sizeOf a < s → OnCtx Γ (env.IsType univs) → EtaPar Γ a b → EtaPar Γ a c →
    Γ ⊢ a : A → ParallelEtaJoin Γ b c

private theorem etaPar_diamond_app (hΓ : OnCtx Γ (env.IsType univs)) (IH : EtaDiamondBelow (sizeOf (VExpr.app f x)))
    (hF : EtaPar Γ f f₁) (hX : EtaPar Γ x x₁) (H2 : EtaPar Γ (.app f x) c)
    (ha : Γ ⊢ .app f x : A) : ParallelEtaJoin Γ (.app f₁ x₁) c := by
  have HB : EtaPar Γ (.app f x) (.app f₁ x₁) := .app hF hX
  generalize hE : VExpr.app f x = E at H2 ha IH HB
  induction H2 generalizing A with
  | app hf₂ hx₂ =>
    cases hE
    obtain ⟨_, _, tf, tx⟩ := ha.app_inv henv hΓ
    exact ParallelEtaJoin.app hΓ (IH (by simp; omega) hΓ hF hf₂ tf) (IH (by simp; omega) hΓ hX hx₂ tx)
      ((EtaPar.full hΓ HB ha).hasType hΓ ha) ((EtaPar.full hΓ (.app hf₂ hx₂) ha).hasType hΓ ha)
  | funEta H₀ HD hty ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.funEta H₀ HD hty) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hty
    have hj := ih hΓ hF hX rfl ha IH HB
    exact (ParallelEtaJoin.fun_left hΓ hj.symm HD hb' hc).symm
  | structEta H₀ hlen hps hl hp hi hs hexp ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.structEta H₀ hlen hps hl hp hi hs hexp) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hs
    have hbexp := (FullReduction.structExpand (EtaPar.full hΓ HB ha)).hasType hΓ hexp
    have hj := ih hΓ hF hX rfl ha IH HB
    exact (ParallelEtaJoin.struct_left hΓ hj.symm hl hp hi hlen hps hb' hbexp hc).symm
  | _ => cases hE

private theorem etaPar_diamond_proj (hΓ : OnCtx Γ (env.IsType univs))
    (IH : EtaDiamondBelow (sizeOf (VExpr.proj s i m)))
    (hM : EtaPar Γ m m₁) (H2 : EtaPar Γ (.proj s i m) c)
    (ha : Γ ⊢ .proj s i m : A) : ParallelEtaJoin Γ (.proj s i m₁) c := by
  have HB : EtaPar Γ (.proj s i m) (.proj s i m₁) := .proj hM
  generalize hE : VExpr.proj s i m = E at H2 ha IH HB
  induction H2 generalizing A with
  | proj hm₂ =>
    cases hE
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
    exact ParallelEtaJoin.proj hΓ (IH (by simp; omega) hΓ hM hm₂ lm.hasType.2)
      ((EtaPar.full hΓ HB ha).hasType hΓ ha) ((EtaPar.full hΓ (.proj hm₂) ha).hasType hΓ ha)
  | funEta H₀ HD hty ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.funEta H₀ HD hty) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hty
    have hj := ih hΓ hM rfl ha IH HB
    exact (ParallelEtaJoin.fun_left hΓ hj.symm HD hb' hc).symm
  | structEta H₀ hlen hps hl hp hi hs hexp ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.structEta H₀ hlen hps hl hp hi hs hexp) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hs
    have hbexp := (FullReduction.structExpand (EtaPar.full hΓ HB ha)).hasType hΓ hexp
    have hj := ih hΓ hM rfl ha IH HB
    exact (ParallelEtaJoin.struct_left hΓ hj.symm hl hp hi hlen hps hb' hbexp hc).symm
  | _ => cases hE

private theorem etaPar_diamond_lam (hΓ : OnCtx Γ (env.IsType univs))
    (IH : EtaDiamondBelow (sizeOf (VExpr.lam D t)))
    (hD : EtaPar Γ D D₁) (ht : EtaPar (D :: Γ) t t₁) (H2 : EtaPar Γ (.lam D t) c)
    (ha : Γ ⊢ .lam D t : A) : ParallelEtaJoin Γ (.lam D₁ t₁) c := by
  have HB : EtaPar Γ (.lam D t) (.lam D₁ t₁) := .lam hD ht
  generalize hE : VExpr.lam D t = E at H2 ha IH HB
  induction H2 generalizing A with
  | lam hD₂ ht₂ =>
    cases hE
    obtain ⟨⟨_, tD⟩, _, tt⟩ := ha.lam_inv henv hΓ
    have hΓ' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, tD⟩
    exact ParallelEtaJoin.lam hΓ tD (IH (by simp; omega) hΓ hD hD₂ tD) (IH (by simp; omega) hΓ' ht ht₂ tt)
      ((EtaPar.full hΓ hD tD).defeq hΓ tD) ((EtaPar.full hΓ hD₂ tD).defeq hΓ tD)
      ((EtaPar.full hΓ' ht tt).hasType hΓ' tt) ((EtaPar.full hΓ' ht₂ tt).hasType hΓ' tt)
      ((EtaPar.full hΓ HB ha).hasType hΓ ha) ((EtaPar.full hΓ (.lam hD₂ ht₂) ha).hasType hΓ ha)
  | funEta H₀ HD hty ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.funEta H₀ HD hty) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hty
    have hj := ih hΓ hD ht rfl ha IH HB
    exact (ParallelEtaJoin.fun_left hΓ hj.symm HD hb' hc).symm
  | structEta H₀ hlen hps hl hp hi hs hexp ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.structEta H₀ hlen hps hl hp hi hs hexp) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hs
    have hbexp := (FullReduction.structExpand (EtaPar.full hΓ HB ha)).hasType hΓ hexp
    have hj := ih hΓ hD ht rfl ha IH HB
    exact (ParallelEtaJoin.struct_left hΓ hj.symm hl hp hi hlen hps hb' hbexp hc).symm
  | _ => cases hE

private theorem etaPar_diamond_forallE (hΓ : OnCtx Γ (env.IsType univs))
    (IH : EtaDiamondBelow (sizeOf (VExpr.forallE D t)))
    (hD : EtaPar Γ D D₁) (ht : EtaPar (D :: Γ) t t₁) (H2 : EtaPar Γ (.forallE D t) c)
    (ha : Γ ⊢ .forallE D t : A) : ParallelEtaJoin Γ (.forallE D₁ t₁) c := by
  have HB : EtaPar Γ (.forallE D t) (.forallE D₁ t₁) := .forallE hD ht
  generalize hE : VExpr.forallE D t = E at H2 ha IH HB
  induction H2 generalizing A with
  | forallE hD₂ ht₂ =>
    cases hE
    obtain ⟨⟨_, tD⟩, _, tt⟩ := ha.forallE_inv henv
    have hΓ' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, tD⟩
    exact ParallelEtaJoin.forallE hΓ tD (IH (by simp; omega) hΓ hD hD₂ tD) (IH (by simp; omega) hΓ' ht ht₂ tt)
      ((EtaPar.full hΓ hD tD).defeq hΓ tD) ((EtaPar.full hΓ hD₂ tD).defeq hΓ tD)
      ((EtaPar.full hΓ' ht tt).hasType hΓ' tt) ((EtaPar.full hΓ' ht₂ tt).hasType hΓ' tt)
      ((EtaPar.full hΓ HB ha).hasType hΓ ha) ((EtaPar.full hΓ (.forallE hD₂ ht₂) ha).hasType hΓ ha)
  | funEta H₀ HD hty ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.funEta H₀ HD hty) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hty
    have hj := ih hΓ hD ht rfl ha IH HB
    exact (ParallelEtaJoin.fun_left hΓ hj.symm HD hb' hc).symm
  | structEta H₀ hlen hps hl hp hi hs hexp ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.structEta H₀ hlen hps hl hp hi hs hexp) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hs
    have hbexp := (FullReduction.structExpand (EtaPar.full hΓ HB ha)).hasType hΓ hexp
    have hj := ih hΓ hD ht rfl ha IH HB
    exact (ParallelEtaJoin.struct_left hΓ hj.symm hl hp hi hlen hps hb' hbexp hc).symm
  | _ => cases hE

private theorem etaPar_diamond_aux : ∀ n, EtaDiamondBelow n := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
  intro Γ a b c A hsz hΓ H H2 ha
  have IH : EtaDiamondBelow (sizeOf a) := fun h => ih (by omega)
  clear ih hsz
  induction H generalizing c A with
  | bvar | sort | const => exact ⟨c, H2, .rfl⟩
  | app hF hX _ _ => exact etaPar_diamond_app hΓ IH hF hX H2 ha
  | proj hM _ => exact etaPar_diamond_proj hΓ IH hM H2 ha
  | lam hD ht _ _ => exact etaPar_diamond_lam hΓ IH hD ht H2 ha
  | forallE hD ht _ _ => exact etaPar_diamond_forallE hΓ IH hD ht H2 ha
  | funEta H₀ HD hty ih =>
    have hb := (EtaPar.full hΓ (.funEta H₀ HD hty) ha).hasType hΓ ha
    have hc := (EtaPar.full hΓ H2 ha).hasType hΓ hty
    exact ParallelEtaJoin.fun_left hΓ (ih hΓ H2 ha IH) HD hc hb
  | structEta H₀ hlen hps hl hp hi hs hexp ih =>
    have hb := (EtaPar.full hΓ (.structEta H₀ hlen hps hl hp hi hs hexp) ha).hasType hΓ ha
    have hc := (EtaPar.full hΓ H2 ha).hasType hΓ hs
    have hcexp := (FullReduction.structExpand (EtaPar.full hΓ H2 ha)).hasType hΓ hexp
    exact ParallelEtaJoin.struct_left hΓ (ih hΓ H2 ha IH) hl hp hi hlen hps hc hcexp hb


/-- Parallel eta has an exact typed diamond. Both outgoing paths consist of a
single parallel eta step; no canonical Eq, front, or computation is used. -/
theorem etaPar_diamond (hΓ : OnCtx Γ (env.IsType univs))
    (R1 : EtaPar Γ a b) (R2 : EtaPar Γ a c) (ht : env.HasType univs Γ a T) :
    ParallelEtaJoin Γ b c :=
  etaPar_diamond_aux _ (Nat.lt_succ_self _) hΓ R1 R2 ht

end Lean4Lean.VEnv.Strengthening.PureObservation
