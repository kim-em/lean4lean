import Lean4Lean.Theory.Typing.Strengthening.SeparatedParallelSpines
import Lean4Lean.Theory.Typing.Strengthening.ExactPrefixCoreDiamond

/-! # Exact prefix commutation with stored and selected structure computation

Separated ordinary roots exclude a delta equation at the same head. The actual
prefix guards exclude both those ordinary roots and selected structure delta.
The remaining parallel overlaps join by smaller-source induction, including
both presentations of constructor projection.
-/
namespace Lean4Lean.VEnv
open _root_.Lean4Lean VExpr Params Strengthening Strengthening.PureObservation
variable [Params]
private abbrev actualD : Definitions :=
  RegisteredStructure.definitions (Definitions.ofEnv env univs henv)

private theorem actual_sound : actualD.Sound env univs :=
  RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A

private abbrev SeparatedDPBelow (s : Nat) : Prop :=
  ∀ {Γ a b c A}, sizeOf a < s → OnCtx Γ (env.IsType univs) →
    DeltaPar Γ a b → SeparatedPar actualD a c → Γ ⊢ a : A →
    ∃ d, SeparatedPar actualD b d ∧ DeltaPar Γ c d

private theorem separated_dp_args {a : VExpr} (hΓ : OnCtx Γ (env.IsType univs))
    (IH : SeparatedDPBelow (sizeOf a)) (hsub : ∀ x ∈ args, sizeOf x < sizeOf a)
    (htyped : ∀ x ∈ args, ∃ T, Γ ⊢ x : T)
    (h1 : List.Forall₂ (DeltaPar Γ) args args') (h2 : List.Forall₂ (SeparatedPar actualD) args argsP) :
    ∃ ds, List.Forall₂ (SeparatedPar actualD) args' ds ∧ List.Forall₂ (DeltaPar Γ) argsP ds := by
  induction h1 generalizing argsP with
  | nil => cases h2; exact ⟨[], .nil, .nil⟩
  | cons hd _ ih =>
    cases h2 with
    | cons hp hps =>
      obtain ⟨d, pd, dd⟩ := IH (hsub _ (List.mem_cons_self ..)) hΓ hd hp
        (htyped _ (List.mem_cons_self ..)).choose_spec
      obtain ⟨ds, ps, ds'⟩ := ih
        (fun _ hx => hsub _ (List.mem_cons_of_mem _ hx))
        (fun _ hx => htyped _ (List.mem_cons_of_mem _ hx)) hps
      exact ⟨d :: ds, .cons pd ps, .cons dd ds'⟩

private theorem separated_dp_iota
    {r : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).RHS ×
      (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Check}
    (hΓ : OnCtx Γ (env.IsType univs)) (IH : SeparatedDPBelow (sizeOf e))
    (hp : Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hm : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Matches e m1 m2)
    (hc : CheckFromTyping env univs _ r m1)
    (hn : ∀ rhs, ¬ actualD.unfolds
      (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).headConst m1 rhs) (hargs : ∀ v, SeparatedPar actualD (m2 v) (m2' v))
    (H : DeltaPar Γ e b) (ha : Γ ⊢ e : A) :
    ∃ d, SeparatedPar actualD b d ∧ DeltaPar Γ (r.1.apply m1 m2') d := by
  classical
  have hck := hc hΓ hm ha
  have hm₀ := hm
  obtain ⟨F, M, lsc, g1, g2, hF, hM, rfl, rfl⟩ :
      ∃ F M lsc g1 g2, ((Pattern.const rc).varN mr).Matches F m1 g1 ∧
        ((Pattern.const cc).varN kc).Matches M lsc g2 ∧ e = .app F M ∧ m2 = Sum.elim g1 g2 := by
    cases hm with | app hF hM => exact ⟨_, _, _, _, _, hF, hM, rfl, rfl⟩
  obtain ⟨vsF, rfl⟩ : ∃ vs, F = VExpr.mkApps (.const rc m1) vs := ⟨_, hF.const_arguments⟩
  obtain ⟨fsM, rfl⟩ : ∃ fs, M = VExpr.mkApps (.const cc lsc) fs := ⟨_, hM.const_arguments⟩
  rw [← VExpr.mkApps_snoc] at H
  obtain ⟨args', rfl, hargs'⟩ := DeltaPar.const_spine_of (vsF ++ [_]).length
    (fun _ hr => Params.iota_no_delta hp hck hr)
    (fun _ hq hr => by subst hq; exact Params.iota_no_quotDelta hp hck hr) (Nat.le_refl _) H
  obtain ⟨vs', M', rfl, hvs', hM'⟩ := List.forall₂_snoc_left hargs'
  obtain ⟨fs', rfl, hfs'⟩ := DeltaPar.rigid_spine (pat_ctor_rigid hp) hM'
  obtain ⟨m3₁, hm3₁, hr₁⟩ := Pattern.Matches.constVarN_transport (R := fun x y => DeltaPar Γ y x)
    mr hF (Lean4Lean.List.Forall₂.flip hvs') (ls' := m1)
  obtain ⟨m3₂, hm3₂, hr₂⟩ := Pattern.Matches.constVarN_transport (R := fun x y => DeltaPar Γ y x)
    kc hM (Lean4Lean.List.Forall₂.flip hfs') (ls' := lsc)
  have hm₃ := Pattern.Matches.app hm3₁ hm3₂
  have hrel : ∀ v, DeltaPar Γ (Sum.elim g1 g2 v) (Sum.elim m3₁ m3₂ v) := by
    intro v; cases v with
    | inl v => exact hr₁ v
    | inr v => exact hr₂ v
  have htv : ∀ v, ∃ T, Γ ⊢ Sum.elim g1 g2 v : T := fun v => hm₀.hasType hΓ ha v
  have hj v := IH (hm₀.sizeOf_lt v) hΓ (hrel v) (hargs v) (htv v).choose_spec
  let common := fun v => (hj v).choose
  have pD : ∀ v, SeparatedPar actualD (Sum.elim m3₁ m3₂ v) (common v) := fun v => (hj v).choose_spec.1
  have dD : ∀ v, DeltaPar Γ (m2' v) (common v) := fun v => (hj v).choose_spec.2
  exact ⟨_, by rw [VExpr.mkApps_snoc]; exact .pattern hp hm₃ hc hn pD,
    DeltaPar.congrRel.apply_rhs r.1 dD⟩

private theorem separated_dp_projection (hΓ : OnCtx Γ (env.IsType univs))
    (IH : SeparatedDPBelow (sizeOf (VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args))))
    (hlen : args.length = args'.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i])
    (hl : env.projections family info)
    (hs : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args') : fieldType)
    (hi : args'[info.nparams + index]? = some field) (ht : Γ ⊢ field : fieldType)
    (H2 : SeparatedPar actualD (.proj family index (VExpr.mkApps (.const info.ctorName ls) args)) c)
    (ha : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args) : A) :
    ∃ d, SeparatedPar actualD field d ∧ DeltaPar Γ c d := by
  have hb := (DeltaPar.full (.projIota hlen hargs hl hs hi ht)).hasType hΓ ha
  have hc := (H2.simAt actual_sound hΓ _ ha).hasType.2
  generalize he : VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args) = source at H2
  cases H2 with
  | proj hM =>
    cases he
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨argsP, rfl, hP⟩ := hM.rigid_spine_paths (projection_ctor_rigid hl)
      (fun _ _ => RegisteredStructure.definitions_ofEnv_no_rigid (projection_ctor_rigid hl))
    obtain ⟨ds, pD, dD⟩ := separated_dp_args hΓ IH
      (fun _ hx => by have := sizeOf_mkApps_arg (f := .const info.ctorName ls) hx; simp; omega)
      (HasType.mkApps_args_typed hΓ lm.hasType.2) (List.forall₂_of_getElem hlen hargs) hP
    obtain ⟨d, hd, pd⟩ := forall₂_getElem?_left pD hi
    have hcong : DeltaPar Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls) argsP))
        (.proj family index (VExpr.mkApps (.const info.ctorName ls) ds)) :=
      .proj (DeltaPar.mkApps_args dD)
    have hT := (DeltaPar.full hcong).hasType hΓ hc
    have ⟨hl₂, hx₂⟩ := getElem_of_forall₂ dD
    exact ⟨d, pd, .projIota hl₂ hx₂ hl hT hd ((pd.simAt actual_sound hΓ _ hb).hasType.2)⟩
  | projIota hl' hn' hi' hF =>
    obtain ⟨hfamily, hindex, hmajor⟩ := VExpr.proj.inj he
    cases hfamily
    cases hindex
    cases henv.ordered.projections_unique hl hl'
    obtain ⟨_, rfl, rfl⟩ := mkApps_const_inj hmajor
    have HA := List.forall₂_of_getElem hlen hargs
    obtain ⟨field0, hi0, hD⟩ := forall₂_getElem?_right HA hi
    cases Option.some.inj (hi0.symm.trans hi')
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
    exact IH (by
      have h := sizeOf_mkApps_arg (f := .const info.ctorName ls) (List.mem_of_getElem? hi0)
      simp; omega) hΓ hD hF
      (HasType.mkApps_args_typed hΓ lm.hasType.2 _ (List.mem_of_getElem? hi0)).choose_spec
  | pattern _ hm => rw [← he] at hm; cases hm
  | bvar | sort | const | delta | app | lam | forallE | beta => cases he

private theorem separated_dp_diamond_aux : ∀ n, SeparatedDPBelow n := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
  intro Γ a b c A hsz hΓ H H2 ha
  have IH : SeparatedDPBelow (sizeOf a) := fun h => ih (by omega)
  cases H with
  | bvar | sort | const => exact ⟨c, H2, .rfl⟩
  | @app _ f f' x x' hF hX =>
    cases H2 with
    | app hf hx =>
      obtain ⟨_, _, lf, lx⟩ := ha.app_inv henv hΓ
      obtain ⟨F, pF, dF⟩ := IH (by simp; omega) hΓ hF hf lf
      obtain ⟨X, pX, dX⟩ := IH (by simp; omega) hΓ hX hx lx
      exact ⟨_, .app pF pX, .app dF dX⟩
    | beta ht hu =>
      obtain ⟨_, _, lf, lx⟩ := ha.app_inv henv hΓ
      have ⟨⟨_, lD⟩, _, lt⟩ := lf.lam_inv henv hΓ
      have ⟨⟨_, hw⟩, _⟩ := (lf.uniqU henv hΓ (HasType.lam lD lt)).forallE_inv henv hΓ
      have lx' := hw.defeq lx
      obtain ⟨D', t', hD, ht', rfl⟩ := DeltaPar.lam_inv hF
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, lD⟩
      obtain ⟨T, pT, dT⟩ := IH (by simp; omega) hΓ' ht' ht lt
      obtain ⟨U, pU, dU⟩ := IH (by simp; omega) hΓ hX hu lx'
      exact ⟨T.inst U, .beta pT pU,
        DeltaPar.instN .zero hΓ' dU ((hu.simAt actual_sound hΓ _ lx').hasType.2) dT ((ht.simAt actual_sound hΓ' _ lt).hasType.2)⟩
    | pattern hp hm hc hn hargs =>
      obtain ⟨sp, rfl⟩ := Params.pat_simple hp
      cases sp with
      | defn => cases hm
      | iota rc mr cc kc => exact separated_dp_iota hΓ IH hp hm hc hn hargs (.app hF hX) ha
  | @delta _ name ls rhs args args' hlen hargs hr =>
    obtain ⟨data, hdata, hle⟩ := hr.length_le
    have hle' : args.length ≤ data.majorOffset := hlen ▸ hle
    obtain ⟨argsP, rfl, hP⟩ := SeparatedPar.const_spine_of H2 (singleton_no_registered_definition hr)
      (fun hp hpre hm => Params.no_match_delta_prefix hdata hp (by omega) hm) (Nat.le_refl _)
    obtain ⟨ds, pD, dD⟩ := separated_dp_args hΓ IH
      (fun _ hx => sizeOf_mkApps_arg hx) (HasType.mkApps_args_typed hΓ ha)
      (List.forall₂_of_getElem hlen hargs) hP
    obtain ⟨rhs', hr', pR⟩ := singleton_prefix_congr separatedPar_congrRel
      (separatedPar_congrRel.argRel (fun hΓ R ht => R.simAt actual_sound hΓ _ ht)) hΓ hr pD
    have ⟨hl, hx⟩ := getElem_of_forall₂ dD
    exact ⟨rhs', pR, .delta hl hx hr'⟩
  | @quotDelta _ ls rhs args args' hlen hargs hr =>
    have hle : args.length ≤ 5 := hlen ▸ hr.length_le
    obtain ⟨argsP, rfl, hP⟩ := SeparatedPar.const_spine_of H2 (quotient_no_registered_definition hr)
      (fun hp hpre hm => Params.no_match_quot_prefix hr.registered hp (by omega) hm) (Nat.le_refl _)
    obtain ⟨ds, pD, dD⟩ := separated_dp_args hΓ IH
      (fun _ hx => sizeOf_mkApps_arg hx) (HasType.mkApps_args_typed hΓ ha)
      (List.forall₂_of_getElem hlen hargs) hP
    obtain ⟨rhs', hr', pR⟩ := quotient_prefix_congr separatedPar_congrRel
      (separatedPar_congrRel.argRel (fun hΓ R ht => R.simAt actual_sound hΓ _ ht)) hΓ hr pD
    have ⟨hl, hx⟩ := getElem_of_forall₂ dD
    exact ⟨rhs', pR, .quotDelta hl hx hr'⟩
  | projIota hlen hargs hl hs hi ht =>
    exact separated_dp_projection hΓ IH hlen hargs hl hs hi ht H2 ha
  | proj hM =>
    cases H2 with
    | proj hm =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
      obtain ⟨M, pM, dM⟩ := IH (by simp; omega) hΓ hM hm lm.hasType.2
      exact ⟨_, .proj pM, .proj dM⟩
    | projIota hl hn hi hF =>
      rename_i info args field ls
      obtain ⟨args', rfl, HA⟩ := hM.rigid_spine (projection_ctor_rigid hl)
      obtain ⟨field', hi', hD⟩ := forall₂_getElem?_left HA hi
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
      obtain ⟨d, pD, dD⟩ := IH (by
        have h := sizeOf_mkApps_arg (f := .const info.ctorName ls) (List.mem_of_getElem? hi)
        simp; omega) hΓ hD hF
        (HasType.mkApps_args_typed hΓ lm.hasType.2 _ (List.mem_of_getElem? hi)).choose_spec
      exact ⟨d, .projIota hl (HA.length_eq.symm.trans hn) hi' pD, dD⟩
    | pattern _ hm => cases hm
  | lam hD hT =>
    cases H2 with
    | lam hD₂ hT₂ =>
      obtain ⟨⟨_, lD⟩, _, lt⟩ := ha.lam_inv henv hΓ
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, lD⟩
      obtain ⟨E, pE, dE⟩ := IH (by simp; omega) hΓ hD hD₂ lD
      obtain ⟨T, pT, dT⟩ := IH (by simp; omega) hΓ' hT hT₂ lt
      have hDD₂ := hD₂.simAt actual_sound hΓ _ lD
      exact ⟨_, .lam pE pT,
        .lam dE (dT.defeqDFC hΓ (.succ .zero hDD₂) ((hT₂.simAt actual_sound hΓ' _ lt).hasType.2))⟩
    | pattern _ hm => cases hm
  | forallE hD hT =>
    cases H2 with
    | forallE hD₂ hT₂ =>
      obtain ⟨⟨_, lD⟩, _, lt⟩ := ha.forallE_inv henv
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, lD⟩
      obtain ⟨E, pE, dE⟩ := IH (by simp; omega) hΓ hD hD₂ lD
      obtain ⟨T, pT, dT⟩ := IH (by simp; omega) hΓ' hT hT₂ lt
      have hDD₂ := hD₂.simAt actual_sound hΓ _ lD
      exact ⟨_, .forallE pE pT,
        .forallE dE (dT.defeqDFC hΓ (.succ .zero hDD₂) ((hT₂.simAt actual_sound hΓ' _ lt).hasType.2))⟩
    | pattern _ hm => cases hm

/-- Actual singleton/quotient prefixes and constructor projection commute with
parallel computation using all stored and selected closed structure equations.
The endpoint is literal, with no normal-comparison or strengthening premise. -/
theorem DeltaPar.separated_diamond_exact (hΓ : OnCtx Γ (env.IsType univs))
    (H : DeltaPar Γ a b)
    (H2 : SeparatedPar (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) a c)
    (ha : Γ ⊢ a : A) :
    ∃ d, SeparatedPar (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) b d ∧
      DeltaPar Γ c d :=
  separated_dp_diamond_aux _ (Nat.lt_succ_self _) hΓ H H2 ha

end Lean4Lean.VEnv
