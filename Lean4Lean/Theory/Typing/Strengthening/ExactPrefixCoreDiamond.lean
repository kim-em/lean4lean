import Lean4Lean.Theory.Typing.Strengthening.PrefixProgramCongruence

/-! # Exact commutation of prefix/projection and core parallel reduction

Full generated-program congruence removes the normal-comparison remainder of
the existing DeltaPar/ParRed diamond. Typed smaller-source joins now give one
literal common endpoint, including at proof types and dependent lambda domains.
-/
namespace Lean4Lean.VEnv
open VExpr Params Strengthening.PureObservation
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A

private abbrev ExactDPBelow (s : Nat) : Prop :=
  ∀ {Γ a b c A}, sizeOf a < s → OnCtx Γ (env.IsType univs) →
    DeltaPar Γ a b → ParRed Γ a c → Γ ⊢ a : A →
    ∃ d, ParRed Γ b d ∧ DeltaPar Γ c d

private theorem exact_dp_args {a : VExpr} (hΓ : OnCtx Γ (env.IsType univs))
    (IH : ExactDPBelow (sizeOf a)) (hsub : ∀ x ∈ args, sizeOf x < sizeOf a)
    (htyped : ∀ x ∈ args, ∃ T, Γ ⊢ x : T)
    (h1 : List.Forall₂ (DeltaPar Γ) args args') (h2 : List.Forall₂ (ParRed Γ) args argsP) :
    ∃ ds, List.Forall₂ (ParRed Γ) args' ds ∧ List.Forall₂ (DeltaPar Γ) argsP ds := by
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

private theorem exact_dp_iota
    {r : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).RHS ×
      (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Check}
    (hΓ : OnCtx Γ (env.IsType univs)) (IH : ExactDPBelow (sizeOf e))
    (hp : Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hm : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Matches e m1 m2)
    (hck : r.2.OK (IsDefEqU env univs Γ) m1 m2) (hargs : ∀ v, ParRed Γ (m2 v) (m2' v))
    (H : DeltaPar Γ e b) (ha : Γ ⊢ e : A) :
    ∃ d, ParRed Γ b d ∧ DeltaPar Γ (r.1.apply m1 m2') d := by
  classical
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
  have pD : ∀ v, ParRed Γ (Sum.elim m3₁ m3₂ v) (common v) := fun v => (hj v).choose_spec.1
  have dD : ∀ v, DeltaPar Γ (m2' v) (common v) := fun v => (hj v).choose_spec.2
  have hck₃ := Pattern.Check.OK.defeq_values hΓ
    (p := Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
    (m' := Sum.elim m3₁ m3₂)
    (fun v => ⟨_, (DeltaPar.full (hrel v)).defeq hΓ (htv v).choose_spec⟩) hck
  exact ⟨_, by rw [VExpr.mkApps_snoc]; exact ParRed.extra hp hm₃ hck₃ pD,
    DeltaPar.congrRel.apply_rhs r.1 dD⟩

private theorem exact_dp_projection (hΓ : OnCtx Γ (env.IsType univs))
    (IH : ExactDPBelow (sizeOf (VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args))))
    (hlen : args.length = args'.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i])
    (hl : env.projections family info)
    (hs : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args') : fieldType)
    (hi : args'[info.nparams + index]? = some field) (ht : Γ ⊢ field : fieldType)
    (H2 : ParRed Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls) args)) c)
    (ha : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args) : A) :
    ∃ d, ParRed Γ field d ∧ DeltaPar Γ c d := by
  have hb := (DeltaPar.full (.projIota hlen hargs hl hs hi ht)).hasType hΓ ha
  have hc := H2.hasType hΓ ha
  cases H2 with
  | proj hM =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨argsP, rfl, hP⟩ := ParRed.rigid_const_spine (projection_ctor_rigid hl) hM
    obtain ⟨ds, pD, dD⟩ := exact_dp_args hΓ IH
      (fun _ hx => by have := sizeOf_mkApps_arg (f := .const info.ctorName ls) hx; simp; omega)
      (HasType.mkApps_args_typed hΓ lm.hasType.2) (List.forall₂_of_getElem hlen hargs) hP
    obtain ⟨d, hd, pd⟩ := forall₂_getElem?_left pD hi
    have hcong : DeltaPar Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls) argsP))
        (.proj family index (VExpr.mkApps (.const info.ctorName ls) ds)) :=
      .proj (DeltaPar.mkApps_args dD)
    have hT := (DeltaPar.full hcong).hasType hΓ hc
    have ⟨hl₂, hx₂⟩ := getElem_of_forall₂ dD
    exact ⟨d, pd, .projIota hl₂ hx₂ hl hT hd (pd.hasType hΓ hb)⟩
  | extra _ hm => cases hm

private theorem exact_dp_diamond_aux : ∀ n, ExactDPBelow n := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
  intro Γ a b c A hsz hΓ H H2 ha
  have IH : ExactDPBelow (sizeOf a) := fun h => ih (by omega)
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
      have hDD := (DeltaPar.full hD).defeq hΓ lD
      have tt' := (DeltaPar.full ht').hasType hΓ' lt
      exact ⟨T.inst U, .beta (pT.defeqDFC hΓ (.succ .zero hDD) tt') pU,
        DeltaPar.instN .zero hΓ' dU (hu.hasType hΓ lx') dT (ht.hasType hΓ' lt)⟩
    | extra hp hm hck hargs =>
      obtain ⟨sp, rfl⟩ := Params.pat_simple hp
      cases sp with
      | defn => cases hm
      | iota rc mr cc kc => exact exact_dp_iota hΓ IH hp hm hck hargs (.app hF hX) ha
  | @delta _ name ls rhs args args' hlen hargs hr =>
    obtain ⟨data, hdata, hle⟩ := hr.length_le
    have hle' : args.length ≤ data.majorOffset := hlen ▸ hle
    obtain ⟨argsP, rfl, hP⟩ := ParRed.const_spine_of args.length
      (fun hp hpre hm => Params.no_match_delta_prefix hdata hp (by omega) hm) (Nat.le_refl _) H2
    obtain ⟨ds, pD, dD⟩ := exact_dp_args hΓ IH
      (fun _ hx => sizeOf_mkApps_arg hx) (HasType.mkApps_args_typed hΓ ha)
      (List.forall₂_of_getElem hlen hargs) hP
    obtain ⟨rhs', hr', pR⟩ := singleton_prefix_congr ParRed.congrRel ParRed.argRel hΓ hr pD
    have ⟨hl, hx⟩ := getElem_of_forall₂ dD
    exact ⟨rhs', pR, .delta hl hx hr'⟩
  | @quotDelta _ ls rhs args args' hlen hargs hr =>
    have hle : args.length ≤ 5 := hlen ▸ hr.length_le
    obtain ⟨argsP, rfl, hP⟩ := ParRed.const_spine_of args.length
      (fun hp hpre hm => Params.no_match_quot_prefix hr.registered hp (by omega) hm) (Nat.le_refl _) H2
    obtain ⟨ds, pD, dD⟩ := exact_dp_args hΓ IH
      (fun _ hx => sizeOf_mkApps_arg hx) (HasType.mkApps_args_typed hΓ ha)
      (List.forall₂_of_getElem hlen hargs) hP
    obtain ⟨rhs', hr', pR⟩ := quotient_prefix_congr ParRed.congrRel ParRed.argRel hΓ hr pD
    have ⟨hl, hx⟩ := getElem_of_forall₂ dD
    exact ⟨rhs', pR, .quotDelta hl hx hr'⟩
  | projIota hlen hargs hl hs hi ht =>
    exact exact_dp_projection hΓ IH hlen hargs hl hs hi ht H2 ha
  | proj hM =>
    cases H2 with
    | proj hm =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
      obtain ⟨M, pM, dM⟩ := IH (by simp; omega) hΓ hM hm lm.hasType.2
      exact ⟨_, .proj pM, .proj dM⟩
    | extra _ hm => cases hm
  | lam hD hT =>
    cases H2 with
    | lam hD₂ hT₂ =>
      obtain ⟨⟨_, lD⟩, _, lt⟩ := ha.lam_inv henv hΓ
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, lD⟩
      obtain ⟨E, pE, dE⟩ := IH (by simp; omega) hΓ hD hD₂ lD
      obtain ⟨T, pT, dT⟩ := IH (by simp; omega) hΓ' hT hT₂ lt
      have hDD' := (DeltaPar.full hD).defeq hΓ lD
      have hDD₂ := hD₂.defeq hΓ lD
      exact ⟨_, .lam pE (pT.defeqDFC hΓ (.succ .zero hDD') ((DeltaPar.full hT).hasType hΓ' lt)),
        .lam dE (dT.defeqDFC hΓ (.succ .zero hDD₂) (hT₂.hasType hΓ' lt))⟩
    | extra _ hm => cases hm
  | forallE hD hT =>
    cases H2 with
    | forallE hD₂ hT₂ =>
      obtain ⟨⟨_, lD⟩, _, lt⟩ := ha.forallE_inv henv
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, lD⟩
      obtain ⟨E, pE, dE⟩ := IH (by simp; omega) hΓ hD hD₂ lD
      obtain ⟨T, pT, dT⟩ := IH (by simp; omega) hΓ' hT hT₂ lt
      have hDD' := (DeltaPar.full hD).defeq hΓ lD
      have hDD₂ := hD₂.defeq hΓ lD
      exact ⟨_, .forallE pE (pT.defeqDFC hΓ (.succ .zero hDD') ((DeltaPar.full hT).hasType hΓ' lt)),
        .forallE dE (dT.defeqDFC hΓ (.succ .zero hDD₂) (hT₂.hasType hΓ' lt))⟩
    | extra _ hm => cases hm

/-- Actual singleton/quotient/projection parallel reduction commutes exactly
with core parallel reduction from every typed source. No normal comparison,
proof-irrelevance quotient, canonical Eq or strengthening front is needed. -/
theorem DeltaPar.parRed_diamond_exact (hΓ : OnCtx Γ (env.IsType univs))
    (H : DeltaPar Γ a b) (H2 : ParRed Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, ParRed Γ b d ∧ DeltaPar Γ c d :=
  exact_dp_diamond_aux _ (Nat.lt_succ_self _) hΓ H H2 ha

/-- One prefix/projection parallel step commutes with an entire core path,
retaining a single residual prefix/projection parallel step. -/
theorem DeltaPar.parRedS_diamond_exact (hΓ : OnCtx Γ (env.IsType univs))
    (H : DeltaPar Γ a b) (H2 : ParRedS Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, ParRedS Γ b d ∧ DeltaPar Γ c d := by
  induction H2 with
  | rfl => exact ⟨b, .rfl, H⟩
  | tail HP P ih =>
    obtain ⟨middle, HB, HD⟩ := ih
    obtain ⟨d, PB, DD⟩ := HD.parRed_diamond_exact hΓ P (ParRedS.hasType hΓ HP ha)
    exact ⟨d, HB.tail PB, DD⟩

/-- Finite actual-prefix/projection paths preserve every source type. -/
theorem DeltaPar.star_hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (DeltaPar Γ) a b) (ha : Γ ⊢ a : A) : Γ ⊢ b : A := by
  induction H with
  | rfl => exact ha
  | tail _ H ih => exact H.full.hasType hΓ ih

/-- Finite actual-prefix/projection paths and finite core paths commute
exactly. This is a mixed-path theorem, not confluence of two prefix paths. -/
theorem DeltaPar.star_parRedS_commute_exact (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (DeltaPar Γ) a b) (H2 : ParRedS Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, ParRedS Γ b d ∧ ReflTransGen (DeltaPar Γ) c d := by
  induction H with
  | rfl => exact ⟨c, H2, .rfl⟩
  | tail HD D ih =>
    obtain ⟨middle, HP, HC⟩ := ih
    obtain ⟨d, PB, DD⟩ := D.parRedS_diamond_exact hΓ HP (DeltaPar.star_hasType hΓ HD ha)
    exact ⟨d, PB, HC.tail DD⟩

end Lean4Lean.VEnv
