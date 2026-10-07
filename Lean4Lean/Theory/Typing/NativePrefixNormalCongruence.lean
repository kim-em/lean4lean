import Lean4Lean.Theory.Typing.NativePrefixLayout
import Lean4Lean.Theory.Typing.NormalSubstitution
import Lean4Lean.Theory.Typing.NativePrefixAbstraction
import Lean4Lean.Theory.Typing.NativeRuleRegistration

namespace Lean4Lean.VEnv
open VExpr Params InductiveSignature InductiveSignature.NativeRecursorData
variable [Params]

omit [Params] in
private theorem normal_append {R : α → β → Prop} (H : List.Forall₂ R a b)
    (H' : List.Forall₂ R a' b') : List.Forall₂ R (a ++ a') (b ++ b') := by
  induction H with
  | nil => exact H'
  | cons h hs ih => exact .cons h ih

omit [Params] in
private theorem normal_take {R : α → β → Prop} (H : List.Forall₂ R a b) (n : Nat) :
    List.Forall₂ R (a.take n) (b.take n) := by
  induction H generalizing n with
  | nil => simp
  | cons h hs ih => cases n with
    | zero => exact .nil
    | succ n => exact .cons h (ih n)

omit [Params] in
private theorem normal_drop {R : α → β → Prop} (H : List.Forall₂ R a b) (n : Nat) :
    List.Forall₂ R (a.drop n) (b.drop n) := by
  induction H generalizing n with
  | nil => simp
  | cons h hs ih => cases n with
    | zero => exact .cons h hs
    | succ n => exact ih n

private theorem normal_vars (hn : n ≤ Γ.length) : List.Forall₂ (NormalEqF η Γ) (vars n 0) (vars n 0) := by
  apply Lean4Lean.List.Forall₂.rfl
  intro e he
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact .refl (.bvar (Lookup.ofLt (by omega)).2)

theorem NativePrefixReplay.normal_components {data : NativeRecursorData}
    {levels : List VLevel} (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativePrefixReplay env univs Γ (mkApps (.const data.name levels) args) program)
    (hg : data.prefixProgram univs levels args = some program)
    (hg' : data.prefixProgram univs levels args' = some program')
    (ha : List.Forall₂ (NormalEqF η Γ) args args') :
    List.Forall₂ (NormalEqF η (program.domains.reverse ++ Γ)) program.captures program'.captures ∧
      NormalEqF η (program.domains.reverse ++ Γ) program.constructor program'.constructor := by
  obtain ⟨source, fields, hsource, hfields, hlen, hctor, hcapture⟩ := prefixProgram_layout hg
  obtain ⟨source', fields', hsource', hfields', hlen', hctor', hcapture'⟩ := prefixProgram_layout hg'
  have he := Option.some.inj (hsource.symm.trans hsource')
  subst source'
  have he := Option.some.inj (hfields.symm.trans hfields')
  subst fields'
  have halen := Lean4Lean.List.Forall₂.length_eq ha
  have hn : 0 < program.domains.length := List.length_pos_iff.mpr H.remaining_nonempty
  have hctx := (IsType.wrapForalls_inv henv hΓ (H.source_typed.isType henv hΓ)).1
  have W : Ctx.LiftN (data.majorOffset + 1 - args.length) 0 Γ (program.domains.reverse ++ Γ) :=
    .zero _ (by simpa only [List.length_reverse] using hlen)
  have hall : List.Forall₂ (NormalEqF η (program.domains.reverse ++ Γ))
      (data.prefixArguments args) (data.prefixArguments args') := by
    unfold prefixArguments
    rw [← halen]
    apply normal_append
    · apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact Lean4Lean.List.Forall₂.imp (fun _ _ h => h.weakN W) ha
    · exact normal_vars (by simp only [List.length_append, List.length_reverse]; omega)
  have hprojection : List.Forall₂ (NormalEqF η (program.domains.reverse ++ Γ))
      (data.prefixProjectionArguments args) (data.prefixProjectionArguments args') :=
    normal_append (normal_append (normal_take hall _) (normal_take (normal_drop hall _) _))
      (.cons (.refl (.bvar (Lookup.ofLt (by simp only [List.length_append, List.length_reverse]; omega)).2)) .nil)
  have hfieldApplications : List.Forall₂ (NormalEqF η (program.domains.reverse ++ Γ))
      (fields.map (fun field => mkApps field.value (data.prefixProjectionArguments args)))
      (fields.map (fun field => mkApps field.value (data.prefixProjectionArguments args'))) := by
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply Lean4Lean.List.Forall₂.rfl
    intro field hfield
    have hmem : mkApps field.value (data.prefixProjectionArguments args) ∈ program.captures := by
      rw [hcapture]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨field, hfield, rfl⟩)
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hmem
    have ht := H.captures_typed i hi (by rw [← H.captures_length]; exact hi)
    rw [he] at ht
    obtain ⟨_, hfn⟩ := VExpr.WF.of_mkApps henv.ordered hctx (show VExpr.WF env univs _ _ from ⟨_, ht⟩)
    exact NormalEqF.mkApps_spine hctx (.refl hfn) hprojection ht
  constructor
  · rw [hcapture, hcapture']
    exact normal_append (normal_take hall _) hfieldApplications
  · obtain ⟨proposition, hp, hm, hc⟩ := H.major_prop
    rw [hctor] at hc
    rw [hctor, hctor']
    exact NormalEqF.instantiateParams_args hctx (normal_append (normal_take hall _) hfieldApplications) hc


omit [Params] in
theorem nativeEtaBody_spine (n : Nat) (fn : VExpr) :
    nativeEtaBody n fn = mkApps (fn.liftN n) (vars n 0) := by
  induction n generalizing fn with
  | zero => simp [nativeEtaBody, vars, mkApps, liftN_zero]
  | succ n ih =>
    rw [nativeEtaBody, ih]
    have hv : vars (n+1) 0 = .bvar n :: vars n 0 := by
      simp only [vars, List.range_succ, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.map_cons, Nat.zero_add]
    rw [hv]
    simp only [lift, liftN, liftN_liftN, Nat.zero_add, Nat.add_comm 1]
    rfl

private theorem native_arguments_wf (hΓ : OnCtx Γ (env.IsType univs))
    (H : VExpr.WF env univs Γ (mkApps fn args)) :
    ∀ arg ∈ args, VExpr.WF env univs Γ arg := by
  induction args generalizing fn with
  | nil => simp
  | cons a args ih =>
    have hf := VExpr.WF.of_mkApps (f := fn.app a) (args := args) henv.ordered hΓ H
    obtain ⟨_, _, _, ha⟩ := hf.app_inv henv.ordered hΓ
    intro arg hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, ha⟩
    · exact ih H arg hm

omit [Params] in
theorem NativeSpineMatch.symm {env : VEnv} (H : NativeSpineMatch env U Γ actual expected) :
    NativeSpineMatch env U Γ expected actual := by
  obtain ⟨n, ls, ls', a, a', ha, ha', hw, hw', he, hs⟩ := H
  exact ⟨n, ls', ls, a', a, ha', ha, hw', hw,
    Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip he),
    Lean4Lean.List.Forall₂.imp (fun _ _ h => IsDefEqU.symm h) (Lean4Lean.List.Forall₂.flip hs)⟩

theorem NativeSpineMatch.trans (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativeSpineMatch env univs Γ a b)
    (H' : NativeSpineMatch env univs Γ b c) : NativeSpineMatch env univs Γ a c := by
  obtain ⟨n, ls, ls', as, bs, ha, hb, hw, hw', he, hs⟩ := H
  obtain ⟨n', ls₁, ls₂, bs', cs, hb', hc, hw₁, hw₂, he', hs'⟩ := H'
  have hh := congrArg VExpr.getAppFnArgs (hb.symm.trans hb')
  rw [spine_mkApps_exact _ _ rfl, spine_mkApps_exact _ _ rfl] at hh
  have ⟨hh, hargs⟩ := Prod.mk.inj hh
  cases hh
  subst bs'
  exact ⟨n, ls, ls₂, as, cs, ha, hc, hw, hw₂,
    Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ h h' => h.trans h') he he',
    Lean4Lean.List.Forall₂.trans (T := env.IsDefEqU univs Γ)
      (fun _ _ _ h h' => h.trans henv hΓ h') hs hs'⟩

theorem NativeSpineMatch.instOuter_normal {name : Name} {levels : List VLevel} (hΓ : OnCtx Γ (env.IsType univs))
    (hhead : e = mkApps (.const name levels) templates)
    (hc : List.Forall₂ (NormalEqF η Γ) captures captures')
    (ht : HasType env univs Γ (e.instOuter captures) type) :
    NativeSpineMatch env univs Γ (e.instOuter captures) (e.instOuter captures') := by
  subst e
  simp only [instOuter_mkApps, instOuter_const] at ht ⊢
  obtain ⟨_, hconst⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
  obtain ⟨_, _, hw, _⟩ := HasType.const_inv henv.ordered hΓ hconst
  refine ⟨name, levels, levels, _, _, rfl, rfl, hw, hw,
    Lean4Lean.List.Forall₂.rfl (fun _ _ => show _ ≈ _ from rfl), ?_⟩
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply Lean4Lean.List.Forall₂.rfl
  intro template hm
  have hwf := native_arguments_wf hΓ ⟨_, ht⟩ _ (List.mem_map.mpr ⟨template, hm, rfl⟩)
  obtain ⟨A, hA⟩ := hwf
  have hA : HasType env univs Γ (InductiveSignature.instantiateParams template captures) A := by
    rw [instantiateParams_eq_instOuter]
    exact hA
  simpa only [instantiateParams_eq_instOuter] using (NormalEqF.instantiateParams_args hΓ hc hA).defeq hΓ


private theorem native_eta_match {domains : List VExpr} (hpos : 0 < domains.length) (hΓ : OnCtx Γ (env.IsType univs))
    {name : Name} {levels : List VLevel}
    (hlevels : ∀ l ∈ levels, l.WF univs)
    (hargs : List.Forall₂ (NormalEqF η Γ) args args')
    (hctor : NormalEqF η (domains.reverse ++ Γ) ctor ctor')
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs)) :
    NativeSpineMatch env univs (domains.reverse ++ Γ)
      (.app (nativeEtaBody (domains.length - 1) (mkApps (.const name levels) args)).lift ctor)
      (.app (nativeEtaBody (domains.length - 1) (mkApps (.const name levels) args')).lift ctor') := by
  rw [nativeEtaBody_spine, nativeEtaBody_spine]
  simp only [lift, liftN_mkApps, liftN, List.map_append]
  refine ⟨name, levels, levels,
    (args.map (·.liftN (domains.length - 1)) |>.map (·.liftN 1)) ++
      (vars (domains.length - 1) 0).map (·.liftN 1) ++ [ctor],
    (args'.map (·.liftN (domains.length - 1)) |>.map (·.liftN 1)) ++
      (vars (domains.length - 1) 0).map (·.liftN 1) ++ [ctor'],
    by simp only [mkApps_append]; rfl, by simp only [mkApps_append]; rfl, hlevels, hlevels,
    Lean4Lean.List.Forall₂.rfl (fun _ _ => show _ ≈ _ from rfl), ?_⟩
  apply normal_append
  · apply normal_append
    · apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      have he : domains.length - 1 + 1 = domains.length := by omega
      simpa only [liftN_liftN, Nat.zero_add, he] using
       Lean4Lean.List.Forall₂.imp (fun _ _ h => (h.weakN
        (show Ctx.LiftN domains.length 0 Γ (domains.reverse ++ Γ) from
          .zero _ (by simp))).defeq hctx) hargs
    · apply Lean4Lean.List.Forall₂.rfl
      intro e he
      simp only [List.mem_map, vars, List.mem_reverse, List.mem_range] at he
      obtain ⟨e, ⟨i, hi, rfl⟩, rfl⟩ := he
      exact ⟨_, .bvar (Lookup.ofLt (by simp only [List.length_append, List.length_reverse, liftVar, Nat.zero_add, Nat.not_lt_zero, ↓reduceIte]; omega)).2⟩
  · exact .cons (hctor.defeq hctx) .nil


/-- Replay a fixed installed native equation after normal changes to its
supplied arguments. The concrete constant head is preserved, and every
capture and reconstructed constructor remains tied to the generated program. -/
theorem NativePrefixReplay.congr_normal {name : Name} {levels : List VLevel}
    {p p' : PrefixProgram} (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativePrefixReplay env univs Γ (mkApps (.const name levels) args) p)
    (hlen : p.domains.length = p'.domains.length)
    (heq : p.equation = p'.equation) (hbody : p.equationBody = p'.equationBody)
    (hlevels : p.levels = p'.levels)
    (ha : List.Forall₂ (NormalEqF η Γ) args args')
    (hcaptures : List.Forall₂ (NormalEqF η (p.domains.reverse ++ Γ)) p.captures p'.captures)
    (hctor : NormalEqF η (p.domains.reverse ++ Γ) p.constructor p'.constructor)
    (hsource : HasType env univs Γ (mkApps (.const name levels) args') p'.type)
    (hhead : ∃ n ls as, p.equationBody.lhs = mkApps (.const n ls) as) :
    NativePrefixReplay env univs Γ (mkApps (.const name levels) args') p' ∧
      NormalEqF η Γ p.rhs p'.rhs := by
  obtain ⟨_, hh⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, H.source_typed⟩
  have hs := NormalEqF.mkApps_spine hΓ (.refl hh) ha H.source_typed
  have htypes := (((hs.defeq hΓ).of_l henv hΓ H.source_typed).hasType.2).uniqU henv hΓ hsource
  have hctx := (IsType.wrapForalls_inv henv hΓ (H.source_typed.isType henv hΓ)).1
  have W := IsDefEqU.wrapForalls_context henv hΓ (.zero : IsDefEqCtx env univs Γ Γ Γ) hlen htypes
  have hcLength := Lean4Lean.List.Forall₂.length_eq hcaptures
  have hpos : 0 < p.domains.length := List.length_pos_iff.mpr H.remaining_nonempty
  obtain ⟨hl, hr, ht⟩ := CaseSchema.EquationBody.extract_sound H.equation_body
  have hiota := IsDefEq.extra_instOuter henv hctx H.equation_present H.levels_wf
    H.levels_length hl.symm hr.symm ht.symm H.captures_length H.captures_typed
  constructor
  · refine {
      source_typed := hsource
      remaining_nonempty := ?_
      equation_present := heq ▸ H.equation_present
      equation_body := ?_
      levels_wf := hlevels ▸ H.levels_wf
      levels_length := ?_
      captures_length := ?_
      captures_typed := ?_
      major_prop := ?_
      native_lhs := ?_ }
    · intro hn
      apply H.remaining_nonempty
      apply List.eq_nil_of_length_eq_zero
      simpa only [hn, List.length_nil] using hlen
    · rw [← heq, ← hbody]
      exact H.equation_body
    · rw [← heq, ← hlevels]
      exact H.levels_length
    · rw [← hcLength, ← hbody]
      exact H.captures_length
    · intro j hj hd
      have hj₀ : j < p.captures.length := by omega
      have hd₀ : j < p.equationBody.domains.length := by simpa only [hbody] using hd
      have hold := H.captures_typed j hj₀ hd₀
      obtain ⟨u, hdom⟩ := hold.isType henv hctx
      have hn := NormalEqF.instantiateParams_args
        (e := p.equationBody.domains[j].instL p.levels) hctx (normal_take hcaptures j)
        (by simpa only [instantiateParams_eq_instOuter] using hdom)
      have ht := ((Lean4Lean.List.forall₂_getElem hcaptures j hj₀ hj).defeq hctx).of_l henv hctx hold
      have hnew := ht.hasType.2.defeqU_r henv hctx (by
        simpa only [instantiateParams_eq_instOuter] using hn.defeq hctx)
      apply HasType.defeqDFC henv W
      simpa only [← hbody, ← hlevels] using hnew
    · obtain ⟨P, hp, hm, hc⟩ := H.major_prop
      exact ⟨P, hp.defeqDFC henv W, hm.defeqDFC henv W,
        (((hctor.defeq hctx).of_l henv hctx hc).hasType.2).defeqDFC henv W⟩
    · apply NativeSpineMatch.defeqDFC henv W
      rw [← hlen, ← hbody, ← hlevels]
      obtain ⟨_, _, hw, _⟩ := HasType.const_inv henv.ordered hΓ hh
      have hleft := native_eta_match (name := name) hpos hΓ hw ha hctor hctx
      obtain ⟨n, ls, as, hhead⟩ := hhead
      have hright := NativeSpineMatch.instOuter_normal hctx
        (by rw [hhead, instL_mkApps]; rfl) hcaptures hiota.hasType.1
      exact (hleft.symm.trans hctx H.native_lhs).trans hctx hright
  · have hn := NormalEqF.instantiateParams_args
      (e := p.equationBody.rhs.instL p.levels) hctx hcaptures
      (by simpa only [instantiateParams_eq_instOuter] using hiota.hasType.2)
    unfold PrefixProgram.rhs
    rw [← hbody, ← hlevels]
    exact NormalEqF.wrapLams_congr hΓ hlen htypes hn

/-- The actual installed native program transports along normal equality of
its supplied arguments; no new capture or index-alignment certificate is needed. -/
theorem NativeDeltaRule.congr_normal {name : Name} {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativeDeltaRule env univs registry Γ name levels args rhs)
    (ha : List.Forall₂ (NormalEqF η Γ) args args') :
    ∃ rhs', NativeDeltaRule env univs registry Γ name levels args' rhs' ∧ NormalEqF η Γ rhs rhs' := by
  cases H with
  | @intro data program hlookup hregistered hname hlarge hw hz hg replay =>
    obtain ⟨program', hg'⟩ := prefixProgram_sameArity hg (Lean4Lean.List.Forall₂.length_eq ha).symm
    obtain ⟨_, _, hl, _, he, hb, _⟩ := prefixProgram_spec hg
    obtain ⟨_, _, hl', _, he', hb', _⟩ := prefixProgram_spec hg'
    have heq : program.equation = program'.equation := Option.some.inj (he.symm.trans he')
    have hbody : program.equationBody = program'.equationBody := by
      rw [heq] at hb
      exact Option.some.inj (hb.symm.trans hb')
    obtain ⟨_, _, _, _, hlen, _, _⟩ := prefixProgram_layout hg
    obtain ⟨_, _, _, _, hlen', _, _⟩ := prefixProgram_layout hg'
    have hlength : program.domains.length = program'.domains.length := by
      rw [hlen, hlen', Lean4Lean.List.Forall₂.length_eq ha]
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, replay.source_typed⟩
    have hs := NormalEqF.mkApps_spine hΓ (.refl hhead) ha replay.source_typed
    have hsource := hregistered.prefixType henv hΓ hw hg'
      (by simpa only [hname] using
        (show VExpr.WF env univs Γ _ from
          ⟨_, ((hs.defeq hΓ).of_l henv hΓ replay.source_typed).hasType.2⟩))
    have replayData : NativePrefixReplay env univs Γ (mkApps (.const data.name levels) args) program := by
      simpa only [hname] using replay
    obtain ⟨hcaptures, hctor⟩ := replayData.normal_components hΓ hg hg' ha
    have hnative := hregistered.singletonEquation_body_head he hb
    obtain ⟨replay', hnormal⟩ := replay.congr_normal hΓ hlength heq hbody (hl.trans hl'.symm)
      ha hcaptures hctor (by simpa only [hname] using hsource) hnative
    exact ⟨_, .intro hlookup hregistered hname hlarge hw hz hg' replay', hnormal⟩

end Lean4Lean.VEnv
