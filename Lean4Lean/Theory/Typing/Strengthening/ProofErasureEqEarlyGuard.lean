import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixGuardReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqVariableGuardReadout

/-! # Canonical Eq guards before the requested index is supplied

Once the carrier and left endpoint are supplied, every earlier-than-five
prefix compares that lifted left endpoint with its fresh requested index.
The joint grammar cannot certify this comparison at a proposition carrier.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape InductiveSignature
variable [Params] {C : SingletonPrefixCode}

/-- At two, three, or four supplied Eq.rec arguments, the literal family guard
requests equality of the supplied left endpoint and fresh variable one. -/
theorem eqRec_early_family_guard_iff
    (heq : env.HasCanonicalEq) (hr : RecursorRegistered env data)
    (hn : data.name = ``Eq.rec) (hz : data.sourceLevel [v,w] ≈ .zero)
    (hS : data.singletonLayout env [v,w] = some S)
    (hE : data.propElim [v,w] = some E) (hrest : rest.length ≤ 2) :
    GuardedSingleton.FamilyGuard Cmp Γ data [v,w] (α :: a :: rest) program S E ↔
      Cmp (program.domains.reverse ++ Γ)
        (eqApp w (α.liftN (4-rest.length)) (a.liftN (4-rest.length)) (a.liftN (4-rest.length)))
        (eqApp w (α.liftN (4-rest.length)) (a.liftN (4-rest.length)) (.bvar 1)) := by
  obtain ⟨hfam, hcs, hp, _, _⟩ := hr.eqRec_singleton_equation heq hn hz
  have hoff := (hr.eqRec_target heq hn).2.1
  have hi := hr.eqRec_numIndices heq hn
  have hio : data.indexOffset = 4 := by simp [RecursorData.indexOffset, hp, hfam, hcs]
  have hparams : (data.openedArguments (α :: a :: rest)).take data.numParams =
      [α.liftN (4-rest.length), a.liftN (4-rest.length)] := by
    simp [RecursorData.openedArguments, hoff, hp]
  have hindex : ((data.openedArguments (α :: a :: rest)).drop data.indexOffset).take data.numIndices =
      [.bvar 1] := by
    cases rest with
    | nil => simp [RecursorData.openedArguments, hoff, hio, hi, vars, List.range, List.range.loop]
    | cons M rest => cases rest with
      | nil => simp [RecursorData.openedArguments, hoff, hio, hi, vars, List.range, List.range.loop]
      | cons m rest => cases rest with
        | nil => simp [RecursorData.openedArguments, hoff, hio, hi, vars, List.range, List.range.loop]
        | cons _ _ => simp only [List.length_cons] at hrest; omega
  unfold GuardedSingleton.FamilyGuard
  dsimp only
  rw [hparams, hindex, eqRec_transportedFamily heq hr hn hz hS hE,
    eqRec_propElim_family heq hr hn hz hS hE]
  rfl

omit [Params] in
private theorem opened_early
    {data : RecursorData} {rest : List VExpr} {P : VExpr}
    (hoff : data.majorOffset = 5) (hrest : rest.length ≤ 2) :
    ∃ M m, data.openedArguments (.sort .zero :: P :: rest) =
      [.sort .zero, P.liftN (4-rest.length), M, m, .bvar 1, .bvar 0] := by
  cases rest with
  | nil => exact ⟨.bvar 3, .bvar 2, by simp [RecursorData.openedArguments, hoff, vars, List.range, List.range.loop, VExpr.liftN]⟩
  | cons M rest => cases rest with
    | nil => exact ⟨M.liftN 3, .bvar 2, by simp [RecursorData.openedArguments, hoff, vars, List.range, List.range.loop, VExpr.liftN]⟩
    | cons m rest => cases rest with
      | nil => exact ⟨M.liftN 2, m.liftN 2, by simp [RecursorData.openedArguments, hoff, vars, List.range, List.range.loop, VExpr.liftN]⟩
      | cons _ _ => simp only [List.length_cons] at hrest; omega

/-- A general singleton code cannot certify a Prop-carrier Eq.rec prefix at
two, three, or four arguments. Its requested index is fresh, whereas the left
endpoint and its typing come from below the residual telescope. -/
theorem SingletonPrefixCode.Valid.no_eq_prop_early_guard
    (V : C.Valid) (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (hn : C.data.name = ``Eq.rec) (hl : C.levels = [v,.succ .zero])
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hrest : rest.length ≤ 2) (ha : (.sort .zero :: P :: rest).length = C.arity)
    (ht : VExpr.WF env univs Γ (VExpr.mkApps (.const C.data.name C.levels) (.sort .zero :: P :: rest)))
    (hcalc : C.telescope ((.sort .zero :: P :: rest).map (proofErase Γ)) = some (domains,result))
    (HG : C.guardWith (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ) domains
      ((.sort .zero :: P :: rest).map (proofErase Γ))) : False := by
  obtain ⟨program, hg, _, HF⟩ := V.realizeWith heq hΓ ha ht hcalc HG
  have hsrc := V.registered.prefixType henv hΓ V.levels_wf hg ht
  obtain ⟨hctx, hopen⟩ := hsrc.etaOpen_wf henv.ordered hΓ
  obtain ⟨_, _, _, _, hlen, _, _⟩ := RecursorData.singletonUnfolding_layout hg
  have hoff := (V.registered.eqRec_target heq hn).2.1
  have hlen : program.domains.length = 4-rest.length := by simpa [hoff] using hlen
  obtain ⟨M, m, hall⟩ := opened_early (P := P) hoff hrest
  have hopen' : VExpr.WF env univs (program.domains.reverse ++ Γ)
      (eqRecApp v (.succ .zero) (.sort .zero) (P.liftN (4-rest.length)) M m (.bvar 1) (.bvar 0)) := by
    refine ⟨program.result, ?_⟩
    rw [etaOpen_spine, VExpr.liftN_mkApps, VExpr.liftN, ← VExpr.mkApps_append, hlen] at hopen
    rw [show ((.sort .zero :: P :: rest).map (·.liftN (4-rest.length)) ++ vars (4-rest.length) 0) =
        C.data.openedArguments (.sort .zero :: P :: rest) by simp [RecursorData.openedArguments, hoff],
      hall, hn, hl] at hopen
    exact hopen
  obtain ⟨_, _, _, hPw, _, _, hv, _⟩ := eqRecApp_typings henv heq hctx hopen'
  rw [hl] at HF
  have HF := (eqRec_early_family_guard_iff heq V.registered hn (hl ▸ V.zero)
    (hl ▸ V.layout_eq) (hl ▸ V.elim_eq) hrest).1 HF
  have HC := proofErase_joint_eq_sort_decode heq (by trivial) hstep hhead hinert hctx
    hPw hPw hPw hv HF
  have W : Ctx.LiftN (4-rest.length) 0 Γ (program.domains.reverse ++ Γ) :=
    .zero _ (by simpa only [List.length_reverse] using hlen)
  exact proofErase_joint_types_no_fresh_variable hstep hhead hΓ hctx W hP hv (by omega) HC

/-- Supplying only the carrier leaves distinct fresh variables as the two
equality endpoints. The literal generated family guard retains both indices. -/
theorem eqRec_one_family_guard_iff
    (heq : env.HasCanonicalEq) (hr : RecursorRegistered env data)
    (hn : data.name = ``Eq.rec) (hz : data.sourceLevel [v,w] ≈ .zero)
    (hS : data.singletonLayout env [v,w] = some S)
    (hE : data.propElim [v,w] = some E) :
    GuardedSingleton.FamilyGuard Cmp Γ data [v,w] [α] program S E ↔
      Cmp (program.domains.reverse ++ Γ)
        (eqApp w (α.liftN 5) (.bvar 4) (.bvar 4))
        (eqApp w (α.liftN 5) (.bvar 4) (.bvar 1)) := by
  obtain ⟨hfam, hcs, hp, _, _⟩ := hr.eqRec_singleton_equation heq hn hz
  have hoff := (hr.eqRec_target heq hn).2.1
  have hi := hr.eqRec_numIndices heq hn
  have hio : data.indexOffset = 4 := by simp [RecursorData.indexOffset, hp, hfam, hcs]
  simp only [GuardedSingleton.FamilyGuard, RecursorData.openedArguments, hoff, hp, hio, hi,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.map_cons, List.map_nil,
    vars, List.range, List.range.loop, List.reverse_cons, List.reverse_nil,
    List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    Nat.zero_add]
  rw [eqRec_transportedFamily heq hr hn hz hS hE, eqRec_propElim_family heq hr hn hz hS hE]
  rfl

/-- A Prop-carrier singleton prefix at one supplied argument cannot pass its
joint family guard: the two fresh proposition variables have different indices. -/
theorem SingletonPrefixCode.Valid.no_eq_prop_one_guard
    (V : C.Valid) (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (hn : C.data.name = ``Eq.rec) (hl : C.levels = [v,.succ .zero])
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : 1 = C.arity)
    (ht : VExpr.WF env univs Γ (VExpr.mkApps (.const C.data.name C.levels) [.sort .zero]))
    (hcalc : C.telescope ([.sort .zero].map (proofErase Γ)) = some (domains,result))
    (HG : C.guardWith (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ) domains
      ([.sort .zero].map (proofErase Γ))) : False := by
  obtain ⟨program, hg, _, HF⟩ := V.realizeWith (args := [VExpr.sort .zero]) heq hΓ ha ht hcalc HG
  have hsrc := V.registered.prefixType henv hΓ V.levels_wf hg ht
  obtain ⟨hctx, hopen⟩ := hsrc.etaOpen_wf henv.ordered hΓ
  obtain ⟨_, _, _, _, hlen, _, _⟩ := RecursorData.singletonUnfolding_layout hg
  have hoff := (V.registered.eqRec_target heq hn).2.1
  have hlen : program.domains.length = 5 := by simpa [hoff] using hlen
  have hopen' : VExpr.WF env univs (program.domains.reverse ++ Γ)
      (eqRecApp v (.succ .zero) (.sort .zero) (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)) := by
    refine ⟨program.result, ?_⟩
    simpa [HasType, etaOpen_spine, VExpr.liftN_mkApps, VExpr.liftN, ← VExpr.mkApps_append,
      hlen, hn, hl, vars, List.range, List.range.loop, eqRecApp, VExpr.mkApps] using hopen
  obtain ⟨_, _, _, hP, _, _, hQ, _⟩ := eqRecApp_typings henv heq hctx hopen'
  rw [hl] at HF
  have HF := (eqRec_one_family_guard_iff heq V.registered hn (hl ▸ V.zero)
    (hl ▸ V.layout_eq) (hl ▸ V.elim_eq)).1 HF
  have HC := proofErase_joint_eq_sort_decode heq (by trivial) hstep hhead hinert hctx hP hP hP hQ HF
  rw [show proofErase _ (.bvar 4) = .bvar 4 from if_neg (not_isProof_of_sort hctx hP),
    show proofErase _ (.bvar 1) = .bvar 1 from if_neg (not_isProof_of_sort hctx hQ)] at HC
  exact (by decide : (4 : Nat) ≠ 1) (HC.bvar_indices hhead)

/-- With no supplied arguments the generated family guard compares two
fresh endpoints at the fresh carrier, keeping their distinct indices. -/
theorem eqRec_zero_family_guard_iff
    (heq : env.HasCanonicalEq) (hr : RecursorRegistered env data)
    (hn : data.name = ``Eq.rec) (hz : data.sourceLevel [v,w] ≈ .zero)
    (hS : data.singletonLayout env [v,w] = some S)
    (hE : data.propElim [v,w] = some E) :
    GuardedSingleton.FamilyGuard Cmp Γ data [v,w] [] program S E ↔
      Cmp (program.domains.reverse ++ Γ)
        (eqApp w (.bvar 5) (.bvar 4) (.bvar 4))
        (eqApp w (.bvar 5) (.bvar 4) (.bvar 1)) := by
  obtain ⟨hfam, hcs, hp, _, _⟩ := hr.eqRec_singleton_equation heq hn hz
  have hoff := (hr.eqRec_target heq hn).2.1
  have hi := hr.eqRec_numIndices heq hn
  have hio : data.indexOffset = 4 := by simp [RecursorData.indexOffset, hp, hfam, hcs]
  simp only [GuardedSingleton.FamilyGuard, RecursorData.openedArguments, hoff, hp, hio, hi,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.map_cons, List.map_nil,
    vars, List.range, List.range.loop, List.reverse_cons, List.reverse_nil,
    List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    Nat.zero_add]
  rw [eqRec_transportedFamily heq hr hn hz hS hE, eqRec_propElim_family heq hr hn hz hS hE]
  rfl

open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary

/-- The zero-argument singleton prefix cannot pass its joint guard at a
positive Eq carrier universe. Its fresh carrier stays a variable, so native
carrier checking cannot identify the distinct fresh equality endpoints. -/
theorem SingletonPrefixCode.Valid.no_eq_zero_guard
    (V : C.Valid) (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (hn : C.data.name = ``Eq.rec) (hl : C.levels = [v,.succ w])
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : 0 = C.arity)
    (ht : VExpr.WF env univs Γ (.const C.data.name C.levels))
    (hcalc : C.telescope [] = some (domains,result))
    (HG : C.guardWith (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ) domains []) : False := by
  obtain ⟨program, hg, _, HF⟩ := V.realizeWith (args := []) heq hΓ ha ht hcalc HG
  have hsrc := V.registered.prefixType henv hΓ V.levels_wf hg ht
  obtain ⟨hctx, hopen⟩ := hsrc.etaOpen_wf henv.ordered hΓ
  obtain ⟨_, _, _, _, hlen, _, _⟩ := RecursorData.singletonUnfolding_layout hg
  have hoff := (V.registered.eqRec_target heq hn).2.1
  have hlen : program.domains.length = 6 := by simpa [hoff] using hlen
  have hopen' : VExpr.WF env univs (program.domains.reverse ++ Γ)
      (eqRecApp v (.succ w) (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)) := by
    refine ⟨program.result, ?_⟩
    simpa [HasType, etaOpen_spine, VExpr.liftN_mkApps, VExpr.liftN, ← VExpr.mkApps_append,
      hlen, hn, hl, vars, List.range, List.range.loop, eqRecApp, VExpr.mkApps] using hopen
  obtain ⟨_, hw, hα, hP, _, _, hQ, _⟩ := eqRecApp_typings henv heq hctx hopen'
  rw [hl] at HF
  have HF := (eqRec_zero_family_guard_iff heq V.registered hn (hl ▸ V.zero)
    (hl ▸ V.layout_eq) (hl ▸ V.elim_eq)).1 HF
  have HC := proofErase_joint_types_inferred hstep hctx
    (HasType.eqApp heq hw hα hP hP) (HasType.eqApp heq hw hα hP hQ) HF
  rw [proofErase_eqProofType heq hw hctx hα hP hP,
    proofErase_eqProofType heq hw hctx hα hP hQ,
    show proofErase _ (.bvar 5) = .bvar 5 from if_neg (not_isProof_of_sort hctx hα),
    show proofErase _ (.bvar 4) = .bvar 4 from if_neg (not_proof_at_positive_type hctx hα hP),
    show proofErase _ (.bvar 1) = .bvar 1 from if_neg (not_proof_at_positive_type hctx hα hQ)] at HC
  have HD := JointCompare.eq_bvar_decode heq hhead hinert HC
  exact (by decide : (4 : Nat) ≠ 1) (HD.bvar_indices hhead)

end Lean4Lean.VEnv.Strengthening
