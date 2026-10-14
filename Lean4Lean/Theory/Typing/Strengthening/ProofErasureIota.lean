import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePatterns
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTemplates

/-! # Visible iota replay with arbitrary stored RHS templates

Stored iota RHSs apply a closed template to a list of captured arguments. The
template need not normalize. Retaining its lambda wrappers makes erasure of the
whole reduct structural whenever the matched source is a non-proof.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions PatternCompute CheckFromTyping)
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

variable [Params]

/-- Every typed non-proof application spine erases structurally, including a
spine whose head is an arbitrary closed lambda template. -/
theorem proofErase_mkApps (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (mkApps f args) T) (hn : ¬ IsProof Γ (mkApps f args)) :
    proofErase Γ (mkApps f args) =
      ProofShape.mkApps (proofErase Γ f) (args.map (proofErase Γ)) := by
  induction args using List.snoc_induction generalizing T with
  | nil => rfl
  | snoc args a ih =>
    rw [mkApps_snoc] at ht hn ⊢
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    simp only [proofErase, if_neg hn, ih hf (not_isProof_fn hΓ hf ha hn),
      List.map_append, List.map_cons, List.map_nil, ProofShape.mkApps_snoc]

namespace ProofShape
/-- A registered fixed-template spine whose original constructor match survives
erasure. The closed template has its declaration typing, and the check is
recovered from source typing. Neither template normalization nor capture equality
is required. -/
inductive TemplatePrimitive : ProofShape → ProofShape → Prop where
  | intro {p : Pattern} {check : p.Check} {paths : List p.Path}
      {captures : p.Path → ProofShape} {rhs : VExpr} {hclosed : rhs.Closed} :
      Pat p ((paths.map Pattern.RHS.var).foldl Pattern.RHS.app (.fixed rhs hclosed), check) →
      CheckFromTyping env univs p
        ((paths.map Pattern.RHS.var).foldl Pattern.RHS.app (.fixed rhs hclosed), check) ls →
      env.HasType univs [] (rhs.instL ls) T →
      Matches p source ls captures →
      TemplatePrimitive source (mkApps (proofErase [] (rhs.instL ls)) (paths.map captures))
end ProofShape

/-- A visible fixed-template rule replays at every typed representative. The
original match supplies proof captures, while closed typing fixes head erasure. -/
theorem erased_template_patterns_replay (hs : D.Sound env univs) :
    ErasedPrimitiveReplay D ProofShape.TemplatePrimitive := by
  intro Γ e T out hΓ ht R
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | intro hp hc hr hm =>
    rw [← hsrc] at hm
    have hn : ¬ IsProof Γ e := fun h => hm.ne_proof (proofErase_eq_proof.2 h)
    obtain ⟨original, HM, HE⟩ := proofErase_pattern_match_inv hm
    have R' := PatternCompute.pattern (D := D) hp HM hc
    have HEq := R'.simAt hs hΓ T ht
    have hn' := mt (isProof_congr hΓ HEq).2 hn
    refine ⟨_, R', ?_⟩
    have hty := HEq.hasType.2
    simp only [Pattern.RHS.apply_foldl_var, Pattern.RHS.apply] at hty hn' ⊢
    rw [proofErase_mkApps hΓ hty hn',
      proofErase_closed_context (hr.closedN' henv.ordered.closed (by trivial)).1 hr hΓ]
    congr 1
    simp only [List.map_map, Function.comp_def, HE]

/-- Every generated iota RHS has the fixed-template form used by replay.
This includes arbitrary retained recursor and constructor capture counts. -/
theorem erased_iota_template_step
    {rhs : VExpr} {hclosed : rhs.Closed}
    (hp : Pat (SimplePattern.iota recName (k + nindices) ctorName (cnparams + nfields)).toPattern
      (SimplePattern.iotaRHS' recName ctorName k nindices cnparams nfields rhs hclosed, check))
    (hc : CheckFromTyping env univs
      (SimplePattern.iota recName (k + nindices) ctorName (cnparams + nfields)).toPattern
      (SimplePattern.iotaRHS' recName ctorName k nindices cnparams nfields rhs hclosed, check) ls)
    (ht : env.HasType univs [] (rhs.instL ls) T)
    (hm : ProofShape.Matches
      (SimplePattern.iota recName (k + nindices) ctorName (cnparams + nfields)).toPattern
      source ls captures) :
    ProofShape.TemplatePrimitive source
      (ProofShape.mkApps (proofErase [] (rhs.instL ls))
        ((SimplePattern.iotaPaths recName ctorName k nindices cnparams nfields).map captures)) :=
  .intro hp hc ht hm

/-- The actual stored rule supplies the template typing used by visible iota
replay; no new typing premise is imposed on its lambda-wrapped RHS. -/
theorem erased_iota_rule_step
    (Hrule : VIotaRuleTyped env recName recUvars nparams cnparams nmotives nminors nindices ctorName
      ctorLevels nfields df ctorParams)
    {hclosed : df.rhs.Closed}
    (hp : Pat (SimplePattern.iota recName (nparams + nmotives + nminors + nindices)
      ctorName (cnparams + nfields)).toPattern
      (SimplePattern.iotaRHS recName ctorName nparams nmotives nminors nindices cnparams nfields
        df.rhs hclosed, check))
    (hc : CheckFromTyping env univs
      (SimplePattern.iota recName (nparams + nmotives + nminors + nindices)
        ctorName (cnparams + nfields)).toPattern
      (SimplePattern.iotaRHS recName ctorName nparams nmotives nminors nindices cnparams nfields
        df.rhs hclosed, check) ls)
    (hls : ∀ l ∈ ls, l.WF univs)
    (hm : ProofShape.Matches
      (SimplePattern.iota recName (nparams + nmotives + nminors + nindices)
        ctorName (cnparams + nfields)).toPattern source ls captures) :
    ProofShape.TemplatePrimitive source
      (ProofShape.mkApps (proofErase [] (df.rhs.instL ls))
        ((SimplePattern.iotaPaths recName ctorName (nparams + nmotives + nminors)
          nindices cnparams nfields).map captures)) :=
  erased_iota_template_step hp hc (Hrule.wf.2.instL hls) hm

omit [Params] in
/-- An enabled rule in the actual environment supplies its uniform check from
one original check. This removes the replay interface's extra check certificate
when working with concrete registered iota templates. -/
theorem erased_iota_template_step_concrete {E : VEnv} (hE : E.WF)
    {rhs : VExpr} {hclosed : rhs.Closed}
    (hp : ConcretePattern E
      (SimplePattern.iota recName (k + nindices) ctorName (cnparams + nfields)).toPattern
      (SimplePattern.iotaRHS' recName ctorName k nindices cnparams nfields rhs hclosed, check))
    {relation : VExpr → VExpr → Prop}
    (hck : check.OK relation ls original)
    (ht : E.HasType U [] (rhs.instL ls) T)
    (hm : ProofShape.Matches
      (SimplePattern.iota recName (k + nindices) ctorName (cnparams + nfields)).toPattern
      source ls captures) :
    @ProofShape.TemplatePrimitive (hE.params U) source
      (ProofShape.mkApps (@proofErase (hE.params U) [] (rhs.instL ls))
        ((SimplePattern.iotaPaths recName ctorName k nindices cnparams nfields).map captures)) := by
  letI := hE.params U
  exact erased_iota_template_step hp (PureObservation.ConcretePattern.checkFromTyping hE hp hck) ht hm

/-- The previous concrete fragment together with arbitrary stored RHS spines. -/
def ErasedIotaPrimitive (D : Definitions) (a b : ProofShape) : Prop :=
  ErasedRegisteredPrimitive D a b ∨ ProofShape.TemplatePrimitive a b

/-- Visible iota templates preserve exact primitive replay. -/
theorem erased_iota_replay (hs : D.Sound env univs) :
    ErasedPrimitiveReplay D (ErasedIotaPrimitive D) := by
  intro Γ e T out hΓ ht R
  exact R.elim (erased_registered_replay hs hΓ ht) (erased_template_patterns_replay hs hΓ ht)

/-- Common erased results using beta, delta, projection, quotient and visible
iota templates descend from independently typed endpoints below binders. -/
theorem proofErase_iota_join_descend (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (Ra : ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ' (a.liftN n k)) out)
    (Rb : ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ' (b.liftN n k)) out) :
    env.IsDefEq univs Γ a b T :=
  proofErase_compute_join_descend hs (erased_iota_replay hs) hΓ hΓ' W ha hb Ra Rb

end Lean4Lean.VEnv.Strengthening
