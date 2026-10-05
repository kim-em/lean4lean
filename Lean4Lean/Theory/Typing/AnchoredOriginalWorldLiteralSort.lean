import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation
import Lean4Lean.Theory.Typing.AnchoredSortAdequacy
import Lean4Lean.Theory.Typing.AnchoredSortableSortRule

/-! Literal-sort reconstruction selects ordinary syntax and its annotation
jointly from an actual code interpretation. No original opening survives. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open EquationWorldClosureOrder
set_option maxHeartbeats 1800000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private structure LiteralSortQuery (strata : EquationStratification env)
    (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (level : VLevel) (profile : Profile n) where
  query : Obs env U registry target locals σ (.sort level) profile []
  annotation : WorldLegacyObsProvenance strata query
  worlds : annotation.worlds = []
  depth : ∀ policy, query.headDepth policy = 0

private def LiteralSortQuery.empty : LiteralSortQuery strata U registry target locals σ level
    (.empty : Profile n) :=
  ⟨.empty, .empty, rfl, fun _ => by simp only [Obs.headDepth]⟩

private def LiteralSortQuery.sort (relevant : Relevant level flag) :
    LiteralSortQuery strata U registry target locals σ level (Profile.sort (n := n) flag) :=
  ⟨.sort relevant, .sort relevant, rfl, fun _ => by simp only [Obs.headDepth]⟩

private def LiteralSortQuery.union
    (left : LiteralSortQuery strata U registry target locals σ level p)
    (right : LiteralSortQuery strata U registry target locals σ level q) :
    LiteralSortQuery strata U registry target locals σ level (p.union q) := {
  query := .union left.query right.query
  annotation := .union left.query right.query left.annotation right.annotation
  worlds := by
    change left.annotation.worlds ++ right.annotation.worlds = []
    rw [left.worlds, right.worlds]
    rfl
  depth := by intro policy; simp only [Obs.headDepth, left.depth, right.depth, Nat.max_self] }

private def LiteralSortQuery.pad
    (source : LiteralSortQuery strata U registry target locals σ level profile) :
    LiteralSortQuery strata U registry target locals σ level profile.pad := {
  query := .pad source.query
  annotation := .pad source.query source.annotation
  worlds := source.worlds
  depth := by intro policy; simpa only [Obs.headDepth] using source.depth policy }

private theorem literalSortQuery
    {strata : EquationStratification env}
    (formed : OnCtx target (env.IsType U))
    (related : TypeRelated env U registry target (.sort level) right (profile : Profile n)) :
    Nonempty (LiteralSortQuery strata U registry target locals σ level profile) := by
  induction n with
  | zero =>
    induction profile with
    | nil => exact ⟨.empty⟩
    | cons flag tail ih =>
      have flagCode := related target .refl (.refl formed) flag (by
        simpa only [Profile.rename_refl, Profile.atoms] using (List.mem_cons_self (a := flag) (l := tail)))
      have tailCode : TypeRelated env U registry target (.sort level) right tail :=
        TypeRelated.of_singletons fun atom member => related.singleton (List.mem_cons_of_mem _ member)
      obtain ⟨rest⟩ := ih tailCode
      exact ⟨(LiteralSortQuery.sort flagCode.literal_relevant).union rest⟩
  | succ n ih =>
    have atomic (atom : Atom (n+1))
        (code : TypeRelated env U registry target (.sort level) right (.singleton atom)) :
        Nonempty (LiteralSortQuery strata U registry target locals σ level (.singleton atom)) := by
      have capability := code target .refl (.refl formed) atom (by
        simpa only [Profile.rename_refl, Profile.atoms, Profile.singleton, Profile.mk] using
          (List.mem_singleton_self atom))
      simp only [lift'_refl] at capability
      cases atom with
      | sort flag => exact ⟨.sort capability.literal_relevant⟩
      | fn | ctor | record => exact capability.elim
      | pi A B domain rows =>
        obtain ⟨witness⟩ := capability
        have impossible := witness.leftExposure.literalSort_head
        contradiction
      | family demand =>
        obtain ⟨witness⟩ := capability
        have impossible := congrArg (fun expression => expression.getAppFnArgs.1)
          witness.leftExposure.literalSort_head
        have head := VExpr.getAppFnArgs_mkApps_head
          (.const demand.name witness.leftLevels) witness.leftArguments
        rw [head] at impossible
        contradiction
      | pad atom =>
        obtain ⟨query⟩ := ih capability
        exact ⟨query.pad⟩
    induction profile with
    | nil => exact ⟨.empty⟩
    | cons atom tail ihTail =>
      obtain ⟨head⟩ := atomic atom (related.singleton List.mem_cons_self)
      have tailCode : TypeRelated env U registry target (.sort level) right tail :=
        TypeRelated.of_singletons fun atom member => related.singleton (List.mem_cons_of_mem _ member)
      obtain ⟨rest⟩ := ihTail tailCode
      exact ⟨head.union rest⟩

/-- Transfer an actually interpreted universe code, then construct the SAME
ordinary destination certificate and its empty-world annotation. -/
theorem TypeRelated.literalSortControlled
    {strata : EquationStratification env}
    {node : EndpointState sourceEnv U source expression assigned}
    (literal : expression = .sort rightLevel)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (leftWF : leftLevel.WF U) (rightWF : rightLevel.WF U)
    (levels : leftLevel ≈ rightLevel)
    (code : TypeRelated env U registry target (.sort leftLevel) (.sort leftLevel) (profile : Profile n))
    (sorted : profile.HasType (.sort relevant))
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length)) :
    ∃ certificate : RichCert sourceEnv env U registry target node locals τ relevant profile [],
      ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
        TypeRelated env U registry target (.sort leftLevel) (.sort rightLevel) profile ∧
        ready.annotation.worlds = [] ∧ ∀ policy, certificate.headDepth policy = 0 := by
  obtain ⟨source⟩ := literalSortQuery (strata := strata) (locals := locals) (σ := τ) formed code
  obtain ⟨answer⟩ := (SortableObs.legacy source.query).sortHereditary (available := fun _ => [])
    (τ := τ) henv hscoped leftWF rightWF levels (by intro i need member; cases member) formed
    (fun _ _ member => nomatch member)
  have paired : TypeRelated env U registry target (.sort leftLevel) (.sort rightLevel) profile := by
    simpa only [subst_sort] using (answer.requestedRelated henv formed).code_of_sortable henv hscoped formed sorted
  have rightCode := (paired.symm henv sorted.wf_value).left_diagonal
  obtain ⟨output⟩ := literalSortQuery (strata := strata) (locals := locals) (σ := τ) formed rightCode
  subst expression
  let certificate : RichCert sourceEnv env U registry target node locals τ relevant profile [] :=
    .legacy (.seed output.query sorted)
  let annotation : WorldCertProvenance strata certificate := .legacy _ (.seed _ _ output.annotation)
  have worlds : annotation.worlds = [] := output.worlds
  have depth : ∀ policy, certificate.headDepth policy = 0 := by
    intro policy
    simpa only [certificate, RichCert.headDepth, SortableCert.headDepth] using output.depth policy
  let ready : ControlledStoredQuery controls frontier (.certificate certificate) := {
    annotation := annotation
    within := fun control active => by
      change certificate.headDepth _ ≤ _
      rw [depth]
      exact Nat.zero_le _
    sponsored := by
      change Sponsored frontier annotation.worlds
      rw [worlds]
      intro world member
      cases member }
  exact ⟨certificate, ready, paired, worlds, depth⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
