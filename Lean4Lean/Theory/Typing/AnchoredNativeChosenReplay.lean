import Lean4Lean.Theory.Typing.AnchoredNativeSupportedReplay
import Lean4Lean.Theory.Typing.NativeCaptureRoles

/-! Replay a native capture plan with the caller's actual proof witnesses.
Data slots remain the fixed native indices. This produces source fitting
entries in the base target world, without allocating canonical proof slots. -/
namespace Lean4Lean.VEnv.CapturePlan
open VExpr

def choose (plan : CapturePlan declared) (arguments witnesses : Subst) : Subst :=
  match plan with
  | .nil => .id
  | .index previous position => (previous.choose arguments witnesses.tail).cons (arguments position)
  | .proof previous => (previous.choose arguments witnesses.tail).cons witnesses.head

/-- Only data slots constrain the chosen witnesses. -/
def IndexAgreement (plan : CapturePlan declared) (arguments witnesses : Subst) : Prop :=
  match plan with
  | .nil => True
  | .index previous position =>
    previous.IndexAgreement arguments witnesses.tail ∧ witnesses.head = arguments position
  | .proof previous => previous.IndexAgreement arguments witnesses.tail

theorem choose_agrees (plan : CapturePlan declared)
    (agree : plan.IndexAgreement arguments witnesses) :
    ∀ i < declared.length, plan.choose arguments witnesses i = witnesses i := by
  induction plan generalizing witnesses with
  | nil => intro i h; simp at h
  | index previous position ih =>
    intro i hi
    cases i with
    | zero => exact agree.2.symm
    | succ i => exact ih agree.1 i (Nat.lt_of_succ_lt_succ hi)
  | proof previous ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact ih agree i (Nat.lt_of_succ_lt_succ hi)

/-- Read the finite ordered role certificate; no captured-expression equality
is used to infer which constructor field was selected. -/
theorem indexAgreement_of_roles (plan : CapturePlan declared)
    (agrees : ∀ i position, plan.roles.reverse[i]? = some (some position) →
      witnesses i = arguments position) : plan.IndexAgreement arguments witnesses := by
  induction plan generalizing witnesses with
  | nil => trivial
  | index previous position ih =>
    refine ⟨ih ?_, ?_⟩
    · intro i p hp
      exact agrees (i + 1) p (by simpa only [roles, List.reverse_append,
        List.reverse_singleton, List.singleton_append, List.getElem?_cons_succ] using hp)
    · exact agrees 0 position (by simp [roles])
  | proof previous ih =>
    apply ih
    intro i p hp
    exact agrees (i + 1) p (by simpa only [roles, List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.getElem?_cons_succ] using hp)

end Lean4Lean.VEnv.CapturePlan

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open private captures_at from Lean4Lean.Theory.Typing.AnchoredNativePrefixPlan
set_option backward.isDefEq.respectTransparency false

private theorem prefix_choose (offset : Nat) (domains : List VExpr) (arguments witnesses : Subst) :
    (nativePrefixPlan offset domains).choose arguments witnesses =
      (nativePrefixPlan offset domains).captures arguments := by
  induction domains generalizing offset witnesses with
  | nil => rfl
  | cons A rest ih =>
    simp only [nativePrefixPlan, CapturePlan.choose, CapturePlan.captures, ih,
      nativePrefixPlan_count, liftN_zero]

/-- The actual source tuple supplies proof witnesses; original field
formation and the stored finite domain chain supply all semantic data casts. -/
theorem NativeSupportedReplay.chosen
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ A level}, sourceEnv.IsDefEqStrong U Γ A A (.sort level) →
      GradedJoint env U registry Γ A A (.sort level))
    {target argumentSource : List VExpr} {argumentLocals : List Nat}
    {arguments : Subst} {argumentAvailable : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (newValues : List VExpr) (newLength : newValues.length = argumentSource.length)
    (rawArguments : Ctx.SubstEq env U target arguments (nativeCaptureSubst newValues) argumentSource)
    (argumentFits : PairedFits env U registry argumentSource target argumentLocals
      arguments (nativeCaptureSubst newValues) argumentAvailable)
    {declared : List VExpr} {plan : CapturePlan declared} {captures : Subst}
    {locals : List Nat} {available : Valuation}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable declared plan captures locals available)
    (witnesses : Subst)
    (witnessesTyped : Ctx.SubstEq env U target witnesses witnesses declared)
    (agree : plan.IndexAgreement (nativeCaptureSubst newValues) witnesses) :
    Ctx.SubstEq env U target captures (plan.choose (nativeCaptureSubst newValues) witnesses) declared ∧
    PairedFits env U registry declared target locals captures
      (plan.choose (nativeCaptureSubst newValues) witnesses) available := by
  induction replay generalizing witnesses with
  | nil => exact ⟨.nil, .nil⟩
  | @commonPrefix later declared plan source literal count added captures =>
    have raw := rawArguments
    have fits := argumentFits
    rw [source] at raw fits
    have choice : plan.choose (nativeCaptureSubst newValues) witnesses =
        Subst.lift_l (.skipN .refl later.length) (nativeCaptureSubst newValues) := by
      rw [literal, prefix_choose]
      exact nativePrefixPlan_captures _ _ _ (by simpa only [source, List.length_append] using newLength)
    rw [choice]
    exact ⟨Ctx.SubstEq.nativePrefix raw, fits.nativePrefix (List.range declared.length)⟩
  | @index n level declared plan captures locals available domain natural position support input footprint
      previous formation lookup needed domainCode resources typed alignment declaredCode closed localNeeds bounded covered ih =>
    cases witnessesTyped with
    | cons tailTyped _ headTyped =>
      obtain ⟨raw, fits⟩ := ih witnesses.tail tailTyped agree.1
      obtain ⟨entry⟩ := argumentFits.forward.entry position ⟨n, input⟩ needed natural lookup
      have pair := alignment.related henv typed declaredCode entry.related
      have newFits := fits.pushGraded henv hscoped hTarget closed
        (earlier formation target locals _ _ available closed hTarget raw fits).1
        domainCode resources typed pair localNeeds bounded covered
      exact ⟨.cons raw (formation.defeq.mono hle) (alignment.path.cast (rawArguments.lookup lookup)),
        newFits⟩
  | @proof declared plan captures locals available domain witness previous formation inhabitant
      localNeeds n bounded empty ih =>
    cases witnessesTyped with
    | cons tailTyped _ headTyped =>
      obtain ⟨raw, fits⟩ := ih witnesses.tail tailTyped agree
      have scope := formation.closedN henv (CtxWF.closed henv tailTyped.wf)
      have actualDomain : domain.subst (plan.choose (nativeCaptureSubst newValues) witnesses.tail) =
          domain.subst witnesses.tail := subst_congr_closedN scope (plan.choose_agrees agree)
      have domains := formation.substDF henv raw.wf hTarget raw
      have actualTyped : env.HasType U target witnesses.head
          (domain.subst (plan.choose (nativeCaptureSubst newValues) witnesses.tail)) :=
        actualDomain.symm ▸ headTyped
      have pair : env.IsDefEq U target witness witnesses.head (domain.subst captures) :=
        .proofIrrel domains.hasType.1 inhabitant (.defeqDF domains.symm actualTyped)
      have leftCert : CodeCert env U registry target locals captures domain
          (Profile.empty (n := n)) [] := .seed .empty (.empty (.sort true))
      have rightCert : CodeCert env U registry target locals
          (plan.choose (nativeCaptureSubst newValues) witnesses.tail) domain
          (Profile.empty (n := n)) [] := .seed .empty (.empty (.sort true))
      have forward : Related env U registry target witness witnesses.head (domain.subst captures)
          (Profile.empty (n := n)) .empty := by
        apply Related.of_singletons
        intro atom member
        cases member
      have backward : Related env U registry target witnesses.head witness
          (domain.subst (plan.choose (nativeCaptureSubst newValues) witnesses.tail))
          (Profile.empty (n := n)) .empty := by
        apply Related.of_singletons
        intro atom member
        cases member
      exact ⟨.cons raw formation pair,
        fits.pushCertificates henv hTarget leftCert rightCert
          (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
          (.empty .empty) (.empty .empty) forward backward localNeeds bounded
          (fun need member atom atomMember => (empty need member atom atomMember).elim)⟩

/-- Transfer the actual original RHS observer to the caller's capture tuple.
The returned observation uses that tuple literally; scoped realization
agreement removes only the irrelevant tail of the finite capture map. -/
theorem NativeSupportedReplay.chosenTerminal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {target argumentSource : List VExpr} {argumentLocals : List Nat}
    {arguments : Subst} {argumentAvailable : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (newValues : List VExpr) (newLength : newValues.length = argumentSource.length)
    (rawArguments : Ctx.SubstEq env U target arguments (nativeCaptureSubst newValues) argumentSource)
    (argumentFits : PairedFits env U registry argumentSource target argumentLocals
      arguments (nativeCaptureSubst newValues) argumentAvailable)
    {declared : List VExpr} {plan : CapturePlan declared} {captures : Subst}
    {locals : List Nat} {available : Valuation}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable declared plan captures locals available)
    (witnesses : Subst)
    (witnessesTyped : Ctx.SubstEq env U target witnesses witnesses declared)
    (agree : plan.IndexAgreement (nativeCaptureSubst newValues) witnesses)
    (closed : available.AtomClosed)
    {rhs assigned : VExpr} (original : sourceEnv.IsDefEqStrong U declared rhs rhs assigned)
    {demand : Profile n} {footprint : Footprint}
    (body : Obs env U registry target locals captures rhs demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals captures witnesses
      available rhs rhs assigned demand) := by
  obtain ⟨raw, fits⟩ := replay.chosen henv hscoped hle (fun H => earlier H) hTarget
    newValues newLength rawArguments argumentFits witnesses witnessesTyped agree
  obtain ⟨result⟩ := (earlier original target locals captures
    (plan.choose (nativeCaptureSubst newValues) witnesses) available closed hTarget raw fits).1 body resources
  have scope := (original.defeq.mono hle).closedN henv (CtxWF.closed henv witnessesTyped.wf)
  have agree := plan.choose_agrees agree
  have equal : rhs.subst (plan.choose (nativeCaptureSubst newValues) witnesses) = rhs.subst witnesses :=
    subst_congr_closedN scope agree
  exact ⟨{ result with
    observation := result.observation.realizePrefix scope witnesses agree
    related := by simpa only [equal] using result.related
    rawRelated := by simpa only [equal] using result.rawRelated }⟩

end Lean4Lean.AnchoredSource.Adapted
