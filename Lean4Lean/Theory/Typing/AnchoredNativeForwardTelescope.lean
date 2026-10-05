import Lean4Lean.Theory.Typing.AnchoredNativeLambdaAlignment
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSubstitution
import Lean4Lean.Theory.Typing.NativeTelescope

/-! Forward source reconstruction through an original shared lambda
telescope. Body observations may grow in grade; the checked lambda adapter
preserves the caller's exact request and finite external resources. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

/-- Internal telescope motive. The declaration theorem supplies the terminal
producer from its actual consumed native plan and original capture origins. -/
def NativeEquationForward (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source : List VExpr) (left right : VExpr) : Prop :=
  ∀ {assigned structural} (original : sourceEnv.HasTypeStrong U source left assigned structural)
    {target locals σ available}, available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ σ source →
    PairedFits env U registry source target locals σ σ available →
    ∀ {n} {demand : Profile n} {footprint},
    Obs env U registry target locals σ left demand footprint → footprint.Available available →
    Nonempty (GradedResult env U registry target locals σ available right demand)

private theorem forward_lambda
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {source : List VExpr} {A left right : VExpr}
    (next : NativeEquationForward sourceEnv env U registry (A :: source) left right)
    {assigned structural}
    (original : sourceEnv.HasTypeStrong U source (.lam A left) assigned structural)
    {target locals σ available} (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {n} {demand : Profile n} {footprint}
    (observation : Obs env U registry target locals σ (.lam A left) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedResult env U registry target locals σ available (.lam A right) demand) := by
  match observation with
  | .empty => exact ⟨.exact .empty (fun _ _ h => nomatch h) (fun _ h => nomatch h)⟩
  | .lam (key := key) (bodyFootprint := bodyFootprint) domain guard body pack covered =>
    obtain ⟨origin⟩ := HasTypeStrong.originalLambdaOrigin earlier original rfl
    have domainAvailable := fun i need hm => resources i need (List.mem_append_left _ hm)
    have outsideAvailable := fun i need hm => resources i need (List.mem_append_right _ hm)
    let localNeeds := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
    have localClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
    have bodyAvailable := pack.available_atomized_localNeeds outsideAvailable
    obtain ⟨raw, _, _, _, _, _, _, anchor⟩ := guard.anchor
    have arguments := Related.convert henv guard.inputTyped guard.domains anchor
    have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons key.anchor) (A :: source) :=
      .cons substitutions (origin.domainStrong.defeq.mono hle) (guard.path.cast raw)
    have localFits := fits.pushDiagonal henv hTarget domain domainAvailable guard.inputTyped arguments
      localNeeds (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
    obtain ⟨changed⟩ := next origin.bodyTyping localClosed hTarget paired localFits body bodyAvailable
    exact changed.lam henv hscoped hTarget closed domain domainAvailable guard localNeeds
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha)) localClosed
  | .union first second =>
    obtain ⟨first'⟩ := forward_lambda henv hscoped hle earlier next original
      closed hTarget substitutions fits first
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨second'⟩ := forward_lambda henv hscoped hle earlier next original
      closed hTarget substitutions fits second
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨first'.union henv hscoped hTarget second'⟩
  | .view child view =>
    obtain ⟨changed⟩ := forward_lambda henv hscoped hle earlier next original
      closed hTarget substitutions fits child resources
    exact ⟨changed.view henv hscoped hTarget view⟩
  | .pad child =>
    obtain ⟨changed⟩ := forward_lambda henv hscoped hle earlier next original
      closed hTarget substitutions fits child resources
    exact ⟨changed.pad henv hscoped hTarget⟩
  | .unpad child =>
    obtain ⟨changed⟩ := forward_lambda henv hscoped hle earlier next original
      closed hTarget substitutions fits child resources
    exact ⟨changed.unpad⟩
  | .rowShift child =>
    obtain ⟨changed⟩ := forward_lambda henv hscoped hle earlier next original
      closed hTarget substitutions fits child resources
    exact ⟨(changed.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn _ _)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

/-- Only original binder typing children are used to extend the paired
substitution. No assigned-type inversion or synthesized adequacy call occurs. -/
theorem NativeEquationForward.underTelescope
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    (domains : List VExpr) {source : List VExpr} {left right : VExpr}
    (terminal : NativeEquationForward sourceEnv env U registry
      (domains.reverse ++ source) left right) :
    NativeEquationForward sourceEnv env U registry source
      (wrapLams domains left) (wrapLams domains right) := by
  induction domains generalizing source with
  | nil => exact terminal
  | cons A domains ih =>
    apply forward_lambda henv hscoped hle earlier
    apply ih
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at terminal
    exact terminal

end Lean4Lean.AnchoredSource.Adapted
