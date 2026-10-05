import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceFactorArguments
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedSort

/-! Reconstruct an actual beta-redex observation at the exact requested
grade. The argument's original typing child supplies the annotation
certificate for the finite demands obtained by inverse substitution. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem one_realized (argument : VExpr) (σ : Subst) :
    (Subst.one argument).comp σ = σ.cons (argument.subst σ) := by
  funext i
  cases i <;> rfl

theorem Obs.betaExpand_atom
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A body argument : VExpr} {output : Atom n} {footprint : Footprint}
    (originalArgument : GradedJoint env U registry source argument argument A)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    (observation : Obs env U registry target locals σ (body.inst argument) (.singleton output) footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (Obs env U registry target locals σ (.app (.lam A body) argument)
      (.singleton output) required) ∧ required.Available available := by
  obtain ⟨bodyFootprint, ⟨bodyObservation⟩, ⟨factor⟩⟩ :=
    observation.factorInst body argument 0 rfl σ (by funext i; rfl) locals (Locals.push locals)
  simp only [Subst.liftN, one_realized] at bodyObservation
  obtain ⟨arguments⟩ := factor.arguments available resources n
  obtain ⟨argResult⟩ :=
    (originalArgument target locals σ σ available closed hTarget substitutions fits).1
      arguments.observation arguments.argumentAvailable
  let domain := argResult.requestedCertificate
  have typed := argResult.requestedTyped
  have related := argResult.requestedRelated henv hTarget
  have code := TypeRelated.lower henv argResult.bound argResult.typeCode
  have raw := rawArgument.subst henv substitutions hTarget
  let key : Key arguments.rank := ⟨A.subst σ, argument.subst σ, arguments.input⟩
  have admitted : Admitted env U registry target key key.anchor key.anchor :=
    ⟨raw, raw, _, typed, domain.formed, code, related, related⟩
  have guard : LambdaGuard env U registry target σ A key _ :=
    ⟨typed, domain.formed, .refl, code, admitted⟩
  have bodyHigh := bodyObservation.raise arguments.bound
  rw [raiseProfile_singleton] at bodyHigh
  have fn := Obs.lam domain guard bodyHigh arguments.pack (fun _ h => h)
  have app := Obs.app fn arguments.observation (ProfileAdapter.refl _) admitted
  have app' : Obs env U registry target locals σ (.app (.lam A body) argument)
      (raiseProfile arguments.rank arguments.bound (.singleton output))
      ((argResult.typeFootprint ++ arguments.outside) ++ arguments.argumentFootprint) := by
    rw [raiseProfile_singleton]
    exact app
  refine ⟨_, ⟨app'.lower arguments.bound⟩, ?_⟩
  intro i need hm
  rcases List.mem_append.mp hm with hm | hm
  · exact (List.mem_append.mp hm).elim
      (argResult.typeAvailable i need) (arguments.outsideAvailable i need)
  · exact arguments.argumentAvailable i need hm

theorem Obs.betaExpand
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A body argument : VExpr} {demand : Profile n} {footprint : Footprint}
    (originalArgument : GradedJoint env U registry source argument argument A)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    (observation : Obs env U registry target locals σ (body.inst argument) demand footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (Obs env U registry target locals σ (.app (.lam A body) argument)
      demand required) ∧ required.Available available := by
  induction demand generalizing footprint with
  | nil => exact ⟨[], ⟨.empty⟩, fun _ _ h => nomatch h⟩
  | cons atom rest ih =>
    obtain ⟨selected⟩ := observation.atom List.mem_cons_self
    obtain ⟨firstFootprint, ⟨first⟩, firstAvailable⟩ := selected.observation.betaExpand_atom henv
      originalArgument rawArgument closed hTarget substitutions fits
      (selected.atomizes.available_closed resources closed)
    obtain ⟨tailFootprint, ⟨tail⟩, selection⟩ := observation.subprofile
      (selected := rest) (fun _ h => List.mem_cons_of_mem _ h)
    obtain ⟨lastFootprint, ⟨last⟩, lastAvailable⟩ := ih tail
      (selection.available_closed resources closed)
    exact ⟨firstFootprint ++ lastFootprint, ⟨.union first last⟩,
      fun i need hm => (List.mem_append.mp hm).elim (firstAvailable i need) (lastAvailable i need)⟩

end Lean4Lean.AnchoredSource.Adapted
