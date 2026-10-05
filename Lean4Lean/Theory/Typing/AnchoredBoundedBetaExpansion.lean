import Lean4Lean.Theory.Typing.AnchoredBoundedFactorization
import Lean4Lean.Theory.Typing.AnchoredBoundedVariable
import Lean4Lean.Theory.Typing.AnchoredBoundedPruning
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceFactorArguments

/-! The finite formal beta opening uses only bounded genuine argument cuts
and a fixed-fuel original argument transfer. No unrestricted Joint is needed. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure BoundedFactoredArguments (current : Name → Bool) (fuel : Nat) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (argument : VExpr) (required : Footprint) (minimum : Nat) where
  rank : Nat
  bound : minimum ≤ rank
  input : Profile rank
  argumentFootprint : Footprint
  observation : Obs env U registry Γ locals σ argument input argumentFootprint
  argumentAvailable : argumentFootprint.Available available
  outside : Footprint
  pack : BinderPack rank input required outside
  outsideAvailable : outside.Available available
  observationBound : observation.nativeDepth current ≤ fuel

theorem BoundedInstFootprint.arguments
    (factor : BoundedInstFootprint current fuel env U registry Γ locals σ argument 0 before after)
    (available : Valuation) (resources : before.Available available) (minimum : Nat) :
    Nonempty (BoundedFactoredArguments current fuel env U registry Γ locals σ available argument after minimum) := by
  induction factor with
  | nil =>
    exact ⟨⟨minimum, Nat.le_refl _, .empty, [], .empty,
      (fun _ _ h => nomatch h), [], .nil, (fun _ _ h => nomatch h), by simp only [Obs.nativeDepth]; omega⟩⟩
  | keep index need rest ih =>
    obtain ⟨tail⟩ := ih (fun i need hm => resources i need (List.mem_cons_of_mem _ hm))
    exact ⟨{
      rank := tail.rank
      bound := tail.bound
      input := tail.input
      argumentFootprint := tail.argumentFootprint
      observation := tail.observation
      argumentAvailable := tail.argumentAvailable
      outside := (index, need) :: tail.outside
      pack := by simpa only [insertIndex, Nat.not_lt_zero, ite_false] using
        BinderPack.external index need tail.pack
      outsideAvailable := by
        intro i original hm
        rcases List.mem_cons.mp hm with he | hm
        · cases he; exact resources index need List.mem_cons_self
        · exact tail.outsideAvailable i original hm
      observationBound := tail.observationBound }⟩
  | @cut n before after demand argumentFootprint observation observationBound rest ih =>
    rw [shiftFootprint_zero] at resources
    obtain ⟨tail⟩ := ih (fun i need hm => resources i need (List.mem_append_right _ hm))
    let N := max n tail.rank
    have hn : n ≤ N := Nat.le_max_left _ _
    have ht : tail.rank ≤ N := Nat.le_max_right _ _
    exact ⟨{
      rank := N
      bound := Nat.le_trans tail.bound ht
      input := (raiseProfile N hn demand).union (raiseProfile N ht tail.input)
      argumentFootprint := argumentFootprint ++ tail.argumentFootprint
      observation := .union (observation.raise hn) (tail.observation.raise ht)
      argumentAvailable := by
        intro i need hm
        exact (List.mem_append.mp hm).elim
          (fun h => resources i need (List.mem_append_left _ h))
          (tail.argumentAvailable i need)
      outside := tail.outside
      pack := by
        simpa only [Need.atGrade, dif_pos hn] using
          BinderPack.local ⟨n, demand⟩ hn (tail.pack.raise ht)
      outsideAvailable := tail.outsideAvailable
      observationBound := by
        simpa only [Obs.nativeDepth, Obs.nativeDepth_raise] using Nat.max_le.mpr ⟨observationBound, tail.observationBound⟩ }⟩

@[simp] theorem Obs.nativeDepth_lower (current : Name → Bool)
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr} {footprint : Footprint}
    {n N : Nat} {demand : Profile n} (bound : n ≤ N)
    (observation : Obs env U registry Γ locals σ expression (raiseProfile N bound demand) footprint) :
    (observation.lower bound).nativeDepth current = observation.nativeDepth current := by
  induction N with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases hn : n = N + 1
    · subst n
      simp only [Obs.lower, Nat.recAux, dite_true]
      exact Obs.nativeDepth_cast current (raiseProfile_self ..) _ observation
    · simp only [Obs.lower, Nat.recAux, dif_neg hn]
      change (Obs.lower (show n ≤ N by omega) (.unpad (cast _ observation))).nativeDepth current = _
      rw [ih]
      simp only [Obs.nativeDepth]
      exact Obs.nativeDepth_cast current
        (raiseProfile_step (show n ≤ N by omega) demand) _ observation

private theorem one_realized (argument : VExpr) (σ : Subst) :
    (Subst.one argument).comp σ = σ.cons (argument.subst σ) := by
  funext i
  cases i <;> rfl

theorem Obs.betaExpandBounded_atom
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A body argument : VExpr} {output : Atom n} {footprint : Footprint}
    (originalArgument : Staged.Transfer current fuel env U registry target locals σ σ available argument argument A)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : Staged.PairedFits current fuel env U registry source target locals σ σ available)
    (observation : Obs env U registry target locals σ (body.inst argument) (.singleton output) footprint)
    (bounded : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    ∃ required, ∃ result : Obs env U registry target locals σ (.app (.lam A body) argument)
      (.singleton output) required, required.Available available ∧ result.nativeDepth current ≤ fuel := by
  have bodyData := observation.factorInstBounded body argument 0 rfl σ (by funext i; rfl)
    locals (Locals.push locals) bounded
  simp only [Subst.liftN] at bodyData
  rw [one_realized] at bodyData
  obtain ⟨bodyFootprint, bodyObservation, ⟨factor⟩, bodyBound⟩ := bodyData
  obtain ⟨arguments⟩ := factor.arguments available resources n
  obtain ⟨argResult⟩ :=
    originalArgument arguments.observation arguments.observationBound arguments.argumentAvailable
  let domain := argResult.toGradedTransferResult.requestedCertificate
  have typed := argResult.toGradedTransferResult.requestedTyped
  have related := argResult.toGradedTransferResult.requestedRelated henv hTarget
  have code := TypeRelated.lower henv argResult.bound argResult.typeCode
  have raw := rawArgument.subst henv substitutions hTarget
  let key : Key arguments.rank := ⟨A.subst σ, argument.subst σ, arguments.input⟩
  have admitted : Admitted env U registry target key key.anchor key.anchor :=
    ⟨raw, raw, _, typed, domain.formed, code, related, related⟩
  have guard : LambdaGuard env U registry target σ A key _ :=
    ⟨typed, domain.formed, .refl, code, admitted⟩
  have highData : ∃ obs : Obs env U registry target (Locals.push locals) (σ.cons (argument.subst σ))
      body (raiseProfile arguments.rank arguments.bound (.singleton output)) bodyFootprint,
      obs.nativeDepth current ≤ fuel :=
    ⟨bodyObservation.raise arguments.bound, by simpa only [Obs.nativeDepth_raise] using bodyBound⟩
  rw [raiseProfile_singleton] at highData
  obtain ⟨bodyHigh, highBound⟩ := highData
  let fn :=  Obs.lam domain guard bodyHigh arguments.pack (fun _ h => h)
  let app :=  Obs.app fn arguments.observation (ProfileAdapter.refl _) admitted
  have directBound : app.nativeDepth current ≤ fuel := by
    simp only [app, fn, Obs.nativeDepth, domain,
      GradedTransferResult.requestedCertificate, CodeCert.nativeDepth_lower]
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨argResult.certificateBound, highBound⟩, arguments.observationBound⟩
  have appData : ∃ obs : Obs env U registry target locals σ (.app (.lam A body) argument)
      (.singleton (raiseAtom arguments.rank arguments.bound output))
      ((argResult.typeFootprint ++ arguments.outside) ++ arguments.argumentFootprint),
      obs.nativeDepth current ≤ fuel := ⟨app, directBound⟩
  rw [← raiseProfile_singleton] at appData
  obtain ⟨app', appBound⟩ := appData
  refine ⟨_, app'.lower arguments.bound, ?_, ?_⟩
  · intro i need hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (List.mem_append.mp hm).elim
        (argResult.typeAvailable i need) (arguments.outsideAvailable i need)
    · exact arguments.argumentAvailable i need hm
  · simpa only [Obs.nativeDepth_lower] using appBound

theorem Obs.betaExpandBounded
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A body argument : VExpr} {demand : Profile n} {footprint : Footprint}
    (originalArgument : Staged.Transfer current fuel env U registry target locals σ σ available argument argument A)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : Staged.PairedFits current fuel env U registry source target locals σ σ available)
    (observation : Obs env U registry target locals σ (body.inst argument) demand footprint)
    (bounded : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    ∃ required, ∃ result : Obs env U registry target locals σ (.app (.lam A body) argument)
      demand required, required.Available available ∧ result.nativeDepth current ≤ fuel := by
  induction demand generalizing footprint with
  | nil => exact ⟨[], .empty, (fun _ _ h => nomatch h), by simp only [Obs.nativeDepth]; omega⟩
  | cons atom rest ih =>
    obtain ⟨selected, selectedBound⟩ := observation.atom_bounded (current := current) List.mem_cons_self
    obtain ⟨firstFootprint, first, firstAvailable, firstBound⟩ := selected.observation.betaExpandBounded_atom henv
      originalArgument rawArgument closed hTarget substitutions fits
      (Nat.le_trans selectedBound bounded) (selected.atomizes.available_closed resources closed)
    obtain ⟨tailFootprint, tail, selection, tailBound⟩ := observation.subprofile_bounded
      (current := current) (selected := rest) (fun _ h => List.mem_cons_of_mem _ h)
    obtain ⟨lastFootprint, last, lastAvailable, lastBound⟩ := ih tail
      (Nat.le_trans tailBound bounded) (selection.available_closed resources closed)
    exact ⟨firstFootprint ++ lastFootprint, .union first last,
      (fun i need hm => (List.mem_append.mp hm).elim (firstAvailable i need) (lastAvailable i need)),
      by simpa only [Obs.nativeDepth] using Nat.max_le.mpr ⟨firstBound, lastBound⟩⟩

end Lean4Lean.AnchoredSource.Adapted
