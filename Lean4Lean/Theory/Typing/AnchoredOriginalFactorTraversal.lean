import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceFactorization
import Lean4Lean.Theory.Typing.AnchoredOriginalEndpointFactor

/-! The actual inverse-substitution traversal, retaining an original typing
location for EVERY removed argument observation. The locations follow actual
EndpointRef exposure; conversion wrappers are retained at whole cuts and
peeled only for structural app/lam/Pi descent. Closed source heads retain their
plans intact, exactly as in Obs.factorInst. Source proof environments remain
independent of the observation's target environment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false

/-- The exact query before source reflection. Its original realization and
whole observation remain available for typed closure reindexing at the cut's
actual assigned type. This record does not assert that its internal typings
can be reflected to the argument's source context. -/
structure WholeCutQuery
    {sourceEnv env : VEnv} {U : Nat} {rootSource : List VExpr} {rootExpression rootType : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {argument : VExpr} {baseDepth : Nat}
    (origin : OriginalEndpointFactor.CutOriginAt root boundary argument baseDepth)
    (registry : CanonicalHead.Registry) (Γ : List VExpr) (σ : Subst)
    (demand : Profile n) (argumentFootprint : Footprint) where
  locals : List Nat
  realization : Subst
  footprint : Footprint
  observation : Obs env U registry Γ locals realization origin.expression demand footprint
  tail_eq : Subst.lift_l (.skipN .refl origin.depth) realization = σ
  footprint_eq : footprint = argumentFootprint.sourceLift (.skipN .refl origin.depth)

/-- The retained full-context query and the reflected argument use the
same target expression; the source assigned type is intentionally retained. -/
theorem WholeCutQuery.realized
    {origin : OriginalEndpointFactor.CutOriginAt root boundary argument baseDepth}
    (whole : WholeCutQuery (env := env) origin registry Γ σ demand argumentFootprint) :
    origin.expression.subst whole.realization = argument.subst σ := by
  rw [origin.expression_eq, subst_lift', whole.tail_eq]

inductive LocatedFootprintAt
    {sourceEnv env : VEnv} {U : Nat} {rootSource : List VExpr} {rootExpression rootType : VExpr}
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (boundary : List VExpr) (registry : CanonicalHead.Registry) (Γ : List VExpr) (locals : List Nat)
    (σ : Subst) (argument : VExpr) (baseDepth depth : Nat) : Footprint → Footprint → Type where
  | nil : LocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth [] []
  | keep (index : Nat) (need : Need)
      (tail : LocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth before after) :
      LocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth
        ((index, need) :: before) ((insertIndex depth index, need) :: after)
  | cut {demand : Profile n} {argumentFootprint : Footprint}
      (origin : OriginalEndpointFactor.CutOriginAt root boundary argument baseDepth)
      (observation : Obs env U registry Γ locals σ argument demand argumentFootprint)
      (whole : WholeCutQuery (env := env) origin registry Γ σ demand argumentFootprint)
      (tail : LocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth before after) :
      LocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth
        (shiftFootprint depth argumentFootprint ++ before) ((depth, ⟨n, demand⟩) :: after)

abbrev LocatedFootprint
    {sourceEnv env : VEnv} {U : Nat} {rootSource : List VExpr} {rootExpression rootType : VExpr}
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (registry : CanonicalHead.Registry) (Γ : List VExpr) (locals : List Nat)
    (σ : Subst) (argument : VExpr) (baseDepth depth : Nat) :=
  LocatedFootprintAt (env := env) root [] registry Γ locals σ argument baseDepth depth

noncomputable def LocatedFootprintAt.erase
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (trace : LocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth before after) :
    InstFootprint env U registry Γ locals σ argument depth before after := by
  induction trace with
  | nil => exact .nil
  | keep index need _ ih => exact .keep index need ih
  | cut _ observation _ _ ih => exact .cut observation ih

noncomputable def LocatedFootprintAt.append
    (first : LocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth before₁ after₁)
    (second : LocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth before₂ after₂) :
    LocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth
      (before₁ ++ before₂) (after₁ ++ after₂) := by
  induction first with
  | nil => exact second
  | keep index need tail ih => exact .keep index need ih
  | cut origin observation whole tail ih =>
    simpa only [List.append_assoc, List.cons_append] using LocatedFootprintAt.cut origin observation whole ih

private theorem BinderPack.strip_external
    (pack : BinderPack n input (before.sourceLift (.skip .refl) ++ required) outside) :
    ∃ rest, BinderPack n input required rest ∧ outside = before ++ rest := by
  induction before generalizing outside with
  | nil => exact ⟨outside, pack, rfl⟩
  | cons entry tail ih =>
    obtain ⟨index, need⟩ := entry
    cases pack with
    | external _ _ rest =>
      obtain ⟨outside, normal, he⟩ := ih rest
      exact ⟨outside, normal, congrArg (List.cons (index, need)) he⟩

theorem LocatedFootprintAt.underBinder
    (factor : LocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth (depth + 1) before after)
    (pack : BinderPack n input before outside) :
    ∃ newOutside, BinderPack n input after newOutside ∧
      Nonempty (LocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth outside newOutside) := by
  induction factor generalizing input outside with
  | nil => cases pack; exact ⟨[], .nil, ⟨.nil⟩⟩
  | keep index need tail ih =>
    cases index with
    | zero =>
      cases pack with
      | «local» _ bound rest =>
        obtain ⟨newOutside, normal, factor⟩ := ih rest
        exact ⟨newOutside, by simpa only [insertIndex_zero] using BinderPack.local need bound normal,
          factor⟩
    | succ index =>
      cases pack with
      | external _ _ rest =>
        obtain ⟨newOutside, normal, ⟨factor⟩⟩ := ih rest
        exact ⟨(insertIndex depth index, need) :: newOutside,
          by simpa only [insertIndex_succ] using BinderPack.external _ need normal,
          ⟨LocatedFootprintAt.keep index need factor⟩⟩
  | cut origin observation whole tail ih =>
    rw [shiftFootprint_succ] at pack
    obtain ⟨rest, normal, he⟩ := BinderPack.strip_external pack
    obtain ⟨newOutside, normal', ⟨factor⟩⟩ := ih normal
    subst outside
    exact ⟨(depth, _) :: newOutside, .external depth _ normal',
      ⟨LocatedFootprintAt.cut origin observation whole factor⟩⟩

/-- Maximum captured closure cost among the cuts retained by this traversal. -/
def LocatedFootprintAt.cost
    (trace : LocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth before after)
    (initial : List Closure) : Nat :=
  match trace with
  | .nil => 0
  | .keep _ _ tail => tail.cost initial
  | .cut origin _ _ tail => max
      (Closure.close origin.view.origin (origin.location.environment initial)).cost
      (tail.cost initial)

/-- The bound is established during traversal against the selected input
closure, including its actual captured binder environment. -/
inductive BoundedLocatedFootprintAt
    {sourceEnv env : VEnv} {U : Nat} {rootSource : List VExpr} {rootExpression rootType : VExpr}
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (boundary : List VExpr) (registry : CanonicalHead.Registry) (Γ : List VExpr) (locals : List Nat)
    (σ : Subst) (argument : VExpr) (baseDepth depth : Nat)
    (budget : List Closure → Nat) : Footprint → Footprint → Type where
  | nil : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget [] []
  | keep (index : Nat) (need : Need)
      (tail : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after) :
      BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget
        ((index, need) :: before) ((insertIndex depth index, need) :: after)
  | cut {demand : Profile n} {argumentFootprint : Footprint}
      (origin : OriginalEndpointFactor.CutOriginAt root boundary argument baseDepth)
      (observation : Obs env U registry Γ locals σ argument demand argumentFootprint)
      (whole : WholeCutQuery (env := env) origin registry Γ σ demand argumentFootprint)
      (bounded : ∀ initial, (Closure.close origin.view.origin
        (origin.location.environment initial)).cost ≤ budget initial)
      (tail : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after) :
      BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget
        (shiftFootprint depth argumentFootprint ++ before) ((depth, ⟨n, demand⟩) :: after)

abbrev BoundedLocatedFootprint
    {sourceEnv env : VEnv} {U : Nat} {rootSource : List VExpr} {rootExpression rootType : VExpr}
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (registry : CanonicalHead.Registry) (Γ : List VExpr) (locals : List Nat)
    (σ : Subst) (argument : VExpr) (baseDepth depth : Nat) (budget : List Closure → Nat) :=
  BoundedLocatedFootprintAt (env := env) root [] registry Γ locals σ argument baseDepth depth budget

noncomputable def BoundedLocatedFootprintAt.erase
    (trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after) :
    LocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth before after := by
  induction trace with
  | nil => exact .nil
  | keep index need _ ih => exact .keep index need ih
  | cut origin observation whole _ _ ih => exact .cut origin observation whole ih

theorem BoundedLocatedFootprintAt.cost_le
    (trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after)
    (initial : List Closure) : trace.erase.cost initial ≤ budget initial := by
  induction trace with
  | nil => exact Nat.zero_le _
  | keep _ _ _ ih => exact ih
  | cut _ _ _ bounded _ ih => exact Nat.max_le.mpr ⟨bounded initial, ih⟩

noncomputable def BoundedLocatedFootprintAt.weaken
    (trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after)
    (bound : ∀ initial, budget initial ≤ larger initial) :
    BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth larger before after := by
  induction trace with
  | nil => exact .nil
  | keep index need _ ih => exact .keep index need ih
  | cut origin observation whole bounded _ ih =>
    exact .cut origin observation whole (fun initial => Nat.le_trans (bounded initial) (bound initial)) ih

noncomputable def BoundedLocatedFootprintAt.append
    (first : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before₁ after₁)
    (second : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before₂ after₂) :
    BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget
      (before₁ ++ before₂) (after₁ ++ after₂) := by
  induction first with
  | nil => exact second
  | keep index need _ ih => exact .keep index need ih
  | cut origin observation whole bounded _ ih =>
    simpa only [List.append_assoc, List.cons_append] using
      BoundedLocatedFootprintAt.cut origin observation whole bounded ih

theorem BoundedLocatedFootprintAt.underBinder
    (factor : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth (depth + 1) budget before after)
    (pack : BinderPack n input before outside) :
    ∃ newOutside, BinderPack n input after newOutside ∧
      Nonempty (BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget outside newOutside) := by
  induction factor generalizing input outside with
  | nil => cases pack; exact ⟨[], .nil, ⟨.nil⟩⟩
  | keep index need tail ih =>
    cases index with
    | zero =>
      cases pack with
      | «local» _ bound rest =>
        obtain ⟨newOutside, normal, factor⟩ := ih rest
        exact ⟨newOutside, by simpa only [insertIndex_zero] using BinderPack.local need bound normal,
          factor⟩
    | succ index =>
      cases pack with
      | external _ _ rest =>
        obtain ⟨newOutside, normal, ⟨factor⟩⟩ := ih rest
        exact ⟨(insertIndex depth index, need) :: newOutside,
          by simpa only [insertIndex_succ] using BinderPack.external _ need normal,
          ⟨BoundedLocatedFootprintAt.keep index need factor⟩⟩
  | cut origin observation whole bounded tail ih =>
    rw [shiftFootprint_succ] at pack
    obtain ⟨rest, normal, he⟩ := BinderPack.strip_external pack
    obtain ⟨newOutside, normal', ⟨factor⟩⟩ := ih normal
    subst outside
    exact ⟨(depth, _) :: newOutside, .external depth _ normal',
      ⟨BoundedLocatedFootprintAt.cut origin observation whole bounded factor⟩⟩

private theorem comp_cons (replacement realization : Subst) (anchor : VExpr) :
    replacement.lift.comp (realization.cons anchor) =
      (replacement.comp realization).cons anchor := by
  funext i
  cases i <;> simp [Subst.comp, Subst.lift, Subst.cons]

private theorem tail_cons (depth : Nat) (τ σ : Subst) (anchor : VExpr)
    (tail : Subst.lift_l (.skipN .refl depth) τ = σ) :
    Subst.lift_l (.skipN .refl (depth + 1)) (τ.cons anchor) = σ := by
  rw [← tail]
  funext i
  simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.cons, Nat.add_comm]

private theorem LambdaGuard.factorInstLocated
    (guard : LambdaGuard env U registry Γ τ (annotation.inst argument depth) key support) :
    LambdaGuard env U registry Γ ((Subst.one argument).liftN depth |>.comp τ)
      annotation key support := by
  refine ⟨guard.inputTyped, guard.formed, ?_, ?_, guard.anchor⟩
  · simpa only [instN_eq, subst_subst] using guard.path
  · simpa only [instN_eq, subst_subst] using guard.domains

private theorem PiGuard.factorInstLocated
    (guard : PiGuard env U Γ τ (A.inst argument depth) (B.inst argument (depth + 1)) C D) :
    PiGuard env U Γ ((Subst.one argument).liftN depth |>.comp τ) A B C D := by
  constructor
  · simpa only [instN_eq, subst_subst] using guard.domainPath
  · simpa only [instN_eq, subst_subst, Subst.liftN, Subst.comp_lift] using guard.bodyPath

private theorem Obs.cutArgument
    (observation : Obs env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (innerPrefix : List VExpr) (prefixSplit : location.binderPrefix = innerPrefix ++ boundary)
    {baseDepth : Nat} (depthEq : depth = baseDepth + innerPrefix.length)
    (he : expression = (VExpr.bvar depth).inst argument depth)
    (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (Obs env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) (.bvar depth) demand required) ∧
      Nonempty (BoundedLocatedFootprintAt (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  have he' : expression = argument.lift' (.skipN .refl depth) := by
    rw [he]
    simp only [inst, instVar, Nat.lt_irrefl, ite_false, ite_true]
    exact (lift'_consN_skipN (k := 0)).symm
  let cut : OriginalEndpointFactor.CutOriginAt root boundary argument baseDepth :=
    ⟨source, expression, assigned, typing, location, depth, he', innerPrefix, prefixSplit, depthEq⟩
  obtain ⟨required, ⟨original⟩, hf⟩ := observation.reflectSource _ he' baseLocals
  rw [tail] at original
  let whole : WholeCutQuery (env := env) cut registry Γ σ demand required :=
    ⟨locals, τ, footprint, observation, tail, hf⟩
  refine ⟨[(depth, ⟨_, demand⟩)], ⟨.var newLocals _ depth demand⟩, ?_⟩
  rw [hf, ← shiftFootprint_sourceLift]
  exact ⟨by simpa only [List.append_nil] using BoundedLocatedFootprintAt.cut cut original whole (fun _ => Nat.le_refl _) BoundedLocatedFootprintAt.nil⟩

private theorem const_inst_inv
    {expression argument : VExpr} {depth : Nat}
    (he : VExpr.const name levels = expression.inst argument depth)
    (hne : expression ≠ .bvar depth) : expression = .const name levels := by
  cases expression <;> simp only [inst, reduceCtorEq, const.injEq] at he
  · simp only [instVar] at he
    split at he <;> try contradiction
    split at he <;> try contradiction
    rename_i h
    exact (hne (h ▸ rfl)).elim
  · rcases he with ⟨rfl, rfl⟩
    rfl

private theorem sort_inst_inv
    {expression argument : VExpr} {depth : Nat}
    (he : VExpr.sort level = expression.inst argument depth)
    (hne : expression ≠ .bvar depth) : expression = .sort level := by
  cases expression <;> simp only [inst, reduceCtorEq, sort.injEq] at he
  · simp only [instVar] at he
    split at he <;> try contradiction
    split at he <;> try contradiction
    rename_i h
    exact (hne (h ▸ rfl)).elim
  · exact he.symm ▸ rfl

private theorem app_inst_inv
    {expression argument : VExpr} {depth : Nat}
    (he : VExpr.app f a = expression.inst argument depth)
    (hne : expression ≠ .bvar depth) :
    ∃ f₀ a₀, expression = .app f₀ a₀ ∧ f = f₀.inst argument depth ∧ a = a₀.inst argument depth := by
  cases expression <;> simp only [inst, reduceCtorEq, app.injEq] at he
  · simp only [instVar] at he
    split at he <;> try contradiction
    split at he <;> try contradiction
    rename_i h
    exact (hne (h ▸ rfl)).elim
  · exact ⟨_, _, rfl, he⟩

private theorem lam_inst_inv
    {expression argument : VExpr} {depth : Nat}
    (he : VExpr.lam A body = expression.inst argument depth)
    (hne : expression ≠ .bvar depth) :
    ∃ A₀ body₀, expression = .lam A₀ body₀ ∧ A = A₀.inst argument depth ∧
      body = body₀.inst argument (depth + 1) := by
  cases expression <;> simp only [inst, reduceCtorEq, lam.injEq] at he
  · simp only [instVar] at he
    split at he <;> try contradiction
    split at he <;> try contradiction
    rename_i h
    exact (hne (h ▸ rfl)).elim
  · exact ⟨_, _, rfl, he⟩

private theorem pi_inst_inv
    {expression argument : VExpr} {depth : Nat}
    (he : VExpr.forallE A B = expression.inst argument depth)
    (hne : expression ≠ .bvar depth) :
    ∃ A₀ B₀, expression = .forallE A₀ B₀ ∧ A = A₀.inst argument depth ∧
      B = B₀.inst argument (depth + 1) := by
  cases expression <;> simp only [inst, reduceCtorEq, forallE.injEq] at he
  · simp only [instVar] at he
    split at he <;> try contradiction
    split at he <;> try contradiction
    rename_i h
    exact (hne (h ▸ rfl)).elim
  · exact ⟨_, _, rfl, he⟩

mutual
theorem Obs.factorInstLocatedRelative
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (innerPrefix : List VExpr) (prefixSplit : location.binderPrefix = innerPrefix ++ boundary)
    (original argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth = baseDepth + innerPrefix.length)
    (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (Obs env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original demand required) ∧
      Nonempty (BoundedLocatedFootprintAt (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  classical
  by_cases hcut : original = .bvar depth
  · subst original
    exact Obs.cutArgument observation typing location innerPrefix prefixSplit depthEq he tail baseLocals newLocals
  match observation, typing, location with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body, typing, location =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], ⟨.delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body⟩, ⟨.nil⟩⟩
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree, typing, location =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], ⟨.native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, ⟨.nil⟩⟩
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, typing, location =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], ⟨.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, ⟨.nil⟩⟩
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, typing, location =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], ⟨.constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, ⟨.nil⟩⟩
  | .var _ _ index demand, typing, location =>
    cases original <;> simp only [inst, reduceCtorEq] at he
    rename_i i
    simp only [instVar] at he
    split at he
    · have hi := VExpr.bvar.inj he
      subst index
      refine ⟨[(i, ⟨_, demand⟩)], ⟨.var newLocals _ i demand⟩, ?_⟩
      simpa only [insertIndex, if_pos ‹i < depth›] using
        (show Nonempty (BoundedLocatedFootprintAt (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
          (fun initial => (Closure.close typing.origin (location.environment initial)).cost) [(i, ⟨_, demand⟩)] [(insertIndex depth i, ⟨_, demand⟩)]) from ⟨.keep i _ .nil⟩)
    · split at he
      · rename_i hi; exact (hcut (hi ▸ rfl)).elim
      · have hi := VExpr.bvar.inj he
        subst index
        have hindex : insertIndex depth (i - 1) = i := by
          unfold insertIndex
          split <;> omega
        refine ⟨[(i, ⟨_, demand⟩)], ⟨.var newLocals _ i demand⟩, ?_⟩
        simpa only [hindex] using
          (show Nonempty (BoundedLocatedFootprintAt (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
            (fun initial => (Closure.close typing.origin (location.environment initial)).cost) [(i - 1, ⟨_, demand⟩)] [(insertIndex depth (i - 1), ⟨_, demand⟩)]) from
            ⟨.keep (i - 1) _ .nil⟩)
  | .empty, typing, location => exact ⟨[], ⟨.empty⟩, ⟨.nil⟩⟩
  | .sort relevant, typing, location =>
    obtain rfl := sort_inst_inv he hcut
    exact ⟨[], ⟨.sort relevant⟩, ⟨.nil⟩⟩
  | .app fn arg arguments admitted, typing, location =>
    obtain ⟨_, _, _, _, hu, hv, domainTyping, codomainTyping, function,
      argumentTyping, resultTyping, path, prefixEq, headBound⟩ := appView location
    obtain ⟨f₀, a₀, rfl, hfn, harg⟩ := app_inst_inv he hcut
    obtain ⟨ff, ⟨hf⟩, ⟨sf⟩⟩ := Obs.factorInstLocatedRelative (baseDepth := baseDepth) fn function (.appFunction path) innerPrefix (by simpa only [Located.binderPrefix, prefixEq] using prefixSplit) f₀ argument depth depthEq hfn σ tail baseLocals newLocals
    obtain ⟨fa, ⟨ha⟩, ⟨sa⟩⟩ := Obs.factorInstLocatedRelative (baseDepth := baseDepth) arg argumentTyping (.appArgument path) innerPrefix (by simpa only [Located.binderPrefix, prefixEq] using prefixSplit) a₀ argument depth depthEq harg σ tail baseLocals newLocals
    refine ⟨ff ++ fa, ⟨.app hf ha arguments ?_⟩, ⟨(sf.weaken (fun initial => Nat.le_trans
      (Nat.le_of_lt (binder_other_cost (by simp) (path.environment initial))) (headBound initial))).append
      (sa.weaken (fun initial => Nat.le_trans
        (Nat.le_of_lt (binder_other_cost (by simp) (path.environment initial))) (headBound initial)))⟩⟩
    simpa only [harg, instN_eq, subst_subst] using admitted
  | .lam domain guard body normal covered, typing, location =>
    obtain ⟨_, _, _, hu, hv, domainTyping, codomainTyping, bodyTyping, path, prefixEq, headBound⟩ := lamView location
    obtain ⟨A₀, body₀, rfl, hA, hb⟩ := lam_inst_inv he hcut
    obtain ⟨fd, ⟨hd⟩, ⟨sd⟩⟩ := CodeCert.factorInstLocatedRelative (baseDepth := baseDepth) domain domainTyping (.lamDomain path) innerPrefix (by simpa only [Located.binderPrefix, prefixEq] using prefixSplit) A₀ argument depth depthEq hA σ tail baseLocals newLocals
    obtain ⟨fb, ⟨hb'⟩, ⟨sb⟩⟩ := Obs.factorInstLocatedRelative (baseDepth := baseDepth) body bodyTyping (.lamBody path) (_ :: innerPrefix) (by simpa only [Located.binderPrefix, prefixEq, List.cons_append] using congrArg (List.cons _) prefixSplit) body₀ argument (depth + 1) (by simp only [List.length_cons]; omega) hb σ
      (tail_cons depth τ σ _ tail) baseLocals (Locals.push newLocals)
    rw [Subst.liftN, comp_cons] at hb'
    obtain ⟨outside, pack, ⟨so⟩⟩ := sb.underBinder normal
    rw [hA] at guard
    exact ⟨fd ++ outside, ⟨.lam hd (LambdaGuard.factorInstLocated guard) hb' pack covered⟩, ⟨(sd.weaken (fun initial => Nat.le_trans
      (Nat.le_of_lt (binder_domain_cost _ _ _ (path.environment initial))) (headBound initial))).append
      (so.weaken (fun initial => Nat.le_trans
        (Nat.le_of_lt (binder_body_cost (by simp) (path.environment initial))) (headBound initial)))⟩⟩
  | .pi domain guard bodies, typing, location =>
    obtain ⟨_, _, hu, hv, domainTyping, bodyTyping, path, prefixEq, headBound⟩ := piView location
    obtain ⟨A₀, B₀, rfl, hA, hB⟩ := pi_inst_inv he hcut
    obtain ⟨fd, ⟨hd⟩, ⟨sd⟩⟩ := CodeCert.factorInstLocatedRelative (baseDepth := baseDepth) domain domainTyping (.piDomain path) innerPrefix (by simpa only [Located.binderPrefix, prefixEq] using prefixSplit) A₀ argument depth depthEq hA σ tail baseLocals newLocals
    obtain ⟨fb, ⟨hb⟩, ⟨sb⟩⟩ := PiRows.factorInstLocatedRelative (baseDepth := baseDepth) bodies bodyTyping (.piBody path) (_ :: innerPrefix) (by simpa only [Located.binderPrefix, prefixEq, List.cons_append] using congrArg (List.cons _) prefixSplit) A₀ B₀ argument depth (by simp only [List.length_cons]; omega) hA hB σ tail baseLocals newLocals
    rw [hA, hB] at guard
    exact ⟨fd ++ fb, ⟨.pi hd (PiGuard.factorInstLocated guard) hb⟩, ⟨(sd.weaken (fun initial => Nat.le_trans
      (Nat.le_of_lt (binder_domain_cost _ _ _ (path.environment initial))) (headBound initial))).append
      (sb.weaken (fun initial => Nat.le_trans
        (Nat.le_of_lt (binder_body_cost (by simp) (path.environment initial))) (headBound initial)))⟩⟩
  | .union left right, typing, location =>
    obtain ⟨fl, ⟨hl⟩, ⟨sl⟩⟩ := Obs.factorInstLocatedRelative (baseDepth := baseDepth) left typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    obtain ⟨fr, ⟨hr⟩, ⟨sr⟩⟩ := Obs.factorInstLocatedRelative (baseDepth := baseDepth) right typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨fl ++ fr, ⟨.union hl hr⟩, ⟨sl.append sr⟩⟩
  | .view source view, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := Obs.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.view h view⟩, ⟨s⟩⟩
  | .pad source, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := Obs.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.pad h⟩, ⟨s⟩⟩
  | .unpad source, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := Obs.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.unpad h⟩, ⟨s⟩⟩
  | .rowShift source, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := Obs.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.rowShift h⟩, ⟨s⟩⟩
termination_by sizeOf observation

theorem CodeCert.factorInstLocatedRelative
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (innerPrefix : List VExpr) (prefixSplit : location.binderPrefix = innerPrefix ++ boundary)
    (original argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth = baseDepth + innerPrefix.length)
    (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (CodeCert env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original demand required) ∧
      Nonempty (BoundedLocatedFootprintAt (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  match certificate, typing, location with
  | .seed observation formed, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := Obs.factorInstLocatedRelative (baseDepth := baseDepth) observation typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.seed h formed⟩, s⟩
  | .union left right, typing, location =>
    obtain ⟨fl, ⟨hl⟩, ⟨sl⟩⟩ := CodeCert.factorInstLocatedRelative (baseDepth := baseDepth) left typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    obtain ⟨fr, ⟨hr⟩, ⟨sr⟩⟩ := CodeCert.factorInstLocatedRelative (baseDepth := baseDepth) right typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨fl ++ fr, ⟨.union hl hr⟩, ⟨sl.append sr⟩⟩
  | .pad source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.pad h⟩, s⟩
  | .familyPad source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.familyPad h⟩, s⟩
  | .unpad source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.unpad h⟩, s⟩
  | .down source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.down h⟩, s⟩
  | .map view source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.map view h⟩, s⟩
  | .select source member, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.select h member⟩, s⟩
  | .focusMinimal source minimal bound, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.focusMinimal h minimal bound⟩, s⟩
termination_by sizeOf certificate

theorem PiRows.factorInstLocatedRelative
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals τ A B ambient rows footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U (A :: source) B assigned)
    (location : Located root typing)
    (innerPrefix : List VExpr) (prefixSplit : location.binderPrefix = innerPrefix ++ boundary)
    (A₀ B₀ argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth + 1 = baseDepth + innerPrefix.length)
    (hA : A = A₀.inst argument depth) (hB : B = B₀.inst argument (depth + 1))
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (PiRows env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) A₀ B₀ ambient rows required) ∧
      Nonempty (BoundedLocatedFootprintAt (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  match bodies, typing, location with
  | .nil, typing, location => exact ⟨[], ⟨.nil⟩, ⟨.nil⟩⟩
  | .cons guard body normal covered rest, typing, location =>
    obtain ⟨fb, ⟨hb⟩, ⟨sb⟩⟩ := CodeCert.factorInstLocatedRelative (baseDepth := baseDepth) body typing location innerPrefix prefixSplit B₀ argument (depth + 1) depthEq hB σ
      (tail_cons depth τ σ _ tail) baseLocals (Locals.push newLocals)
    rw [Subst.liftN, comp_cons] at hb
    obtain ⟨outside, pack, ⟨so⟩⟩ := sb.underBinder normal
    obtain ⟨fr, ⟨hr⟩, ⟨sr⟩⟩ := PiRows.factorInstLocatedRelative (baseDepth := baseDepth) rest typing location innerPrefix prefixSplit A₀ B₀ argument depth depthEq hA hB σ tail baseLocals newLocals
    rw [hA] at guard
    exact ⟨outside ++ fr, ⟨.cons (LambdaGuard.factorInstLocated guard) hb pack covered hr⟩, ⟨so.append sr⟩⟩
termination_by sizeOf bodies
end


noncomputable def LocatedFootprint.erase
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (trace : LocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth before after) :
    InstFootprint env U registry Γ locals σ argument depth before after := LocatedFootprintAt.erase trace

noncomputable def LocatedFootprint.append
    (first : LocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth before₁ after₁)
    (second : LocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth before₂ after₂) :
    LocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth
      (before₁ ++ before₂) (after₁ ++ after₂) := LocatedFootprintAt.append first second

theorem LocatedFootprint.underBinder
    (factor : LocatedFootprint (env := env) root registry Γ locals σ argument baseDepth (depth + 1) before after)
    (pack : BinderPack n input before outside) :
    ∃ newOutside, BinderPack n input after newOutside ∧
      Nonempty (LocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth outside newOutside) := LocatedFootprintAt.underBinder factor pack

def LocatedFootprint.cost
    (trace : LocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth before after)
    (initial : List Closure) : Nat := LocatedFootprintAt.cost trace initial

noncomputable def BoundedLocatedFootprint.erase
    (trace : BoundedLocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth budget before after) :
    LocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth before after := BoundedLocatedFootprintAt.erase trace

theorem BoundedLocatedFootprint.cost_le
    (trace : BoundedLocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth budget before after)
    (initial : List Closure) : trace.erase.cost initial ≤ budget initial := BoundedLocatedFootprintAt.cost_le trace initial

noncomputable def BoundedLocatedFootprint.weaken
    (trace : BoundedLocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth budget before after)
    (bound : ∀ initial, budget initial ≤ larger initial) :
    BoundedLocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth larger before after := BoundedLocatedFootprintAt.weaken trace bound

noncomputable def BoundedLocatedFootprint.append
    (first : BoundedLocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth budget before₁ after₁)
    (second : BoundedLocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth budget before₂ after₂) :
    BoundedLocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth budget
      (before₁ ++ before₂) (after₁ ++ after₂) := BoundedLocatedFootprintAt.append first second

theorem BoundedLocatedFootprint.underBinder
    (factor : BoundedLocatedFootprint (env := env) root registry Γ locals σ argument baseDepth (depth + 1) budget before after)
    (pack : BinderPack n input before outside) :
    ∃ newOutside, BinderPack n input after newOutside ∧
      Nonempty (BoundedLocatedFootprint (env := env) root registry Γ locals σ argument baseDepth depth budget outside newOutside) := BoundedLocatedFootprintAt.underBinder factor pack

theorem Obs.factorInstLocatedBounded
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (original argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth = baseDepth + location.binderPrefix.length)
    (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (Obs env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original demand required) ∧
      Nonempty (BoundedLocatedFootprint (env := env) root registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  exact Obs.factorInstLocatedRelative (boundary := []) (baseDepth := baseDepth) observation typing location location.binderPrefix (by simp) original argument depth depthEq he σ tail baseLocals newLocals

theorem CodeCert.factorInstLocatedBounded
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (original argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth = baseDepth + location.binderPrefix.length)
    (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (CodeCert env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original demand required) ∧
      Nonempty (BoundedLocatedFootprint (env := env) root registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  exact CodeCert.factorInstLocatedRelative (boundary := []) (baseDepth := baseDepth) certificate typing location location.binderPrefix (by simp) original argument depth depthEq he σ tail baseLocals newLocals

theorem PiRows.factorInstLocatedBounded
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals τ A B ambient rows footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U (A :: source) B assigned)
    (location : Located root typing)
    (A₀ B₀ argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth + 1 = baseDepth + location.binderPrefix.length)
    (hA : A = A₀.inst argument depth) (hB : B = B₀.inst argument (depth + 1))
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (PiRows env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) A₀ B₀ ambient rows required) ∧
      Nonempty (BoundedLocatedFootprint (env := env) root registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  exact PiRows.factorInstLocatedRelative (boundary := []) (baseDepth := baseDepth) bodies typing location location.binderPrefix (by simp) A₀ B₀ argument depth depthEq hA hB σ tail baseLocals newLocals

theorem Obs.factorInstLocated
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (original argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth = baseDepth + location.binderPrefix.length)
    (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (Obs env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original demand required) ∧
      Nonempty (LocatedFootprint (env := env) root registry Γ baseLocals σ argument baseDepth depth footprint required) := by
  obtain ⟨required, certificate, ⟨trace⟩⟩ := Obs.factorInstLocatedBounded (baseDepth := baseDepth) observation typing location original argument depth depthEq he σ tail baseLocals newLocals
  exact ⟨required, certificate, ⟨trace.erase⟩⟩

theorem CodeCert.factorInstLocated
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (original argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth = baseDepth + location.binderPrefix.length)
    (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (CodeCert env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original demand required) ∧
      Nonempty (LocatedFootprint (env := env) root registry Γ baseLocals σ argument baseDepth depth footprint required) := by
  obtain ⟨required, certificate, ⟨trace⟩⟩ := CodeCert.factorInstLocatedBounded (baseDepth := baseDepth) certificate typing location original argument depth depthEq he σ tail baseLocals newLocals
  exact ⟨required, certificate, ⟨trace.erase⟩⟩

theorem PiRows.factorInstLocated
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals τ A B ambient rows footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U (A :: source) B assigned)
    (location : Located root typing)
    (A₀ B₀ argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth + 1 = baseDepth + location.binderPrefix.length)
    (hA : A = A₀.inst argument depth) (hB : B = B₀.inst argument (depth + 1))
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (PiRows env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) A₀ B₀ ambient rows required) ∧
      Nonempty (LocatedFootprint (env := env) root registry Γ baseLocals σ argument baseDepth depth footprint required) := by
  obtain ⟨required, certificate, ⟨trace⟩⟩ := PiRows.factorInstLocatedBounded (baseDepth := baseDepth) bodies typing location A₀ B₀ argument depth depthEq hA hB σ tail baseLocals newLocals
  exact ⟨required, certificate, ⟨trace.erase⟩⟩

/-- Factor at the selected original endpoint's own source context. Its
existing binder prefix is the boundary, so syntactic substitution starts at
zero even when that endpoint is a synthetic application under outer binders. -/
theorem CodeCert.factorInstAtStart
    (certificate : CodeCert env U registry Γ locals σ (B.inst argument) demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source (B.inst argument) assigned)
    (location : Located root typing) (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (CodeCert env U registry Γ newLocals
      ((Subst.one argument).comp σ) B demand required) ∧
      Nonempty (BoundedLocatedFootprintAt (env := env) root location.binderPrefix registry Γ
        baseLocals σ argument 0 0
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost)
        footprint required) := by
  exact CodeCert.factorInstLocatedRelative (baseDepth := 0) certificate typing location []
    (by simp) B argument 0 rfl rfl σ rfl baseLocals newLocals

/-- Enter inverse substitution at the actual original endpoint. The caller
supplies no intermediate typing state or path: every cut is reached from
this reference, and a whole cut retains this reference's assigned type. -/
theorem CodeCert.factorInstOriginal
    (certificate : CodeCert env U registry Γ locals σ (B.inst argument) demand footprint)
    (root : EndpointRef sourceEnv U source (B.inst argument) assigned)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (CodeCert env U registry Γ newLocals
      ((Subst.one argument).comp σ) B demand required) ∧
      Nonempty (LocatedFootprint (env := env) root registry Γ baseLocals σ argument
        0 0 footprint required) := by
  exact CodeCert.factorInstLocated (baseDepth := 0) certificate (.ref root) .here B argument 0
    rfl rfl σ rfl baseLocals newLocals

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
