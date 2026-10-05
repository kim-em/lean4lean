import Lean4Lean.Theory.Typing.AnchoredEarlierFunctionDisplay
import Lean4Lean.Theory.Typing.AnchoredLiteralFunctionDisplay
import Lean4Lean.Theory.Typing.AnchoredTraceTermZero

/-! The function step of concrete proof-generating trace expansion. Native
proof slots remain in the actual application frame; only duplicate type
exposure slots are contracted by the closed earlier-display theorem. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem frontMap (ρ : Lift) (front : List VExpr) :
    (Lift.skipN .refl front.length).comp (ρ.consN front.length) =
      ρ.comp (.skipN .refl (renameAdded ρ front).length) := by
  simp only [renameAdded_length, Lift.skipN_comp_consN, Lift.refl_comp,
    Lift.comp_skipN, Lift.comp]

theorem FunctionBehavior.prependEndpoints
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (lower : ∀ (Γ front : List VExpr) (le re l r type : VExpr) (value support : Profile n),
      TraceEndpoint registry front le l → TraceEndpoint registry front re r →
      ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length) →
      env.IsDefEq U (front ++ Γ) (le.lift' (.skipN .refl front.length)) l
        (type.lift' (.skipN .refl front.length)) →
      env.IsDefEq U (front ++ Γ) (re.lift' (.skipN .refl front.length)) r
        (type.lift' (.skipN .refl front.length)) →
      Related env U registry (front ++ Γ) l r (type.lift' (.skipN .refl front.length))
        (value.rename (.skipN .refl front.length)) (support.rename (.skipN .refl front.length)) →
      Related env U registry Γ le re type value support)
    {Γ front : List VExpr} {left right leftResult rightResult type : VExpr}
    {key : Key n} {output : Atom n} {support : Profile (n + 1)}
    (leftTrace : TraceEndpoint registry front left leftResult)
    (rightTrace : TraceEndpoint registry front right rightResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftEq : env.IsDefEq U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult (type.lift' (.skipN .refl front.length)))
    (rightEq : env.IsDefEq U (front ++ Γ)
      (right.lift' (.skipN .refl front.length)) rightResult (type.lift' (.skipN .refl front.length)))
    (H : Related env U registry (front ++ Γ) leftResult rightResult
      (type.lift' (.skipN .refl front.length))
      ((Profile.fn key output).rename (.skipN .refl front.length))
      (support.rename (.skipN .refl front.length))) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output support := by
  obtain ⟨frame, frameMap⟩ := generated.toEmbedding henv
  have H' : Related env U registry (front ++ Γ) leftResult rightResult
      (type.lift' frame.liftMap) ((Profile.fn key output).rename frame.liftMap)
      (support.rename frame.liftMap) := by simpa only [frameMap] using H
  have proofSection : ProofInsertion env U Γ (front ++ Γ) frame.liftMap := by
    simpa only [frameMap] using generated
  have base := H'.drop henv hscoped frame proofSection
  rw [frame.leftInv] at base
  have model := base.functionBehavior henv hscoped generated.baseWF
  obtain ⟨chosen⟩ := model.literalDisplay henv
  refine ⟨model.1, chosen.A, chosen.B, chosen.domain, chosen.rows, chosen.resultType,
    chosen.typeMember, chosen.rowMember, chosen.typed, chosen.display, ?_⟩
  intro Δ ρ future x y admitted
  let ν := chosen.display.map.comp ρ
  let newFront := renameAdded ν front
  let skip : Lift := .skipN .refl newFront.length
  have total : FutureInsertion env U Γ Δ ν := chosen.insertion.toFuture.comp future henv
  obtain ⟨newGenerated, extended⟩ := generated.renameFront front total henv
  have newGenerated' : ProofInsertion env U Δ (newFront ++ Δ) skip := by
    simpa only [newFront, skip, renameAdded_length] using newGenerated
  have moved := H.future henv extended
  have moved' : Related env U registry (newFront ++ Δ)
      (leftResult.lift' (ν.consN front.length)) (rightResult.lift' (ν.consN front.length))
      (type.lift' (chosen.display.map.comp (ρ.comp skip)))
      (.fn (key.rename (chosen.display.map.comp (ρ.comp skip)))
        (output.rename (chosen.display.map.comp (ρ.comp skip))))
      ((support.rename ν).rename skip) := by
    simpa only [← lift'_comp, ← Profile.rename_comp, frontMap, Profile.fn,
      Profile.rename_singleton, Atom.rename_fn, ← Key.rename_comp, ← Atom.rename_comp, ν, newFront, skip, Lift.comp_assoc] using moved
  have arg := Admitted.future henv newGenerated'.toFuture admitted
  have arg' : Admitted env U registry (newFront ++ Δ)
      (key.rename (chosen.display.map.comp (ρ.comp skip))) (x.lift' skip) (y.lift' skip) := by
    simpa only [← Key.rename_comp, Lift.comp_assoc] using arg
  obtain ⟨first, second, cross⟩ := moved'.atEarlierDisplay henv hscoped chosen.display
    chosen.rowMember chosen.typed (future.comp newGenerated'.toFuture henv) arg'
  have rawL : env.IsDefEq U (newFront ++ Δ) ((left.lift' ν).lift' skip)
      (leftResult.lift' (ν.consN front.length)) ((type.lift' ν).lift' skip) := by
    simpa only [← lift'_comp, frontMap, ν, skip, newFront] using leftEq.weak' henv extended.weakening
  have rawR : env.IsDefEq U (newFront ++ Δ) ((right.lift' ν).lift' skip)
      (rightResult.lift' (ν.consN front.length)) ((type.lift' ν).lift' skip) := by
    simpa only [← lift'_comp, frontMap, ν, skip, newFront] using rightEq.weak' henv extended.weakening
  have piPath : TypeConversion env U (newFront ++ Δ) ((type.lift' ν).lift' skip)
      (.forallE ((chosen.display.leftDomain.lift' ρ).lift' skip)
        ((chosen.display.leftBody.lift' ρ.cons).lift' skip.cons)) := by
    simpa only [ν, lift', lift'_comp] using
      (chosen.display.leftExposure.sound.weak' henv future.weakening).weak' henv newGenerated'.weakening
  have piL := piPath.cast rawL
  have piR := piPath.cast rawR
  obtain ⟨_, _, _, _, rowPath, _⟩ :=
    chosen.display.rowDomains key chosen.resultType chosen.rowMember
  have rawArg : env.IsDefEq U Δ x y (chosen.display.leftDomain.lift' ρ) := by
    apply (rowPath.weak' henv future.weakening).cast
    simpa only [Key.rename, lift'_comp] using admitted.2.1
  have rawArg' := rawArg.weak' henv newGenerated'.weakening
  obtain ⟨level, bodyType⟩ := chosen.display.leftBodyType
  have bodyEq := (bodyType.weak' henv future.weakening.cons).instDF henv
    (future.targetWF henv) rawArg
  have bodyEq' := bodyEq.weak' henv newGenerated'.weakening
  have lx := IsDefEq.appDF piL rawArg'.hasType.1
  have ly := IsDefEq.appDF piL rawArg'.hasType.2
  have rx := IsDefEq.appDF piR rawArg'.hasType.1
  have ry := IsDefEq.appDF piR rawArg'.hasType.2
  simp only [lift'_inst_hi] at bodyEq'
  have ly := IsDefEq.defeqDF bodyEq'.symm ly
  have ry := IsDefEq.defeqDF bodyEq'.symm ry
  have tl := leftTrace.rename hscoped ν
  have tr := rightTrace.rename hscoped ν
  have liftSkip (e : VExpr) : e.lift' skip = e.liftN newFront.length :=
    lift'_consN_skipN (k := 0)
  have finish {a b aResult bResult u v : VExpr}
      (ta : TraceEndpoint registry newFront a aResult)
      (tb : TraceEndpoint registry newFront b bResult)
      (ea : env.IsDefEq U (newFront ++ Δ)
        ((VExpr.app a u).lift' skip) (.app aResult (u.liftN newFront.length))
        (((chosen.display.leftBody.lift' ρ.cons).inst x).lift' skip))
      (eb : env.IsDefEq U (newFront ++ Δ)
        ((VExpr.app b v).lift' skip) (.app bResult (v.liftN newFront.length))
        (((chosen.display.leftBody.lift' ρ.cons).inst x).lift' skip))
      (h : Related env U registry (newFront ++ Δ)
        (.app aResult (u.lift' skip)) (.app bResult (v.lift' skip))
        ((chosen.display.leftBody.lift' (ρ.comp skip).cons).inst (x.lift' skip))
        (.singleton (output.rename (chosen.display.map.comp (ρ.comp skip))))
        (chosen.resultType.rename (chosen.display.map.comp (ρ.comp skip)))) :
      Related env U registry Δ (.app a u) (.app b v)
        ((chosen.display.leftBody.lift' ρ.cons).inst x)
        (.singleton (output.rename ν)) (chosen.resultType.rename ν) := by
    apply lower Δ newFront _ _ _ _ _ _ _ (ta.app u) (tb.app v) newGenerated' ea eb
    simpa only [liftSkip u, liftSkip v, Profile.rename_singleton,
      Atom.rename_comp, Profile.rename_comp, ν, Lift.comp_assoc, lift'_inst_hi,
      ← lift'_comp, skip, Lift.comp] using h
  refine ⟨finish tl tl ?_ ?_ first, finish tr tr ?_ ?_ second, finish tl tr ?_ ?_ cross⟩
  all_goals
    first
    | simpa only [lift', liftSkip x, liftSkip y, lift'_inst_hi] using lx
    | simpa only [lift', liftSkip x, liftSkip y, lift'_inst_hi] using ly
    | simpa only [lift', liftSkip x, liftSkip y, lift'_inst_hi] using rx
    | simpa only [lift', liftSkip x, liftSkip y, lift'_inst_hi] using ry

end Lean4Lean.AnchoredSemantics
