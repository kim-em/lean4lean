import Lean4Lean.Theory.Typing.AnchoredFamilySeededProducer
import Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades
import Lean4Lean.Theory.Typing.AnchoredDataRelations
import Lean4Lean.Theory.Typing.AnchoredFamilyHead

/-! Original family applications retain their actual argument children next
to the finite seeded application frames. Binary argument evidence is produced
by those children, at exactly the frozen frame inputs; it is not recovered
from raw equality of family applications. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Source provenance for every argument observation in a seeded spine.
This finite derivation records original children, not a semantic supplier. -/
inductive FamilySpinePayload (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) (name : Name) (levels : List VLevel) :
    {expression assigned : VExpr} → {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint → Prop where
  | constant : FamilySpinePayload sourceEnv env U registry source target locals σ available
      name levels (.constant lookup formation certificate resources)
  | application
      (original : OriginalTypePayload sourceEnv env U registry source a A)
      (frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before)
      {function : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
        name levels f (.forallE A B) frame.profile frame.footprint}
      (previous : FamilySpinePayload sourceEnv env U registry source target locals σ available
        name levels function) :
      FamilySpinePayload sourceEnv env U registry source target locals σ available
        name levels (.application frame function)
  | conversion
      {original : sourceEnv.IsDefEqStrong U source A B (.sort level)}
      {edge : OriginalPayload sourceEnv env U registry original}
      {certificate : CodeCert env U registry target locals σ B profile footprint}
      {transfer : CodeTransferResult env U registry target locals σ σ available B A profile}
      {term : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
        name levels expression A profile transfer.footprint}
      (previous : FamilySpinePayload sourceEnv env U registry source target locals σ available
        name levels term) :
      FamilySpinePayload sourceEnv env U registry source target locals σ available
        name levels (.conversion edge certificate transfer term)

/-- The original application tree supplies both the seeded frames and their
literal argument children in one traversal, preserving every conversion. -/
theorem HasTypeStrong.seededFamilySpine
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {expression assigned : VExpr} {structural : Bool} {name : Name} {levels : List VLevel}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (seeds : NativeSpineSeeds env U registry target locals σ available expression)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    ∃ spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
        name levels expression assigned profile footprint,
      spine.seeds = seeds ∧ FamilySpinePayload sourceEnv env U registry source target locals σ available
        name levels spine := by
  induction original generalizing n footprint with
  | const lookup hw hl hu closedType type ihClosed ihType =>
    simp only [VExpr.getAppFnArgs_const] at head
    cases head
    cases seeds
    exact ⟨.constant lookup (earlier type.refl).leftFormation certificate resources, rfl, .constant⟩
  | app hu hv domain codomain whole function argument result ihD ihC ihW ihF ihA ihR =>
    cases seeds with
    | app functionSeeds argumentSeed =>
      have argumentPayload : OriginalTypePayload sourceEnv env U registry _ _ _ :=
        ⟨argument.refl, (earlier argument.refl).joint⟩
      obtain ⟨frame, seedEq⟩ := certificate.seededApplicationInput henv hle
        argumentPayload argumentSeed closed hTarget substitutions fits resources
      obtain ⟨tail, tailEq, children⟩ := ihF substitutions fits
        (by simpa only [VExpr.getAppFnArgs_app] using head) functionSeeds frame.certificate frame.resources
      exact ⟨.application frame tail,
        by simp only [NativeSeededSpineCertificate.seeds, tailEq, seedEq],
        .application argumentPayload frame children⟩
  | base _ ih => exact ih substitutions fits head seeds certificate resources
  | defeq hu conversion leftType rightType term ihL ihR ih =>
    obtain ⟨transfer⟩ := certificate.transfer_graded henv hscoped hTarget closed
      ((earlier conversion).joint.symm target locals σ σ available closed hTarget substitutions fits).1 resources
    obtain ⟨tail, same, children⟩ := ih substitutions fits head seeds transfer.certificate transfer.available
    exact ⟨.conversion (earlier conversion) certificate transfer tail, same, .conversion children⟩
  | bvar | sort' | elim | proj | lam | forallE =>
    simp only [VExpr.getAppFnArgs] at head
    contradiction

private theorem arguments_append
    (first : FamilyArguments env U registry target keys xs ys)
    (second : FamilyArguments env U registry target more zs ws) :
    FamilyArguments env U registry target (keys ++ more) (xs ++ zs) (ys ++ ws) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

/-- The stored source observer is transferred through its original typing
child and retagged to the frame's actual domain support. -/
theorem SeededApplicationCodeInput.familyAdmission
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B a : VExpr} {result : Profile n} {before : Footprint}
    (frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before)
    (original : OriginalTypePayload sourceEnv env U registry source a A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry source target locals σ τ available) :
    RankedData.RequestAdmission env U (relations env U registry frame.collected.rank) target
      (⟨frame.key, frame.support⟩ : DataRequest (Profile frame.collected.rank)) (a.subst σ) (a.subst τ) := by
  obtain ⟨value⟩ := (original.2 target locals σ τ available closed hTarget substitutions fits).1
    frame.argumentObservation frame.argumentResources
  obtain ⟨anchor, _, typed, formed, code, self, _⟩ := frame.guard.familyAdmission henv
  have raw := (original.1.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
  exact ⟨anchor, raw, typed, formed, code, self,
    Related.retag henv typed code (value.requestedRelated henv hTarget)⟩

/-- Every parameter/index admission comes from the original argument at
that exact application position. The key list is exactly the seeded list. -/
theorem FamilySpinePayload.arguments
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {name : Name} {levels : List VLevel} {expression assigned : VExpr}
    {profile : Profile n} {footprint : Footprint}
    {spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint}
    (payload : FamilySpinePayload sourceEnv env U registry source target locals σ available name levels spine)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry source target locals σ τ available) :
    FamilyArguments env U registry target spine.familyKeys
      (expression.getAppFnArgs.2.map (·.subst σ)) (expression.getAppFnArgs.2.map (·.subst τ)) := by
  induction payload with
  | constant => exact .nil
  | application original frame previous ih =>
    simpa only [NativeSeededSpineCertificate.familyKeys, getAppFnArgs_app,
      List.map_append, List.map_singleton] using
      arguments_append ih (FamilyArguments.cons (key := ⟨frame.collected.rank, frame.key, frame.support⟩)
        (frame.familyAdmission henv hle original closed hTarget substitutions fits) .nil)
  | conversion previous ih => exact ih

end Lean4Lean.AnchoredSource.Adapted
