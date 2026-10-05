import Lean4Lean.Theory.Typing.AnchoredNativeRetelescopeContext
import Lean4Lean.Theory.Typing.AnchoredNativeSpineDemand
import Lean4Lean.Theory.Typing.AnchoredNativePlanPadding
import Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope

/-! Rebuild the actual registered telescope from a finite computational
skeleton and its whole header certificate. The skeleton stores only actual
terminal observations, selected argument keys, and literal finite demand
coverage. Domain guards and source domain certificates are constructed by
original header-child interpretation, not supplied by a semantic oracle. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

inductive NativeRetelescopeSkeleton (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels) :
    (arguments : List VExpr) → {n : Nat} → Atom n → Footprint → Type where
  | terminal {atom : Atom n}
      (leaf : NativeInitialTerminal env U registry target signature arguments (.singleton atom) footprint) :
      NativeRetelescopeSkeleton env U registry target signature arguments atom footprint
  | binder {key : Key n} {output : Atom n}
      (origin : signature.domains[arguments.length]? = some domain)
      (body : NativeRetelescopeSkeleton env U registry target signature
        (arguments ++ [key.anchor]) output bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      NativeRetelescopeSkeleton env U registry target signature arguments (n := n + 1) (AtomData.fn key output) outside
  | pad {atom : Atom n}
      (body : NativeRetelescopeSkeleton env U registry target signature arguments atom footprint) :
      NativeRetelescopeSkeleton env U registry target signature arguments (n := n + 1) (AtomData.pad atom) footprint

structure NativeRetelescopeResult (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels) (arguments : List VExpr)
    (available : Valuation) (atom : Atom n) where
  output : Atom n
  footprint : Footprint
  tree : NativeInitialTree env U registry target signature arguments (.singleton output) footprint
  resources : footprint.Available available
  view : AtomView env U registry target atom output

noncomputable def NativeRetelescopeResult.certificate
    (result : NativeRetelescopeResult env U registry target signature arguments available atom)
    {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ expression support footprint) :
    CodeCert env U registry target locals σ expression (result.view.mapType support) footprint :=
  .map result.view certificate

theorem NativeRetelescopeResult.typed
    (result : NativeRetelescopeResult env U registry target signature arguments available atom)
    (typed : (Profile.singleton atom).HasType support) :
    (Profile.singleton result.output).HasType (result.view.mapType support) :=
  result.view.mapType_typed typed

/-- Every recursive source code query is an original domain/codomain child of
the registered header. The changed child footprint is packed from its actual
availability in the fixed finite prefix valuation. -/
theorem NativeRetelescopeSkeleton.build
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    {arguments : List VExpr} {atom : Atom n} {required : Footprint}
    (skeleton : NativeRetelescopeSkeleton env U registry target signature arguments atom required)
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry)
      (signature.domains.take arguments.length).reverse
      (wrapForalls (signature.domains.drop arguments.length) signature.result))
    {available : Valuation} (closed : available.AtomClosed)
    (substitutions : Ctx.SubstEq env U target (nativeCaptureSubst arguments)
      (nativeCaptureSubst arguments) (signature.domains.take arguments.length).reverse)
    (fits : PairedFits env U registry (signature.domains.take arguments.length).reverse target
      (List.range arguments.length) (nativeCaptureSubst arguments) (nativeCaptureSubst arguments) available)
    (resources : required.Available available)
    {support : Profile n} {typeFootprint : Footprint}
    (certificate : CodeCert env U registry target (List.range arguments.length)
      (nativeCaptureSubst arguments)
      (wrapForalls (signature.domains.drop arguments.length) signature.result) support typeFootprint)
    (typeResources : typeFootprint.Available available)
    (typed : (Profile.singleton atom).HasType support) :
    Nonempty (NativeRetelescopeResult env U registry target signature arguments available atom) := by
  induction skeleton generalizing available typeFootprint with
  | terminal leaf => exact ⟨⟨_, _, .terminal leaf, resources, .refl _⟩⟩
  | @pad n arguments required atom body ih =>
    have lowerTyped : (Profile.singleton atom).HasType support.down := by
      apply Profile.HasType.pad_inv
      simpa only [Profile.pad_singleton] using typed
    obtain ⟨low⟩ := ih header closed substitutions fits resources (.down certificate) typeResources lowerTyped
    let high := low.tree.padSingleton henv
    exact ⟨⟨high.output, low.footprint, high.tree, low.resources,
      .trans (.pad low.view) high.view⟩⟩
  | @binder n domain arguments bodyFootprint packed outside key output origin body pack covered ih =>
    have literal := signature.prefixResidual_cons origin
    rw [literal] at header certificate
    obtain ⟨binder⟩ := certificate.retelescopedBinder henv hscoped hle header closed hTarget
      substitutions fits typeResources typed
    have extraBound := fun need member => (pack.localNeeds need member).1
    have extraCovered := fun need member atom ha => covered atom ((pack.localNeeds need member).2 atom ha)
    have coverage := binder.nextCoverage bodyFootprint.localNeeds extraBound extraCovered
    obtain ⟨u, formedA, originalA⟩ := header.domain.1
    obtain ⟨raw, localFits⟩ := binder.nextFits henv hTarget (formedA.defeq.mono hle)
      substitutions fits bodyFootprint.localNeeds extraBound extraCovered
    have bodyResources : bodyFootprint.Available
        (Valuation.push (binder.nextNeeds bodyFootprint.localNeeds) available) := by
      have old := pack.available resources
      intro i need member
      cases i with
      | zero => exact List.mem_append_left _ (List.mem_append_right _ (old 0 need member))
      | succ i => exact old (i + 1) need member
    have sourceEq := signature.prefixContext_cons origin
    have localsEq : List.range (arguments ++ [key.anchor]).length = Locals.push (List.range arguments.length) := by
      simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
    have lengthEq : (arguments ++ [key.anchor]).length = arguments.length + 1 := by simp
    have header' := header.codomain.2
    rw [← sourceEq] at header'
    have raw' : Ctx.SubstEq env U target
        (nativeCaptureSubst (arguments ++ [key.anchor])) (nativeCaptureSubst (arguments ++ [key.anchor]))
        (signature.domains.take (arguments ++ [key.anchor]).length).reverse := by
      simpa only [lengthEq, sourceEq, nativeCaptureSubst_append] using raw
    have fits' : PairedFits env U registry
        (signature.domains.take (arguments ++ [key.anchor]).length).reverse target
        (List.range (arguments ++ [key.anchor]).length)
        (nativeCaptureSubst (arguments ++ [key.anchor])) (nativeCaptureSubst (arguments ++ [key.anchor]))
        (Valuation.push (binder.nextNeeds bodyFootprint.localNeeds) available) := by
      simpa only [localsEq, lengthEq, sourceEq, nativeCaptureSubst_append, List.range_succ_eq_map, Locals.push] using localFits
    have certificate' : CodeCert env U registry target (List.range (arguments ++ [key.anchor]).length)
        (nativeCaptureSubst (arguments ++ [key.anchor]))
        (wrapForalls (signature.domains.drop (arguments ++ [key.anchor]).length) signature.result)
        binder.result binder.row.bodyFootprint := by
      simpa only [localsEq, lengthEq, nativeCaptureSubst_append, List.range_succ_eq_map, Locals.push] using binder.row.body
    obtain ⟨child⟩ := ih (by simpa only [lengthEq] using header')
      (binder.nextClosed _ closed) raw' fits' bodyResources certificate'
      (binder.bodyAvailable _) binder.resultTyped
    obtain ⟨childPacked, childOutside, childPack, childCovered, childOutsideAvailable⟩ :=
      Footprint.pack_available child.resources (fun need member => (coverage need member).1)
        (fun need member => (coverage need member).2)
    refine ⟨⟨.fn binder.actualKey child.output, binder.row.domainFootprint ++ childOutside,
      .binder origin binder.row.domain binder.guard child.tree childPack childCovered, ?_,
      .trans binder.forward (.fn binder.actualKey child.view)⟩⟩
    intro i need member
    exact (List.mem_append.mp member).elim (binder.row.domainAvailable i need)
      (childOutsideAvailable i need)

end Lean4Lean.AnchoredSource.Adapted
