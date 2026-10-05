import Lean4Lean.Theory.Typing.AnchoredFamilyCaptureObservation
import Lean4Lean.Theory.Typing.AnchoredNativeRhsOpening

/-! Dependent replay of finite original native equation rows against actual
projection captures. The frozen requests supply both raw typing and the
source certificates in the paired fitting valuation. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Uniform target requests recover the original heterogeneous row ledger,
including every field-domain certificate dependency. The replacement tuple
may contain primitive projections of a neutral structure major. -/
theorem FamilySeededCodeRows.nativeCapturePair
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target : List VExpr} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required [] []
      (nativeCaptureSubst []) (fun _ => []) expression domains keys)
    (hTarget : OnCtx target (env.IsType U))
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N)
    {values : List VExpr}
    (arguments : RankedData.Arguments env U (relations env U registry N) target
      (FamilyKey.uniform N keys bounded) (keys.map (·.key.anchor)) values) :
    rows.terminalValuation.AtomClosed ∧ required.Available rows.terminalValuation ∧
      Ctx.SubstEq env U target (nativeCaptureSubst (keys.map (·.key.anchor)))
        (nativeCaptureSubst values) domains.reverse ∧
      PairedFits env U registry domains.reverse target rows.terminalLocals
        (nativeCaptureSubst (keys.map (·.key.anchor))) (nativeCaptureSubst values)
        rows.terminalValuation := by
  have initial : FamilyPrefixAlignment env U registry [] target []
      (nativeCaptureSubst []) (nativeCaptureSubst []) (nativeCaptureSubst []) (fun _ => []) :=
    ⟨.nil, .nil, .nil, .nil⟩
  have closed : Valuation.AtomClosed (fun _ => []) := by intro _ _ member; cases member
  obtain ⟨_, finalClosed, resources, final⟩ := rows.alignExact henv hscoped hle closed hTarget
    initial (FamilyArguments.of_uniform henv hTarget N bounded arguments)
  refine ⟨finalClosed, resources, ?_, ?_⟩
  · simpa only [familySubst_native, List.nil_append, List.append_nil] using final.substitutions
  · simpa only [familySubst_native, List.nil_append, List.append_nil] using final.fits

/-- The actual original RHS is interpreted with the paired capture tuple
just reconstructed from fixed requests. All resulting certificates remain
in the original finite terminal ledger. -/
theorem FamilySeededCodeRows.nativeRhs
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {target : List VExpr} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required [] []
      (nativeCaptureSubst []) (fun _ => []) expression domains keys)
    (hTarget : OnCtx target (env.IsType U))
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N)
    {values : List VExpr}
    (arguments : RankedData.Arguments env U (relations env U registry N) target
      (FamilyKey.uniform N keys bounded) (keys.map (·.key.anchor)) values)
    {rhs result : VExpr}
    (original : sourceEnv.HasTypeStrong U [] (wrapLams domains rhs)
      (wrapForalls domains result) structural)
    (formation : sourceEnv.IsDefEqStrong U [] (wrapForalls domains result)
      (wrapForalls domains result) (.sort level))
    {demand : Profile n}
    (observation : Obs env U registry target rows.terminalLocals
      (nativeCaptureSubst (keys.map (·.key.anchor))) rhs demand required) :
    Nonempty (DeclaredRhsResult env U registry target rows.terminalLocals
      (nativeCaptureSubst (keys.map (·.key.anchor))) (nativeCaptureSubst values)
      rows.terminalValuation domains rhs result demand) := by
  obtain ⟨closed, resources, substitutions, fits⟩ :=
    rows.nativeCapturePair henv hscoped hle hTarget N bounded arguments
  exact HasTypeStrong.declaredRhs henv hscoped hsource hle earlier (by trivial)
    original formation closed hTarget
    (by simpa only [List.append_nil] using substitutions)
    (by simpa only [List.append_nil] using fits) observation resources

end Lean4Lean.AnchoredSource.Adapted
