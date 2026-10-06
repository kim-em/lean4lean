import Lean4Lean.Theory.Typing.ConcretePatterns
import Lean4Lean.Theory.Typing.FullChurchRosser

/-! The `Params` instance of a well-formed environment, built from its
canonical registry. The structure-major and native soundness facts are passed
in by the caller; they are proved in separate files. -/

namespace Lean4Lean.VEnv
open InductiveSignature CanonicalDataHead

/-- Assemble `Params` from the canonical registry and the remaining facts. -/
@[instance_reducible] noncomputable def Params.ofRegistry {E : VEnv} {registry : Registry} {declarations : List VDecl}
    (henv : E.WF) (contract : registry.EnvironmentContract E declarations) (U : Nat)
    (sound : ∀ {Γ : List VExpr} {p : Pattern} {r : p.RHS × p.Check} {e A m1 m2},
      OnCtx Γ (E.IsType U) → NativeIotaPattern E registry.natives p r →
      p.Matches e m1 m2 → E.HasType U Γ e A → E.IsDefEqU U Γ e (r.1.apply m1 m2))
    (structMajor : ∀ {rc mr cc kc} {r : (Pattern.app ((Pattern.const rc).varN mr)
        ((Pattern.const cc).varN kc)).RHS × (Pattern.app ((Pattern.const rc).varN mr)
        ((Pattern.const cc).varN kc)).Check} {Γ family info lsc fs ls ps},
      ConcretePattern registry E (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r →
      OnCtx Γ (E.IsType U) → E.projections family info →
      E.HasType U Γ (VExpr.mkApps (.const cc lsc) fs) (VExpr.mkApps (.const family ls) ps) →
      fs.length = kc → cc = info.ctorName ∧ kc = info.nparams + info.numFields)
    (iotaParams : ∀ {rc mr cc kc} {r : (Pattern.app ((Pattern.const rc).varN mr)
        ((Pattern.const cc).varN kc)).RHS × (Pattern.app ((Pattern.const rc).varN mr)
        ((Pattern.const cc).varN kc)).Check} {family info lsc lsc' ps ps' fields g g'},
      ConcretePattern registry E (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r →
      E.projections family info → cc = info.ctorName →
      ((Pattern.const cc).varN kc).Matches (VExpr.mkApps (.const cc lsc) (ps ++ fields)) lsc g →
      ((Pattern.const cc).varN kc).Matches (VExpr.mkApps (.const cc lsc') (ps' ++ fields)) lsc' g' →
      ps.length = info.nparams → ps'.length = info.nparams →
      (∀ (m1 : List VLevel) (g1 : ((Pattern.const rc).varN mr).Path → VExpr),
        Pattern.RHS.apply (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
            m1 (Sum.elim g1 g) r.1 =
          Pattern.RHS.apply (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
            m1 (Sum.elim g1 g') r.1) ∧
      (∀ (m1 : List VLevel) (g1 : ((Pattern.const rc).varN mr).Path → VExpr)
        (df : VExpr → VExpr → Prop),
        Pattern.Check.OK (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
            df m1 (Sum.elim g1 g) r.2 →
          Pattern.Check.OK (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
            df m1 (Sum.elim g1 g') r.2))
    (schemaStruct : ∀ {Γ rule actual family info ls ps},
      MatchedCaseStep E U Γ rule actual → OnCtx Γ (E.IsType U) →
      E.projections family info →
      E.HasType U Γ (VExpr.mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments)
        (VExpr.mkApps (.const family ls) ps) →
      actual.ctorName = info.ctorName ∧
        actual.ctorArguments.length = info.nparams + info.numFields ∧
        rule.numFields ≤ info.numFields) : Params where
  env := E
  henv := henv
  univs := U
  recursorData := registry.natives
  recursorData_registered h := let ⟨a, b, _⟩ := contract.natives _ _ h; ⟨a, b⟩
  Pat := ConcretePattern registry E
  pat_origin h := ConcretePattern.origin henv contract h
  pat_recursor h := ConcretePattern.recursor henv contract h
  pat_simple h := ConcretePattern.simple henv contract h
  pat_uniq h h' hs hi := ConcretePattern.uniq henv contract h h' hs hi
  pat_wf hΓ h hm ht hc := by
    rcases h with h | ⟨_, h⟩ | h
    · exact DefinitionPattern.sound henv hΓ (fun _ _ h => (contract.definitions _ _ h).1) h hm ht
    · exact QuotPattern.sound henv hΓ h hm ht hc
    · exact sound hΓ h hm ht
  pat_app_l h hs := ConcretePattern.app_l henv contract h hs
  pat_app_l_uniq h h' hs hs' hb := ConcretePattern.app_l_uniq henv contract h h' hs hs' hb
  pat_app_uniq h h' hs hs' hl hr := ConcretePattern.app_uniq henv contract h h' hs hs' hl hr
  pat_const_native h := ConcretePattern.const_native henv contract h
  recursorData_quot hq := ConcretePattern.native_quot henv contract hq
  pat_ctor_rigid h := ConcretePattern.ctor_rigid henv contract h
  projection_ctor_rigid hl := nativeHeadRigid_iff.mpr (henv.projectionCtorRigid hl)
  pat_struct_major h hΓ hl hs hlen := structMajor h hΓ hl hs hlen
  pat_iota_params h hl hcc hm hm' hps hps' := iotaParams h hl hcc hm hm' hps hps'
  schema_struct_major hm hΓ hl hs := schemaStruct hm hΓ hl hs

end Lean4Lean.VEnv
