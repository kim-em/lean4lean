import Lean4Lean.Theory.Typing.ShapeModel.EnvSigOrigin
import Lean4Lean.Theory.Typing.ShapeModel.Head
import Lean4Lean.Theory.Typing.NativeConstructorRigidity

/-!
# The head facts of the semantic signature of a well-formed environment

`envSig_headFacts`: the signature `envSig env` of a well-formed environment satisfies
`SemSig.HeadFacts env` (`Head.lean`).

* `ruleNotRigid`: the rules headed by a constant are its definition, quotient and native iota
  equations, none of which is headed by a rigid constant (`EnvRule.head_not_rigid`).
* `famCtors`: the constructors of a family are declared constructors (`mem_sigFamCtors`).
* `famType`: the family table records a type that is definitionally a telescope whose body is
  definitionally the recorded sort (`famOf_shape`); congruence under the telescope closes it.
* `ctorType`: a constructor's type is syntactically a telescope ending in its family applied
  (`IsCtor.shape`), and the family is rigid: a table constructor's family is a table family
  (`ctorOf_rigid`), the family of a major of a generic eliminator equation outside the table is
  an original family of the schema (`generic_major_origin`, `WF.case_original_family_rigid`).
-/

namespace Lean4Lean.ShapeModel
open InductiveSignature

variable {env : VEnv}

/-! ## Congruence under a telescope -/

theorem onCtx_append_right' {P : List VExpr → VExpr → Prop} :
    ∀ {xs ys : List VExpr}, OnCtx (xs ++ ys) P → OnCtx ys P
  | [], _, H => H
  | _ :: _, _, H => onCtx_append_right' H.1

theorem isType_wrapForalls_inv' (henv : env.Ordered) :
    ∀ {domains Γ : List VExpr} {body : VExpr}, OnCtx Γ (env.IsType U) →
      env.IsType U Γ (VExpr.wrapForalls domains body) →
      OnCtx (domains.reverse ++ Γ) (env.IsType U)
  | [], _, _, hΓ, _ => hΓ
  | d :: ds, Γ, body, hΓ, H => by
    have hinv := VEnv.IsType.forallE_inv henv H
    have := isType_wrapForalls_inv' henv (domains := ds) (Γ := d :: Γ) (body := body)
      ⟨hΓ, hinv.1⟩ hinv.2
    simpa [List.reverse_cons, List.append_assoc] using this

/-- The domains of a typed telescope are types in their scopes (for any type of the telescope). -/
theorem hasType_wrapForalls_inv (henv : env.Ordered) {domains Γ : List VExpr} {body V : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.HasType U Γ (VExpr.wrapForalls domains body) V) :
    OnCtx (domains.reverse ++ Γ) (env.IsType U) := by
  cases domains with
  | nil => exact hΓ
  | cons d ds =>
    have hinv := VEnv.HasType.forallE_inv henv H
    have := isType_wrapForalls_inv' henv (domains := ds) (Γ := d :: Γ) (body := body)
      ⟨hΓ, hinv.1⟩ hinv.2
    simpa [List.reverse_cons, List.append_assoc] using this

theorem wrapForalls_congr_body' :
    ∀ {domains Γ : List VExpr} {body body' : VExpr} {level : VLevel},
      OnCtx (domains.reverse ++ Γ) (env.IsType U) →
      env.IsDefEq U (domains.reverse ++ Γ) body body' (.sort level) →
      ∃ level', env.IsDefEq U Γ (VExpr.wrapForalls domains body)
        (VExpr.wrapForalls domains body') (.sort level')
  | [], _, _, _, level, _, h => ⟨level, h⟩
  | d :: ds, Γ, body, body', level, hctx, h => by
    have hctx' : OnCtx (ds.reverse ++ d :: Γ) (env.IsType U) := by
      simpa [List.reverse_cons, List.append_assoc] using hctx
    obtain ⟨l', hrest⟩ := wrapForalls_congr_body' hctx'
      (by simpa [List.reverse_cons, List.append_assoc] using h)
    obtain ⟨dl, hd⟩ := (onCtx_append_right' hctx').2
    exact ⟨.imax dl l', .forallEDF hd hrest⟩

/-! ## The fields -/

theorem envSig_famType (H : env.WF) (hl : sigFamLevel env c = some l)
    (hci : env.constants c = some ci) :
    ∃ W doms T T', env.IsDefEq ci.uvars [] ci.type W T ∧
      env.IsDefEq ci.uvars [] W (VExpr.wrapForalls doms (.sort l)) T' := by
  simp only [sigFamLevel, Option.map_eq_some_iff] at hl
  obtain ⟨d, hd, rfl⟩ := hl
  obtain ⟨ci', hci', huv, doms, result, type, h1, -, h2⟩ := famOf_shape H hd
  rw [hci] at hci'
  cases hci'
  rw [huv]
  have hctx := hasType_wrapForalls_inv H.ordered (Γ := []) trivial h1.hasType.2
  obtain ⟨_, hw⟩ := wrapForalls_congr_body' (Γ := []) (by simpa using hctx) (by simpa using h2)
  exact ⟨_, doms, _, _, h1, hw⟩

/-- The family of a constructor of the signature is rigid. -/
theorem sigCtor_family_rigid (H : env.WF) (hk : sigCtor env c = some k) : env.Rigid k.family := by
  obtain ⟨hc, cv, hcv, hF, -⟩ := sigCtor_spec hk
  have table : ∀ k', ctorOf env c = some k' → env.Rigid k.family := by
    intro k' hk'
    obtain ⟨ci, doms, idx, hci, -, ht, -⟩ := ctorOf_shape' H hk'
    rw [hcv] at hci
    cases hci
    rw [ht, familyOfType_shape] at hF
    rw [← Option.some.inj hF]
    exact (ctorOf_rigid H hk').2.1
  rcases hc with hc | ⟨hm, -⟩
  · obtain ⟨k', hk'⟩ := Option.ne_none_iff_exists'.mp hc
    exact table k' hk'
  · obtain ⟨key, schema, hreg, owner, rules, df, fn, ls, args, hgen, hdf, hm⟩ := hm
    rcases generic_major_origin H hreg hgen hdf hm with hc | ⟨horig, -⟩
    · obtain ⟨k', hk'⟩ := Option.ne_none_iff_exists'.mp hc
      exact table k' hk'
    · rw [sigCtor_family hk] at horig
      exact VEnv.nativeHeadRigid_iff.mp
        (VEnv.WF.case_original_family_rigid H hreg (List.mem_of_getElem? horig))

theorem envSig_ctorType (H : env.WF) (hk : sigCtor env c = some k)
    (hci : env.constants c = some ci) :
    (∀ r, EnvRule env r → r.head ≠ .const k.family) ∧
    ∃ doms ls args T, env.IsDefEq ci.uvars [] ci.type
      (VExpr.wrapForalls doms (VExpr.mkApps (.const k.family ls) args)) T := by
  refine ⟨fun r hr => EnvRule.head_not_rigid H (sigCtor_family_rigid H hk) hr, ?_⟩
  obtain ⟨hc, cv, hcv, hF, -⟩ := sigCtor_spec hk
  rw [hci] at hcv
  cases hcv
  obtain ⟨k', ci', doms, idx, hci', -, ht, -⟩ := IsCtor.shape H hc
  rw [hci] at hci'
  cases hci'
  rw [ht, familyOfType_shape] at hF
  rw [← Option.some.inj hF]
  obtain ⟨u, hu⟩ := H.ordered.constWF hci
  have hu' : env.IsDefEq ci.uvars [] ci.type ci.type (.sort u) := hu
  refine ⟨doms, VLevel.params k'.uvars, vars k'.nparams k'.nfields ++ idx, .sort u, ?_⟩
  rwa [← ht]

/-- The head facts of the semantic signature of a well-formed environment. -/
theorem envSig_headFacts (H : env.WF) : letI := envSig env; SemSig.HeadFacts env := by
  letI := envSig env
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r c hr hh hrig
    exact EnvRule.head_not_rigid H hrig hr hh
  · intro c c' hc'
    obtain ⟨k, hk, -⟩ := (mem_sigFamCtors H).mp hc'
    obtain ⟨-, cv, hcv, -⟩ := sigCtor_spec hk
    exact ⟨cv, k, hcv, hk⟩
  · intro c l ci hl hci
    exact envSig_famType H hl hci
  · intro c k ci hk hci
    exact envSig_ctorType H hk hci

end Lean4Lean.ShapeModel
