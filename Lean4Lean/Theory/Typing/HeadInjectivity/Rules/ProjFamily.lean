import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.ProjTyping

/-! # The family header of a projection-registered structure

For a projection entry `S`, `info` of the declaration history (`VEnv.ProjOrigin`), the
family constant `S` is installed at the projection's universe arity, and its declared type is
definitionally a telescope over the header's own parameter domains and the index domains,
ending in the recorded result sort. The header's parameter domains and the constructor's raw
parameter domains are both context-convertible to the declaration's common parameter
telescope (`VEnv.ProjOrigin.familyTele_data`).

Composing the header conversion and the two parameter conversions into a single
definitional equality at a sort needs uniqueness of types: `TypeShape` types the header
conversion at an arbitrary `exprType`, and the two context conversions are typed at possibly
different sorts per domain. This file imports only the uniqueness-free base (D7). -/

namespace Lean4Lean
namespace VEnv
variable {env : VEnv} {U : Nat}

private theorem takeForalls_eq_wrapForalls' :
    ∀ {n : Nat} {type result : VExpr} {domains : List VExpr},
      type.takeForalls n = some (domains, result) →
      type = VExpr.wrapForalls domains result ∧ domains.length = n
  | 0, type, result, domains, H => by
    cases Option.some.inj H
    exact ⟨rfl, rfl⟩
  | n + 1, type, result, domains, H => by
    cases type with
    | forallE domain body =>
      cases htail : body.takeForalls n with
      | none => simp [VExpr.takeForalls, htail] at H
      | some out =>
        rw [VExpr.takeForalls, htail] at H
        cases Option.some.inj H
        have ih := takeForalls_eq_wrapForalls' htail
        exact ⟨congrArg (VExpr.forallE domain) ih.1, by simp [ih.2]⟩
    | bvar | sort | const | elim | app | lam | proj => simp [VExpr.takeForalls] at H

/-- The body of a well-formed Pi telescope is a type in the telescope's context. -/
theorem IsType.wrapForalls_body (henv : env.Ordered) :
    ∀ {ds : List VExpr} {Γ : List VExpr} {R : VExpr},
      env.IsType U Γ (VExpr.wrapForalls ds R) → env.IsType U (ds.reverse ++ Γ) R
  | [], _, _, h => by simpa [VExpr.wrapForalls] using h
  | d :: ds, Γ, R, h => by
    obtain ⟨-, hB⟩ := IsType.forallE_inv henv h
    simpa [List.reverse_cons, List.append_assoc] using IsType.wrapForalls_body henv hB

/-- The head of a typed application spine is typed. -/
theorem HasType.mkApps_fn (henv : env.Ordered) {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {args : List VExpr} {f V : VExpr}, env.HasType U Γ (VExpr.mkApps f args) V →
      ∃ V', env.HasType U Γ f V'
  | [], _, _, h => ⟨_, h⟩
  | a :: as, f, V, h => by
    obtain ⟨V', h'⟩ := HasType.mkApps_fn henv hΓ (args := as) (f := .app f a) h
    obtain ⟨A, B, hf, -⟩ := HasType.app_inv henv hΓ h'
    exact ⟨_, hf⟩

/-- Congruence of a typed Pi telescope in its body. -/
theorem HasType.wrapForalls_congr_body (henv : env.Ordered) :
    ∀ {ds : List VExpr} {Γ : List VExpr} {B B' V : VExpr} {v : VLevel},
      env.HasType U Γ (VExpr.wrapForalls ds B) V →
      env.IsDefEq U (ds.reverse ++ Γ) B B' (.sort v) →
      ∃ w, env.IsDefEq U Γ (VExpr.wrapForalls ds B) (VExpr.wrapForalls ds B') (.sort w)
  | [], _, _, _, _, _, _, h => ⟨_, by simpa [VExpr.wrapForalls] using h⟩
  | d :: ds, Γ, B, B', V, v, hT, h => by
    obtain ⟨⟨u, hd⟩, ⟨u', hB⟩⟩ := HasType.forallE_inv henv hT
    obtain ⟨w, hw⟩ := HasType.wrapForalls_congr_body henv (Γ := d :: Γ) hB
      (by simpa [List.reverse_cons, List.append_assoc] using h)
    exact ⟨_, .forallEDF hd hw⟩

/-- **The family header of a projection entry**, up to the conversions recorded by
`SourceParameterWF`: the declared family type `famType` of `S` is definitionally (at the
recorded `exprType`) a telescope over the header's parameter domains `ownParams` and the
index domains `idoms` with body `result`, which is the recorded sort; the constructor type
is a telescope over its raw parameter domains `pdoms` and field domains `fdoms`, ending in
`S` at its own universe parameters applied to the parameter variables and `idx`; both
`ownParams` and `pdoms` are context-convertible to the common parameters `params`. -/
theorem ProjOrigin.familyTele_data {S : Name} {info : VProjectionInfo}
    (h : env.ProjOrigin S info) :
    ∃ (envTypes : VEnv) (famType : VExpr) (params ownParams pdoms fdoms idoms idx : List VExpr)
      (result exprType : VExpr),
      envTypes.Ordered ∧ envTypes ≤ env ∧
      (∃ base dsb cis, VEnv.WF' dsb base ∧ base.addConstVals cis = some envTypes) ∧
      envTypes.constants S = some ⟨info.uvars, famType⟩ ∧
      info.ctorType = VExpr.wrapForalls (pdoms ++ fdoms)
        (VExpr.mkApps (.const S (VLevel.params info.uvars))
          ((List.range info.nparams).reverse.map
              (fun i => .bvar ((pdoms ++ fdoms).length - info.nparams + i)) ++ idx)) ∧
      pdoms.length = info.nparams ∧ ownParams.length = info.nparams ∧
      idoms.length = info.nindices ∧ idx.length = info.nindices ∧
      envTypes.IsDefEq info.uvars [] famType (VExpr.wrapForalls (ownParams ++ idoms) result)
        exprType ∧
      envTypes.IsDefEq info.uvars (idoms.reverse ++ ownParams.reverse) result
        (.sort info.resultLevel) (.sort (.succ info.resultLevel)) ∧
      (∃ w, envTypes.IsDefEq info.uvars [] (VExpr.wrapForalls (ownParams ++ idoms) result)
        (VExpr.wrapForalls (ownParams ++ idoms) (.sort info.resultLevel)) (.sort w)) ∧
      envTypes.IsDefEqCtx info.uvars [] params.reverse ownParams.reverse ∧
      envTypes.IsDefEqCtx info.uvars [] params.reverse pdoms.reverse := by
  obtain ⟨doms, idx, hshape, hdl, hidx⟩ := h.ctorType_shape
  obtain ⟨base, envTypes, dsb, decl, type, ctor, hbase, htypes, hle, hord, htype, hctors, rfl,
    hu, hnp, hni, hrl, -, hct, -, hwf, -, -, hspw⟩ := h
  obtain ⟨params, envTypes0, htypes0, HT, HC, -⟩ := hspw
  cases htypes0.symm.trans htypes
  obtain ⟨normalized, ownParams, afterParams, indices, result, exprType, hT, hP, hI, hPD,
    hres⟩ := HT type htype
  obtain ⟨hn1, hn2⟩ := takeForalls_eq_wrapForalls' hP
  obtain ⟨ha1, ha2⟩ := takeForalls_eq_wrapForalls' hI
  obtain ⟨ctorParams, tail, htake, hCPD⟩ := HC type htype ctor (by rw [hctors]; simp)
  -- the constructor's raw parameter prefix is the first `nparams` domains
  have hsplit : doms = doms.take info.nparams ++ doms.drop info.nparams :=
    (List.take_append_drop _ _).symm
  have hcp : ctorParams = doms.take info.nparams := by
    have hs := hshape
    generalize VExpr.mkApps _ _ = R at hs
    have h2 := VExpr.takeForalls_wrapForalls_append (doms.take info.nparams)
      (doms.drop info.nparams) R
    rw [List.take_append_drop, ← hs, hct, List.length_take, Nat.min_eq_left hdl, hnp,
      htake] at h2
    rw [hnp]; exact (Prod.mk.inj (Option.some.inj h2)).1
  -- the family constant has the declaration's universe arity
  have hconst : envTypes.constants type.name = some type.toVConstVal.toVConstant :=
    VEnv.addConstVals_get htypes (List.mem_map.mpr ⟨type, htype, rfl⟩)
  have huv : type.uvars = decl.uvars := by
    rw [← hct, hshape] at hwf
    have hctx := IsType.wrapForalls_ctx hord (Γ := []) trivial hwf doms.length (Nat.le_refl _)
    obtain ⟨_, hR⟩ := IsType.wrapForalls_body hord hwf
    simp only [List.append_nil, List.take_length] at hR hctx
    obtain ⟨_, hc⟩ := HasType.mkApps_fn hord hctx hR
    obtain ⟨ci, hci, -, hlen⟩ := HasType.const_inv hord hctx hc
    rw [hconst] at hci
    cases hci
    simpa [hu] using hlen.symm
  have hbt : base ≤ envTypes := VEnv.addConstVals_le htypes
  have hnorm : normalized = VExpr.wrapForalls (ownParams ++ indices) result := by
    rw [hn1, ha1]; simp [VExpr.wrapForalls]
  refine ⟨envTypes, type.type, params, ownParams, doms.take info.nparams,
    doms.drop info.nparams, indices, idx, result, exprType, hord, hle,
    ⟨base, dsb, _, hbase, htypes⟩, ?_, ?_, by simp; omega, by rw [hn2, hnp],
    by rw [ha2, hni], hidx, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hconst, hu, ← huv]
  · rw [← hsplit]; exact hshape
  · rw [hu, ← hnorm]; exact hT.mono hbt
  · rw [hu, hrl]; exact hres.mono hbt
  · rw [hu, hrl]
    have hN := (hT.mono hbt).hasType.2
    rw [hnorm] at hN
    exact HasType.wrapForalls_congr_body hord hN
      (by simpa [List.reverse_append] using hres.mono hbt)
  · rw [hu]; exact hPD.mono hbt
  · rw [hu, ← hcp]; exact hCPD
