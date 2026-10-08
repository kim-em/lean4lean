import Lean4Lean.Verify.Inductive.Nested.ProjectionTransportGap

/-! The projection transport of the restored-equation route in well-formed
contexts, with no hypothesis.

The renaming restoration substitution of `Nested/RestoredEquationWF.lean`
transports projection rules through `ProjectionTransportOnCtx`, which only
asks for the rules in well-formed image contexts. There beta conversion of a
typed term is beta subject reduction (`VExpr.BetaRed.simAt`) and level
equivalence is definitional equality (`VExpr.LEquiv.defeq`).

* Primary projections (of original structures): the transported lowered
  constructor type beta reduces to the source constructor type registered by
  the final environment (`ProjectionTransportOnCtx.of_ctorType_betaRed`).
* Auxiliary projections (of an auxiliary structure-like family `A`, renamed to
  its container `J`): the restoration lambdas of `A` and its constructor are
  `λ params, J levels args` and `λ params, J.c levels args`. The generated
  constructor type of `A`, the restoration of the lowered one, is
  syntactically the parameter closure of `J.c`'s type instantiated at the
  specialization (`AuxiliarySpecializationEvidence.constructorShapes`, up to
  level equivalence). So the transported field types of `A` are, up to beta
  reduction and level equivalence, the field types of `J` at the
  instantiated specialization arguments
  (`VEnv.fieldTransport_of_specialization`), and each projection rule of `A`
  is the corresponding rule of `J` after beta reducing the restoration
  lambdas (`VEnv.ProjectionTransportOnCtx.of_specialization`).

The composition is `NestedValidatedRunResult.restoredEquationGaps` and
`NestedValidatedRunResult.hrestoredWF_of`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

/-! ### Syntactic lemmas -/

namespace VExpr

theorem LEquiv.instL {U₀ U : Nat} {e e' : VExpr} {ls : List VLevel}
    (H : LEquiv U₀ e e') (hls : ∀ l ∈ ls, l.WF U) :
    LEquiv U (e.instL ls) (e'.instL ls) := by
  induction H with
  | refl => exact .refl
  | sort h1 _ => exact .sort (VLevel.inst_congr_l h1) (VLevel.WF.inst hls)
  | const h1 _ =>
    refine .const ?_ ?_
    · exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
        (Lean4Lean.List.Forall₂.imp (fun _ _ h => VLevel.inst_congr_l h) h1))
    · intro v hv
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv
      exact VLevel.WF.inst hls
  | elim h1 _ =>
    refine .elim ?_ ?_
    · exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
        (Lean4Lean.List.Forall₂.imp (fun _ _ h => VLevel.inst_congr_l h) h1))
    · intro v hv
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv
      exact VLevel.WF.inst hls
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

theorem LEquiv.forallArity_eq {U : Nat} {e e' : VExpr} (H : LEquiv U e e') :
    e.forallArity = e'.forallArity := by
  induction H with
  | refl => rfl
  | forallE _ _ _ ih => simp [forallArity, ih]
  | _ => rfl

theorem LEquiv.forallE_inv_l {U : Nat} {A b T : VExpr} (H : LEquiv U (.forallE A b) T) :
    ∃ A' b', T = .forallE A' b' ∧ LEquiv U A A' ∧ LEquiv U b b' := by
  generalize hx : VExpr.forallE A b = x at H
  cases H with
  | refl => subst hx; exact ⟨_, _, rfl, .refl, .refl⟩
  | forallE h1 h2 => cases hx; exact ⟨_, _, rfl, h1, h2⟩
  | _ => cases hx

theorem forallArity_mkApps_of_zero' :
    ∀ {f : VExpr} (xs : List VExpr), f.forallArity = 0 → (VExpr.mkApps f xs).forallArity = 0
  | _, [], h => h
  | _, _ :: xs, _ => forallArity_mkApps_of_zero' (f := .app _ _) xs rfl

theorem forallArity_mkApps_const_instOuter (c : Name) (ls : List VLevel)
    (xs args : List VExpr) :
    ((VExpr.mkApps (.const c ls) xs).instOuter args).forallArity = 0 := by
  rw [instOuter_mkApps, instOuter_const]
  exact forallArity_mkApps_of_zero' _ rfl

@[simp] theorem replaceRen_proj' {ρ : Name → Option VExpr} {σ : Name → Name}
    {n : Name} {i : Nat} {e : VExpr} :
    (VExpr.proj n i e).replaceRen ρ σ = .proj (σ n) i (e.replaceRen ρ σ) := rfl

namespace BetaRed

/-- Beta reduction of a restoration lambda `λ params, J levels args` (at
levels `lv`) applied to a complete parameter spine. -/
theorem mkApps_specialization {P hargs : List VExpr} {J : Name} {ls lv : List VLevel}
    (params rest : List VExpr) (hP : params.length = P.length) :
    BetaRed (VExpr.mkApps ((VExpr.wrapLams P (VExpr.mkApps (.const J ls) hargs)).instL lv)
        (params ++ rest))
      (VExpr.mkApps (.const J (ls.map (·.inst lv)))
        (hargs.map (fun a => (a.instL lv).instOuter params) ++ rest)) := by
  rw [VExpr.instL_wrapLams]
  have := mkApps_wrapLams (P.map (VExpr.instL lv))
    ((VExpr.mkApps (.const J ls) hargs).instL lv) (params ++ rest)
    (by simp [hP])
  simp only [List.length_map, ← hP, List.take_left', List.drop_left'] at this
  refine this.trans ?_
  simp only [VExpr.instL_mkApps, VExpr.instL, VExpr.instOuter_mkApps,
    VExpr.instOuter_const, ← VExpr.mkApps_append, List.map_map, Function.comp_def]
  exact .refl

end BetaRed
end VExpr

namespace VProjectionInfo

theorem instantiateProjectionParameters_wrapForalls_eq :
    ∀ (doms : List VExpr) (body : VExpr) (params : List VExpr),
      doms.length = params.length →
      instantiateProjectionParameters (VExpr.wrapForalls doms body) params =
        some (body.instOuter params)
  | [], _, [], _ => rfl
  | [], _, _ :: _, h => by simp at h
  | _ :: _, _, [], h => by simp at h
  | d :: ds, body, p :: ps, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    change instantiateProjectionParameters ((VExpr.wrapForalls ds body).inst p) ps = _
    rw [VExpr.wrapForalls_inst, Nat.zero_add,
      instantiateProjectionParameters_wrapForalls_eq _ _ ps (by simpa using h)]
    simp [h]

theorem instantiateProjectionFields_lequiv {typeName : Name} {major : VExpr} {wanted : Nat}
    {U : Nat} :
    ∀ (fuel : Nat) {current : Nat} {A B X : VExpr}, VExpr.LEquiv U A B →
      instantiateProjectionFields typeName major wanted current fuel A = some X →
      ∃ Y, instantiateProjectionFields typeName major wanted current fuel B = some Y ∧
        VExpr.LEquiv U X Y
  | 0, _, _, _, _, _, hX => by simp [instantiateProjectionFields] at hX
  | fuel + 1, current, A, B, X, h, hX => by
    cases A with
    | forallE d b =>
      obtain ⟨d', b', rfl, hd, hb⟩ := h.forallE_inv_l
      simp only [instantiateProjectionFields] at hX ⊢
      by_cases hw : wanted = current
      · rw [if_pos hw] at hX ⊢
        cases hX
        exact ⟨_, rfl, hd⟩
      · rw [if_neg hw] at hX ⊢
        exact instantiateProjectionFields_lequiv fuel (hb.inst _ 0) hX
    | _ => simp [instantiateProjectionFields] at hX

theorem fieldType_lengths {info : VProjectionInfo} {typeName : Name} {levels : List VLevel}
    {params : List VExpr} {index : Nat} {major X : VExpr}
    (H : info.fieldType typeName levels params index major = some X) :
    levels.length = info.uvars ∧ params.length = info.nparams := by
  unfold fieldType at H
  split at H
  · cases H
  · next h =>
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at h
    exact h

end VProjectionInfo

namespace VEnv

/-- **Field types of a specialized projection.** The transported field types
of a projection `(typeName, info)` renamed to `J`, whose transported
constructor type beta reduces to the parameter closure of `J`'s constructor
type instantiated at `hargs` (up to level equivalence), are definitionally
the field types of `J`'s registered projection at the instantiated
specialization, in well-formed contexts. -/
theorem fieldTransport_of_specialization {envS : VEnv} (henv : envS.WF)
    {ρ : Name → Option VExpr} {σ : Name → Name} (hρ : VExpr.ReplacementsClosed ρ)
    {typeName J : Name} {info infoJ : VProjectionInfo}
    {G T B : VExpr} {Psrc Q hargs : List VExpr} {ls : List VLevel} {U₀ : Nat}
    (hσtn : σ typeName = J)
    (hBR : VExpr.BetaRed (info.ctorType.replaceRen ρ σ) G)
    (hG : G = VExpr.wrapForalls Psrc (VExpr.instantiateForallPrefix T hargs))
    (hPsrc : Psrc.length = info.nparams)
    (hT : VExpr.LEquiv U₀ T (infoJ.ctorType.instL ls))
    (hJ : infoJ.ctorType = VExpr.wrapForalls Q B) (hQ : Q.length = hargs.length)
    (hB : B.ClosedN Q.length)
    (hJn : infoJ.nparams = hargs.length) (hJu : infoJ.uvars = ls.length) :
    ∀ {U : Nat} {Γ : List VExpr} {lv : List VLevel} {params : List VExpr} {index : Nat}
      {major F : VExpr},
      OnCtx Γ (envS.IsType U) → (∀ l ∈ lv, l.WF U) →
      info.fieldType typeName lv params index major = some F →
      ∃ F', infoJ.fieldType J (ls.map (·.inst lv))
          (hargs.map fun a => (a.instL lv).instOuter (params.map (·.replaceRen ρ σ))) index
          (major.replaceRen ρ σ) = some F' ∧
        ∀ {ℓ : VLevel}, envS.HasType U Γ (F.replaceRen ρ σ) (.sort ℓ) →
          envS.IsDefEq U Γ (F.replaceRen ρ σ) F' (.sort ℓ) := by
  intro U Γ lv params index major F hΓ hlv hF
  obtain ⟨hlvLen, hparamsLen⟩ := VProjectionInfo.fieldType_lengths hF
  have h1 := VProjectionInfo.fieldType_replaceRen' (typeName := typeName) (levels := lv)
    (params := params) (index := index) (major := major) (σ := σ) hρ info
  rw [hF, hσtn] at h1
  obtain ⟨Y, hY, hFY⟩ := VProjectionInfo.fieldType_betaRed (ctorType' := G) hBR h1
  -- the tail of `G` at the parameters
  obtain ⟨Q₀, B₀, hTeq, hQ₀, hB₀⟩ := by
    rw [hJ, VExpr.instL_wrapForalls] at hT
    exact hT.wrapForalls_inv
  have hQ₀len : Q₀.length = hargs.length := by
    rw [Lean4Lean.List.Forall₂.length_eq hQ₀]; simpa using hQ
  have hX : VExpr.instantiateForallPrefix T hargs = B₀.instOuter hargs := by
    rw [hTeq]
    exact VerifyInductive.VExpr.instantiateForallPrefix_wrapForalls _ _ _ hQ₀len
  let ps := params.map (·.replaceRen ρ σ)
  have hpsLen : ps.length = info.nparams := by simp [ps, hparamsLen]
  have htailG : VProjectionInfo.instantiateProjectionParameters (G.instL lv) ps =
      some (((B₀.instOuter hargs).instL lv).instOuter ps) := by
    rw [hG, hX, VExpr.instL_wrapForalls]
    exact VProjectionInfo.instantiateProjectionParameters_wrapForalls_eq _ _ _
      (by simp [hPsrc, hpsLen])
  have hY' : VProjectionInfo.instantiateProjectionFields J (major.replaceRen ρ σ) index 0
      (index + 1) (((B₀.instOuter hargs).instL lv).instOuter ps) = some Y := by
    unfold VProjectionInfo.fieldType at hY
    split at hY
    · cases hY
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hY
      obtain ⟨tail, htail, hfields⟩ := hY
      have : tail = ((B₀.instOuter hargs).instL lv).instOuter ps :=
        Option.some.inj (htail.symm.trans htailG)
      subst this
      exact hfields
  -- the tail of `J`'s constructor type at the instantiated specialization
  let ls' := ls.map (·.inst lv)
  let params' := hargs.map fun a => (a.instL lv).instOuter ps
  have htailJ : ((((B.instL ls).instOuter hargs).instL lv).instOuter ps) =
      (B.instL ls').instOuter params' := by
    rw [VExpr.instL_instOuter, VExpr.instL_instL,
      VExpr.instOuter_instOuter _ _ _ (by simpa [hQ] using hB.instL)]
    simp [ls', params', List.map_map, Function.comp_def]
  have hLE : VExpr.LEquiv U (((B₀.instOuter hargs).instL lv).instOuter ps)
      ((B.instL ls').instOuter params') := by
    rw [← htailJ]
    exact ((hB₀.instOuter hargs).instL hlv).instOuter ps
  obtain ⟨Z, hZ, hYZ⟩ := VProjectionInfo.instantiateProjectionFields_lequiv _ hLE hY'
  refine ⟨Z, ?_, ?_⟩
  · unfold VProjectionInfo.fieldType
    rw [if_neg (by simp [hJu, hJn])]
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(B.instL ls').instOuter params', ?_, hZ⟩
    rw [hJ, VExpr.instL_wrapForalls]
    exact VProjectionInfo.instantiateProjectionParameters_wrapForalls_eq _ _ _
      (by simp [hQ])
  · intro ℓ hty
    have h2 := hFY.simAt henv.ordered henv.betaSubjectReduction hΓ _ hty
    have hYty : envS.HasType U Γ Y (.sort ℓ) := h2.hasType.2
    have h3 := (hYZ.defeq henv hΓ ⟨_, hYty⟩).of_l henv hΓ hYty
    exact h2.trans h3

/-- **Projection rules of a specialized family.** A projection
`(typeName, info)` whose type and constructor names are replaced by the
restoration lambdas `λ P, J ls hargs` and `λ P, J.c ls hargs` of a family `J`
registering the projection `infoJ` in `envS`, with matching index count,
field count and result-level guard, and with transported field types
definitionally those of `J` (`fieldTransport_of_specialization`), transports
in well-formed contexts. -/
theorem ProjectionTransportOnCtx.of_specialization {envS : VEnv} (henv : envS.WF)
    {ρ : Name → Option VExpr} {σ : Name → Name} {typeName J : Name}
    {info infoJ : VProjectionInfo} {P hargs : List VExpr} {ls : List VLevel}
    (hS : envS.projections J infoJ)
    (htn : ρ typeName = some (VExpr.wrapLams P (VExpr.mkApps (.const J ls) hargs)))
    (hσtn : σ typeName = J)
    (hctor : ρ info.ctorName =
      some (VExpr.wrapLams P (VExpr.mkApps (.const infoJ.ctorName ls) hargs)))
    (hP : P.length = info.nparams) (hargsLen : hargs.length = infoJ.nparams)
    (hlsLen : ls.length = infoJ.uvars) (hclosedJ : infoJ.ctorType.Closed)
    (hnindices : info.nindices = infoJ.nindices)
    (hguard : ∀ lv : List VLevel, (info.resultLevel.inst lv).IsNeverZero →
      (infoJ.resultLevel.inst (ls.map (·.inst lv))).IsNeverZero)
    (hnumFields : info.numFields = infoJ.numFields)
    (HF : ∀ {U : Nat} {Γ : List VExpr} {lv : List VLevel} {params : List VExpr}
      {index : Nat} {major F : VExpr},
      OnCtx Γ (envS.IsType U) → (∀ l ∈ lv, l.WF U) →
      info.fieldType typeName lv params index major = some F →
      ∃ F', infoJ.fieldType J (ls.map (·.inst lv))
          (hargs.map fun a => (a.instL lv).instOuter (params.map (·.replaceRen ρ σ))) index
          (major.replaceRen ρ σ) = some F' ∧
        ∀ {ℓ : VLevel}, envS.HasType U Γ (F.replaceRen ρ σ) (.sort ℓ) →
          envS.IsDefEq U Γ (F.replaceRen ρ σ) F' (.sort ℓ)) :
    ProjectionTransportOnCtx envS ρ σ typeName info where
  projDF := by
    intro U Γ lv params index sourceMajor F fieldLevel major indexArgs major'
      hΓ hlv hlvLen hparams hindices hfield _ hguardA ihField ihLeft ihRight
    obtain ⟨F', hF', hdef⟩ := HF hΓ hlv hfield
    have hdefF := hdef ihField
    simp only [VExpr.replaceRen_mkApps, List.map_append,
      VExpr.replaceRen_const_some htn] at ihLeft ihRight
    have hB := VExpr.BetaRed.mkApps_specialization (P := P) (J := J) (ls := ls) (lv := lv)
      (hargs := hargs) (params.map (·.replaceRen ρ σ)) (indexArgs.map (·.replaceRen ρ σ))
      (by simp [hparams, hP])
    obtain ⟨u, hTu⟩ := ihLeft.isType henv.ordered hΓ
    have hTT := hB.simAt henv.ordered henv.betaSubjectReduction hΓ _ hTu
    have ihLeft' := VEnv.IsDefEq.defeqDF hTT ihLeft
    have ihRight' := VEnv.IsDefEq.defeqDF hTT ihRight
    have hP' := VEnv.IsDefEq.projDF hS (levels := ls.map (·.inst lv))
      (fun l hl => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hl
        exact VLevel.WF.inst hlv)
      (by simp [hlsLen]) (by simp [hargsLen])
      (by simp [hindices, hnindices]) hF' hdefF.hasType.2 ihLeft' ihRight' hclosedJ
      (hguardA.imp (hguard lv) id)
    simp only [VExpr.replaceRen_proj', hσtn]
    exact .defeqDF hdefF.symm hP'
  projIota := by
    intro U Γ index lv args field F hΓ ih1 h3 ih2
    have hlen : info.nparams ≤ args.length := by
      have := (List.getElem?_eq_some_iff.mp h3).1
      omega
    simp only [VExpr.replaceRen_proj', VExpr.replaceRen_mkApps,
      VExpr.replaceRen_const_some hctor, hσtn] at ih1 ⊢
    have hsplit : args.map (·.replaceRen ρ σ) =
        (args.map (·.replaceRen ρ σ)).take P.length ++
          (args.map (·.replaceRen ρ σ)).drop P.length :=
      (List.take_append_drop _ _).symm
    rw [hsplit] at ih1 ⊢
    have hB := VExpr.BetaRed.mkApps_specialization (P := P) (J := infoJ.ctorName) (ls := ls)
      (lv := lv) (hargs := hargs) ((args.map (·.replaceRen ρ σ)).take P.length)
      ((args.map (·.replaceRen ρ σ)).drop P.length) (by simp [hP]; omega)
    have hsim := (VExpr.BetaRed.proj (n := J) (i := index) hB).simAt henv.ordered
      henv.betaSubjectReduction hΓ _ ih1
    refine hsim.trans (.projIota hS hsim.hasType.2 ?_ ih2)
    rw [List.getElem?_append_right (by simp [hargsLen])]
    simp only [List.length_map, hargsLen, Nat.add_sub_cancel_left, List.getElem?_drop,
      List.getElem?_map, hP, h3, Option.map_some]
  structEta := by
    intro U Γ lv params e hΓ hparams hnidx ih1 ih2
    simp only [VExpr.replaceRen_proj', VExpr.replaceRen_mkApps, List.map_append,
      List.map_map, Function.comp_def, VExpr.replaceRen_const_some hctor,
      VExpr.replaceRen_const_some htn, hσtn] at ih1 ih2 ⊢
    have hBT := VExpr.BetaRed.mkApps_specialization (P := P) (J := J) (ls := ls) (lv := lv)
      (hargs := hargs) (params.map (·.replaceRen ρ σ)) [] (by simp [hparams, hP])
    simp only [List.append_nil] at hBT
    obtain ⟨u, hTu⟩ := ih1.isType henv.ordered hΓ
    have hTT := hBT.simAt henv.ordered henv.betaSubjectReduction hΓ _ hTu
    have hBC := VExpr.BetaRed.mkApps_specialization (P := P) (J := infoJ.ctorName)
      (ls := ls) (lv := lv) (hargs := hargs) (params.map (·.replaceRen ρ σ))
      ((List.range info.numFields).map fun index =>
        VExpr.proj J index (e.replaceRen ρ σ)) (by simp [hparams, hP])
    have hsim := hBC.simAt henv.ordered henv.betaSubjectReduction hΓ _ ih2
    have he' := VEnv.IsDefEq.defeqDF hTT ih1
    have hC' := VEnv.IsDefEq.defeqDF hTT hsim.hasType.2
    rw [hnumFields] at hC'
    have hη := VEnv.IsDefEq.structEta hS (by simp [hargsLen]) (hnindices ▸ hnidx) he' hC'
    rw [← hnumFields] at hη
    exact hsim.trans (.defeqDF hTT.symm hη)
  unitLike := by
    intro U Γ lv params e e' hΓ hparams hnidx hnf ih1 ih2
    simp only [VExpr.replaceRen_mkApps, VExpr.replaceRen_const_some htn] at ih1 ih2 ⊢
    have hBT := VExpr.BetaRed.mkApps_specialization (P := P) (J := J) (ls := ls) (lv := lv)
      (hargs := hargs) (params.map (·.replaceRen ρ σ)) [] (by simp [hparams, hP])
    simp only [List.append_nil] at hBT
    obtain ⟨u, hTu⟩ := ih1.isType henv.ordered hΓ
    have hTT := hBT.simAt henv.ordered henv.betaSubjectReduction hΓ _ hTu
    have hU := VEnv.IsDefEq.unitLike hS (by simp [hargsLen]) (hnindices ▸ hnidx)
      (hnumFields ▸ hnf) (VEnv.IsDefEq.defeqDF hTT ih1) (VEnv.IsDefEq.defeqDF hTT ih2)
    exact .defeqDF hTT.symm hU

end VEnv

namespace VExpr

theorem ClosedN.wrapForalls_inv :
    ∀ {doms : List VExpr} {body : VExpr} {k : Nat},
      (VExpr.wrapForalls doms body).ClosedN k → body.ClosedN (k + doms.length)
  | [], _, _, h => h
  | _ :: ds, _, k, h => by
    have := ClosedN.wrapForalls_inv (doms := ds) (k := k + 1) h.2
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem forallArity_wrapForalls_mkApps_const_instOuter (c : Name) (ls : List VLevel) :
    ∀ (args doms xs : List VExpr),
      ((VExpr.wrapForalls doms (VExpr.mkApps (.const c ls) xs)).instOuter args).forallArity =
        doms.length
  | [], doms, xs => by
    simp only [instOuter_nil, forallArity_wrapForalls]
    rw [forallArity_mkApps_of_zero' _ rfl, Nat.add_zero]
  | a :: as, doms, xs => by
    rw [instOuter_cons, VExpr.wrapForalls_inst, inst_mkApps]
    simp only [inst]
    rw [forallArity_wrapForalls_mkApps_const_instOuter c ls as, VExpr.instDomains_length]

end VExpr

namespace VerifyInductive

/-- **Primary projections in well-formed contexts.** A lowered projection of
an original structure transports to the final environment, which registers
the source structure's projection: the transported lowered constructor type
beta reduces to the source constructor type. -/
theorem NestedValidatedRunResult.projectionPrimaryOnCtx_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.finalBaseVEnv →
        ∀ entry ∈ E.production.loweredDecl.projectionEntries,
          entry.typeName ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames →
          VEnv.ProjectionTransportOnCtx C.finalBaseVEnv
            ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
              fun _ => E.production.compilationSignature.params)
            (compilationRestoration sourceDecl auxiliaries).renaming
            entry.typeName entry.info := by
  intro auxiliaries D C hC hV entry hentry hTN₀
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, henvTypes, Haux, Hexpansion, -, D', Hrestoring, -⟩
  rw [D.lambdaReplacement_eq D', D.renaming_eq D']
  have hTN : entry.typeName ∉ (compilationRestoration sourceDecl aux').restorableNames :=
    fun h => hTN₀ ((D.restorable_iff D' _).mpr h)
  let r := compilationRestoration sourceDecl aux'
  have hSwf : C.finalBaseVEnv.WF := hV.tr.wf
  obtain ⟨-, -, hauxNames, hheadNames', -, -, -, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D' True.intro
  obtain ⟨-, hheadNames, hnp, hargs, hPclosed, -, -⟩ :=
    E.headerSetup wf hadded henvTypes Haux Hexpansion hnodup
  have hclosed := Restoration.lambdaReplacement_closed hnp hargs hPclosed
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hlevels := E.loweredConstructorLevels_heads wf Hsources hheadNames'
  have hordered := henvTypes.ordered
  have hPN := E.constructorProjNames_of wf hadded Haux Hexpansion hnodup
  -- source constructor types are closed types mentioning no restorable name
  have hsourceTyped : ∀ family ∈ sourceDecl.types, ∀ sc ∈ family.ctors,
      ∃ u, envTypes.HasType sourceDecl.uvars [] sc.type (.sort u) := by
    have Hsource := E.nativeSource.core
    rw [E.nativeSourceDecl_eq] at Hsource
    have htypesEq : E.nativeSource.envTypes = envTypes :=
      Option.some.inj (Hsource.typesAdded.symm.trans hadded)
    intro family hfamily sc hsc
    obtain ⟨T, -, hT⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hsource.types family hfamily
    obtain ⟨C, -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_r hT.ctors sc hsc
    obtain ⟨u, hu⟩ := hC.wf
    rw [htypesEq, hC.uvars, ← Hsource.uvars] at hu
    exact ⟨u, hu⟩
  have hsourceFree : ∀ family ∈ sourceDecl.types, ∀ sc ∈ family.ctors,
      sc.type.containsAnyConst r.restorableNames = false := by
    intro family hfamily sc hsc
    obtain ⟨u, hu⟩ := hsourceTyped family hfamily sc hsc
    exact (hu.noFreshConsts hordered hfreshAll (by intro _ h; simp at h)).1
  -- the expansion of the source families into the lowered prefix
  have hassembly := C.formationAssembly.types
  rw [C.formationExpanded, hC] at hassembly
  have hlen : sourceDecl.types.length =
      (E.production.loweredDecl.types.take sourceDecl.types.length).length := by
    have := Lean4Lean.List.Forall₂.length_eq hassembly
    simp only [List.length_append] at this
    simp only [List.length_take]
    omega
  rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types]
    at hassembly
  have hprefixExp := ((Lean4Lean.List.Forall₂.append_of_left hlen).mp hassembly).1
  have Hboth := Lean4Lean.List.Forall₂.and hprefixExp Hrestoring
  -- the lowered entry
  obtain ⟨t, ht, lc, hlct, rfl⟩ := E.production.loweredDecl.projectionEntries_origin hentry
  simp only at hTN ⊢
  have htTake : t ∈ E.production.loweredDecl.types.take sourceDecl.types.length := by
    rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types] at ht
    rcases List.mem_append.mp ht with h | h
    · exact h
    · exfalso
      apply hTN
      apply List.mem_append_left
      rw [hheadNames]
      exact mem_familyNames.mpr ⟨t, h, .inl rfl⟩
  obtain ⟨st, hst, hexpT, hrestT⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hboth t htTake
  have hlcmem : lc ∈ t.ctors := by rw [hlct]; exact List.mem_singleton_self lc
  obtain ⟨sc, hsc, hcexp⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r hexpT.constructors lc hlcmem
  obtain ⟨sc', hsc', hcrest⟩ := Lean4Lean.List.Forall₂.forall_exists_r hrestT lc hlcmem
  have hstCtors : st.ctors = [sc] := by
    have hl := Lean4Lean.List.Forall₂.length_eq hexpT.constructors
    rw [hlct] at hl
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
    rw [hx] at hsc ⊢
    rw [List.mem_singleton.mp hsc]
  have hsc'eq : sc' = sc := by
    rw [hstCtors] at hsc'
    simpa using hsc'
  rw [hsc'eq] at hcrest
  have hrestore : r.expr lc.type = some sc.type :=
    hcrest.restore (hsourceFree st hst sc hsc) (hlevels t htTake lc hlcmem)
  have hloweredUvars : E.production.loweredDecl.uvars = sourceDecl.uvars := by
    have h := C.formationAssembly.uvars
    rwa [C.formationExpanded, hC] at h
  have hloweredNparams : E.production.loweredDecl.nparams = sourceDecl.nparams := by
    have h := C.formationAssembly.nparams
    rwa [C.formationExpanded, hC] at h
  -- the registered source entry
  have hsrcEntry : (⟨st.name, ⟨sourceDecl.uvars, sourceDecl.nparams, st.numIndices,
      st.resultLevel, sc.name, sc.type⟩⟩ : VProjectionEntry) ∈
        sourceDecl.projectionEntries := by
    rw [VInductDecl.projectionEntries, List.mem_filterMap]
    exact ⟨st, hst, by simp [hstCtors]⟩
  have hS := C.canonical.recursorsAdded.le.projections
    (VEnv.addProjections_iff.mpr (Or.inl ⟨_, hsrcEntry, rfl, rfl⟩))
  have hctorName : lc.name ∉ r.restorableNames :=
    not_restorable_of_take hnodup hheadNames hauxNames
      (mem_familyNames.mpr ⟨t, htTake, .inr ⟨lc, hlcmem, rfl⟩⟩)
  have hρtn := Restoration.lambdaReplacement_eq_none_of_not_restorable
    (domains := fun _ => E.production.compilationSignature.params) hTN
  have hσtn := Restoration.renaming_eq_self hTN
  have hρctor := Restoration.lambdaReplacement_eq_none_of_not_restorable
    (domains := fun _ => E.production.compilationSignature.params) hctorName
  have hσctor := Restoration.renaming_eq_self hctorName
  have hS' : C.finalBaseVEnv.projections t.name ⟨E.production.loweredDecl.uvars,
      E.production.loweredDecl.nparams, t.numIndices, t.resultLevel, lc.name, sc.type⟩ := by
    rw [hloweredUvars, hloweredNparams, hexpT.name, hexpT.numIndices, hexpT.resultLevel,
      hcexp.name]
    exact hS
  have harity := Restoration.expr_forallArity r hrestore
  obtain ⟨u, hu⟩ := hsourceTyped st hst sc hsc
  have hscClosed : sc.type.Closed := by
    simpa using hu.closedN hordered trivial
  have hfixLc : lc.type.ProjNamesFixed r.renaming :=
    Restoration.projNamesFixed_of_avoid (hPN lc (List.mem_flatMap.mpr ⟨t, ht, hlcmem⟩))
  have hBR : VExpr.BetaRed
      (lc.type.replaceRen (r.lambdaReplacement fun _ => E.production.compilationSignature.params)
        r.renaming) sc.type :=
    Restoration.expr_betaRed
      (fun c t' h => Restoration.lambdaReplacement_shape r (fun h hh => (hnp h hh).symm) h)
      (fun c h hf => by simp [Restoration.lambdaReplacement, hf])
      (fun c hf => Restoration.renaming_of_find_none hf) hfixLc hrestore
  exact VEnv.ProjectionTransportOnCtx.of_ctorType_betaRed hSwf.ordered
    (fun _ => hSwf.betaSubjectReduction) hclosed hS' hρtn hσtn hρctor hσctor hscClosed
    harity hBR

/-- **Auxiliary projections in well-formed contexts.** A lowered projection
of an auxiliary structure-like family `A` (lowered from the specialization of
a structure-like container family `J` with constructor `J.c`) transports to
the final environment, renamed to `J`, whose projection is registered by the
installed container: the transported field types of `A` are, up to beta
reduction and level equivalence, those of `J` at the instantiated
specialization arguments. -/
theorem NestedValidatedRunResult.projectionAuxiliaryOnCtx_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.finalBaseVEnv →
        ∀ entry ∈ E.production.loweredDecl.projectionEntries,
          entry.typeName ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames →
          VEnv.ProjectionTransportOnCtx C.finalBaseVEnv
            ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
              fun _ => E.production.compilationSignature.params)
            (compilationRestoration sourceDecl auxiliaries).renaming
            entry.typeName entry.info := by
  intro auxiliaries D C hC hV entry hentry hTN₀
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, henvTypes, Haux, Hexpansion, -, D', -,
      HauxRestoring⟩
  rw [D.lambdaReplacement_eq D', D.renaming_eq D']
  have hTN : entry.typeName ∈ (compilationRestoration sourceDecl aux').restorableNames :=
    (D.restorable_iff D' _).mp hTN₀
  let r := compilationRestoration sourceDecl aux'
  have hSwf : C.finalBaseVEnv.WF := hV.tr.wf
  obtain ⟨-, -, hauxNames, hheadNames', -, -, -, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D' True.intro
  obtain ⟨-, hheadNames, hnp, hargs, hPclosed, -, -⟩ :=
    E.headerSetup wf hadded henvTypes Haux Hexpansion hnodup
  have hclosed := Restoration.lambdaReplacement_closed hnp hargs hPclosed
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hordered := henvTypes.ordered
  have hPN := E.constructorProjNames_of wf hadded Haux Hexpansion hnodup
  have hbase : (ves.venv (if isUnsafe then .unsafe else .safe)).WF := TrEnv'.wf wf.tr
  -- the final environment contains the source header environment
  have hvenvTypes : C.canonical.venvTypes = envTypes := by
    have h1 := C.canonical.typesAdded.abstract
    rw [C.typeValues, hadded] at h1
    exact (Option.some.inj h1).symm
  have hctorsAdded := C.canonical.ctorsAdded.abstract
  rw [C.constructorValues, hvenvTypes] at hctorsAdded
  have hleCtors : C.canonical.venvCtors ≤ C.finalBaseVEnv :=
    VEnv.addEliminators_addProjections_le.trans C.canonical.recursorsAdded.le
  have hle : envTypes ≤ C.finalBaseVEnv :=
    (VEnv.addConstVals_le hctorsAdded).trans hleCtors
  have hbaseLe : ves.venv (if isUnsafe then .unsafe else .safe) ≤ C.finalBaseVEnv :=
    (VEnv.addConstVals_le hadded).trans hle
  have hloweredUvars : E.production.loweredDecl.uvars = sourceDecl.uvars := by
    have h := C.formationAssembly.uvars
    rwa [C.formationExpanded, hC] at h
  have hloweredNparams : E.production.loweredDecl.nparams = sourceDecl.nparams := by
    have h := C.formationAssembly.nparams
    rwa [C.formationExpanded, hC] at h
  -- the lowered entry is an auxiliary family
  obtain ⟨t, ht, lc, hlct, rfl⟩ := E.production.loweredDecl.projectionEntries_origin hentry
  simp only at hTN ⊢
  have htDrop : t ∈ E.production.loweredDecl.types.drop sourceDecl.types.length := by
    have ht' := ht
    rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types] at ht'
    rcases List.mem_append.mp ht' with h | h
    · exact absurd hTN (not_restorable_of_take hnodup hheadNames hauxNames
        (mem_familyNames.mpr ⟨t, h, .inl rfl⟩))
    · exact h
  have hlcmem : lc ∈ t.ctors := by rw [hlct]; exact List.mem_singleton_self lc
  obtain ⟨g, hg, hexp, hexpR⟩ := Lean4Lean.List.Forall₂.forall_exists_r
    (Lean4Lean.List.Forall₂.and Hexpansion HauxRestoring) t htDrop
  obtain ⟨a, ha, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_r Haux g hg
  obtain ⟨gc, hgc, hc⟩ := Lean4Lean.List.Forall₂.forall_exists_r hexpR.constructors lc hlcmem
  have hgCtors : g.ctors.length = 1 := by
    have hl := Lean4Lean.List.Forall₂.length_eq hexpR.constructors
    rw [hlct] at hl
    simpa using hl
  obtain ⟨Psrc, hPsrcLen, hshapes⟩ := hev.constructorShapes
  obtain ⟨c, hcmem, T, hTle, hgcType⟩ := Lean4Lean.List.Forall₂.forall_exists_r hshapes gc hgc
  have hsrcCtors : a.source.ctors = [c] := by
    have hl := Lean4Lean.List.Forall₂.length_eq hshapes
    rw [hgCtors] at hl
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
    rw [hx] at hcmem ⊢
    rw [List.mem_singleton.mp hcmem]
  -- the restoration of the lowered constructor type is the generated one
  obtain ⟨sp, -, -, -, -, -, hctors⟩ := hev.application
  obtain ⟨c', hc'mem, hdc⟩ := Lean4Lean.List.Forall₂.forall_exists_r hctors gc hgc
  have hc'c : c' = c := by
    rw [hsrcCtors] at hc'mem
    simpa using hc'mem
  subst hc'c
  obtain ⟨_, hgd⟩ := hdc.type
  have hfree : gc.type.containsAnyConst r.restorableNames = false :=
    (hgd.hasType.1.noFreshConsts hordered hfreshAll (by intro _ h; simp at h)).1
  have hauxLevels : ∀ t ∈ E.production.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ t.ctors, lc.type.ConstLevelsAt (r.heads.map (·.auxiliary))
        (VLevel.params sourceDecl.uvars) := by
    have h := E.loweredAuxiliaryConstructorLevels wf Hsources
    rwa [← auxiliarySpecializations_headNames Haux Hexpansion,
      ← compilationRestoration_heads_auxiliary] at h
  have hrestore : r.expr lc.type = some gc.type :=
    hc.type.restore hfree (hauxLevels t htDrop lc hlcmem)
  -- the restoration heads of `A` and of its constructor
  have hheadsNodup : (r.heads.map (·.auxiliary)).Nodup := by
    rw [compilationRestoration_heads_auxiliary]
    exact D'.headNodup
  let hT : HeadSpecialization :=
    { auxiliary := a.auxiliary, uvars := sourceDecl.uvars, nparams := sourceDecl.nparams,
      target := a.source.name, levels := a.levels, arguments := a.arguments }
  have hTmem : hT ∈ r.heads := List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
  have htname : t.name = a.auxiliary := hexp.name.trans hev.auxiliary.symm
  have hfindT : r.heads.find? (fun h => h.auxiliary == t.name) = some hT := by
    rw [htname]
    exact Restoration.find?_of_nodup hheadsNodup hTmem
  let hCt : HeadSpecialization :=
    { auxiliary := a.constructorName c', uvars := sourceDecl.uvars,
      nparams := sourceDecl.nparams, target := c'.name, levels := a.levels,
      arguments := a.arguments }
  have hCmem : hCt ∈ r.heads :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c', hc'mem, rfl⟩)⟩
  have hlcname : lc.name = a.constructorName c' := by
    rw [hc.name, hdc.name, ← hev.auxiliary]
    rfl
  have hfindC : r.heads.find? (fun h => h.auxiliary == lc.name) = some hCt := by
    rw [hlcname]
    exact Restoration.find?_of_nodup hheadsNodup hCmem
  have hPlen : E.production.compilationSignature.params.length =
      E.production.loweredDecl.nparams := by
    rw [← hnp hT hTmem, hloweredNparams]
  -- the container's registered projection
  have hsrc : a.source ∈ a.container.types := List.getElem_mem a.family.isLt
  have hcSrc : c' ∈ a.source.ctors := by rw [hsrcCtors]; exact List.mem_singleton_self c'
  have hJentry : (⟨a.source.name, ⟨a.container.uvars, a.container.nparams,
      a.source.numIndices, a.source.resultLevel, c'.name, c'.type⟩⟩ : VProjectionEntry) ∈
        a.container.projectionEntries := by
    rw [VInductDecl.projectionEntries, List.mem_filterMap]
    exact ⟨a.source, hsrc, by simp [hsrcCtors]⟩
  have hS := (hev.installed.mono hbaseLe).projection hJentry
  -- the container constructor type
  obtain ⟨_, hsp⟩ := hev.installed.sourceParameterWF
  obtain ⟨doms, res, hctype, hn, -, hhead, harityJ⟩ :=
    (hsp.rawCtorShape a.source hsrc c' hcSrc).forallArity
  have hcsplit : c'.type = VExpr.wrapForalls (doms.take a.container.nparams)
      (VExpr.wrapForalls (doms.drop a.container.nparams) res) := by
    rw [hctype, ← VExpr.wrapForalls_append, List.take_append_drop]
  have hQlen : (doms.take a.container.nparams).length = a.arguments.length := by
    rw [hev.argumentsLength]; simp [Nat.min_eq_left hn]
  have hcconst := hev.installed.constructorConstant_mem hsrc hcSrc
  obtain ⟨u, hu⟩ := hbase.ordered.constWF hcconst
  have hcClosed : c'.type.Closed := by
    simpa using hu.closedN hbase.ordered trivial
  have hBclosed : (VExpr.wrapForalls (doms.drop a.container.nparams) res).ClosedN
      (doms.take a.container.nparams).length := by
    have h0 : c'.type.ClosedN 0 := hcClosed
    rw [hcsplit] at h0
    simpa using VExpr.ClosedN.wrapForalls_inv h0
  have hres : res = VExpr.mkApps (.const a.source.name (VLevel.params a.container.uvars))
      (VExpr.getAppFnArgs.go res []).2 := by
    have h1 := VExpr.mkApps_getAppFnArgs_eq res
    have h2 : (VExpr.getAppFnArgs.go res []).1 =
        .const a.source.name (VLevel.params a.container.uvars) := hhead
    rw [h2] at h1
    exact h1.symm
  -- index count and result level
  have hinit : E.production.initialEnv = ves.venv (if isUnsafe then .unsafe else .safe) :=
    E.production_initialEnv
  have hshape : E.production.loweredDecl.TypeShape
      (ves.venv (if isUnsafe then .unsafe else .safe)) E.production.headers.headers.params t := by
    have h := E.production.headers.headers.typeShapes t (List.mem_of_mem_drop htDrop)
    generalize E.production.headers.headers.params = hp at h ⊢
    rwa [hinit] at h
  have hlink : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      (E.production.constructors.completed.parameterScope.toCtx.reverse).reverse
      E.production.headers.commonParameterContext := by
    rw [List.reverse_reverse,
      ConstructorPhasesResult.completed_parameterScope_toCtx]
    exact VEnv.IsDefEqCtx.mono (VEnv.addConstVals_le hadded)
      (E.commonParameterContext_refl wf)
  have hparamsEq : E.production.compilationSignature.params =
      E.production.constructors.completed.parameterScope.toCtx.reverse :=
    E.production.loweredConstruction.consumedGeneration.params
  have hP : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      E.production.compilationSignature.params.reverse
      E.production.headers.commonParameterContext := by
    rw [hparamsEq]; exact hlink
  obtain ⟨d, hd, hdshape⟩ := a.directFamily_isSome sourceDecl.uvars
    E.production.compilationSignature.params hev.familyForallPrefix
    (fun _ h => hev.ctorForallPrefix h)
  obtain ⟨hni, hrl, -⟩ := auxiliaryFamily_header henvTypes (VEnv.addConstVals_le hadded)
    hev hexp hshape hloweredUvars hloweredNparams hP hd rfl (VLevel.equiv_def'.2 rfl)
  rw [hdshape.numIndices] at hni
  rw [hdshape.resultLevel] at hrl
  -- the field count
  have hTle' := hTle
  rw [hcsplit, VExpr.instL_wrapForalls] at hTle'
  obtain ⟨Q₀, B₀, hTeq, hQ₀, hB₀⟩ := hTle'.wrapForalls_inv
  have hQ₀len : Q₀.length = a.arguments.length := by
    rw [Lean4Lean.List.Forall₂.length_eq hQ₀]; simpa using hQlen
  have hnumFields : (lc.type.forallArity - E.production.loweredDecl.nparams) =
      (c'.type.forallArity - a.container.nparams) := by
    have harityA := Restoration.expr_forallArity r hrestore
    rw [← harityA, hgcType, VExpr.forallArity_wrapForalls, hTeq,
      VerifyInductive.VExpr.instantiateForallPrefix_wrapForalls _ _ _ hQ₀len,
      ((hB₀.instOuter a.arguments).forallArity_eq), hres, VExpr.instL_wrapForalls,
      VExpr.instL_mkApps, VExpr.instL,
      VExpr.forallArity_wrapForalls_mkApps_const_instOuter, harityJ, List.length_map,
      List.length_drop, hPsrcLen, hloweredNparams]
    omega
  refine VEnv.ProjectionTransportOnCtx.of_specialization hSwf
    (info := ⟨E.production.loweredDecl.uvars, E.production.loweredDecl.nparams,
      t.numIndices, t.resultLevel, lc.name, lc.type⟩)
    (infoJ := ⟨a.container.uvars, a.container.nparams, a.source.numIndices,
      a.source.resultLevel, c'.name, c'.type⟩)
    (P := E.production.compilationSignature.params) hS ?_ ?_ ?_ hPlen
    hev.argumentsLength hev.levelsLength hcClosed hni ?_ hnumFields ?_
  · unfold Restoration.lambdaReplacement
    rw [show (compilationRestoration sourceDecl aux').heads.find?
      (fun h => h.auxiliary == t.name) = some hT from hfindT]
    rfl
  · unfold Restoration.renaming
    rw [show (compilationRestoration sourceDecl aux').heads.find?
      (fun h => h.auxiliary == t.name) = some hT from hfindT]
  · unfold Restoration.lambdaReplacement
    rw [show (compilationRestoration sourceDecl aux').heads.find?
      (fun h => h.auxiliary == lc.name) = some hCt from hfindC]
    rfl
  · intro lv h
    rw [← VLevel.inst_inst]
    exact h.of_equiv (VLevel.inst_congr_l hrl)
  · have hσtn : (compilationRestoration sourceDecl aux').renaming t.name = a.source.name := by
      unfold Restoration.renaming
      rw [show (compilationRestoration sourceDecl aux').heads.find?
        (fun h => h.auxiliary == t.name) = some hT from hfindT]
    have hfixLc : lc.type.ProjNamesFixed r.renaming :=
      Restoration.projNamesFixed_of_avoid (hPN lc (List.mem_flatMap.mpr ⟨t, ht, hlcmem⟩))
    have hBR : VExpr.BetaRed
        (lc.type.replaceRen
          (r.lambdaReplacement fun _ => E.production.compilationSignature.params)
          r.renaming) gc.type :=
      Restoration.expr_betaRed
        (fun c t' h => Restoration.lambdaReplacement_shape r (fun h hh => (hnp h hh).symm) h)
        (fun c h hf => by simp [Restoration.lambdaReplacement, hf])
        (fun c hf => Restoration.renaming_of_find_none hf) hfixLc hrestore
    intro U Γ lv params index major F hΓ hlv hF
    exact VEnv.fieldTransport_of_specialization hSwf hclosed
      (info := ⟨E.production.loweredDecl.uvars, E.production.loweredDecl.nparams,
        t.numIndices, t.resultLevel, lc.name, lc.type⟩)
      (infoJ := ⟨a.container.uvars, a.container.nparams, a.source.numIndices,
        a.source.resultLevel, c'.name, c'.type⟩) (ls := a.levels)
      hσtn hBR hgcType
      (hPsrcLen.trans hloweredNparams.symm) hTle hcsplit hQlen hBclosed
      hev.argumentsLength.symm hev.levelsLength.symm hΓ hlv hF

/-- **`NestedRestoredEquationGaps` for every restoration table and final
assembly shape of the run**, with no hypothesis: the projection-name fields
are `restoredEquationProjNames_of` and `eliminatorProjNames_of`, the
auxiliary constructor lambdas are typed by
`restoredEquationAuxiliaryConstructors_of`, and the lowered projections
transport in well-formed contexts (`projectionPrimaryOnCtx_of` for original
structures, `projectionAuxiliaryOnCtx_of` for auxiliary structure-like
families). -/
theorem NestedValidatedRunResult.restoredEquationGaps
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.finalBaseVEnv →
        NestedRestoredEquationGaps E C auxiliaries := by
  refine E.restoredEquationGaps_of' wf Hsources fun auxiliaries D C hC hV =>
    ⟨E.restoredEquationAuxiliaryConstructors_of wf Hsources auxiliaries D, ?_⟩
  intro entry hentry
  by_cases hTN : entry.typeName ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames
  · exact E.projectionAuxiliaryOnCtx_of wf Hsources auxiliaries D C hC hV entry hentry hTN
  · exact E.projectionPrimaryOnCtx_of wf Hsources auxiliaries D C hC hV entry hentry hTN

/-- **`HrestoredWF` of `NestedValidatedRunResult.hruleShape_of`**: every
restored generated equation is well formed in the final abstract environment
of a final assembly shape in which the stripped output environment is valid.
This is `hrestoredWF_of_gaps` with the gaps of `restoredEquationGaps`. -/
theorem NestedValidatedRunResult.hrestoredWF_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.finalBaseVEnv →
        ∀ (k : Fin E.production.production.generationSignature.constructors.size)
          (rule : VDefEq),
          (compilationRestoration sourceDecl auxiliaries).equation
              (E.production.production.canonicalGeneration.equation k) =
            some rule →
          rule.WF C.finalBaseVEnv :=
  E.hrestoredWF_of_gaps wf Hsources (E.restoredEquationGaps wf Hsources)

end VerifyInductive

end Lean4Lean
