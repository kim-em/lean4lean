import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPendingSupplyHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRecognizedSupplyReturn

/-! # Restore pending supplies using the actual whole return path

A waiting head's source-domain typing is recovered from the native path to a
lambda and the recorded annotation path. Target-image agreement alone is not
used to infer that typing.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.liftN_lam_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
open private erase_lam_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-- A lambda reached through an ordered insertion chain has a lower lambda
shape, with the original chain on its domain and the shifted chain on its body. -/
theorem EqInsertionPath.lam_inv (blocks : EqInsertionPath)
    (E : blocks.erased e = .lam rawA rawBody) :
    ∃ A body, e = .lam A body ∧ blocks.erased A = rawA ∧
      blocks.underBinder.erased body = rawBody := by
  induction blocks generalizing e rawA rawBody with
  | nil => exact ⟨rawA, rawBody, E, rfl, rfl⟩
  | cons p blocks ih =>
    obtain ⟨n,k⟩ := p
    obtain ⟨A', body', EE, EA, EB⟩ := ih E
    obtain ⟨A, body, Ee, EAlift, EBlift⟩ := ProofShape.liftN_lam_inv EE
    refine ⟨A, body, Ee, ?_, ?_⟩
    · simpa only [EqInsertionPath.erased, EAlift] using EA
    · simpa only [EqInsertionPath.underBinder, List.map_cons, EqInsertionPath.erased, EBlift] using EB

/-- Ordered erased insertions preserve an application node. -/
theorem EqInsertionPath.erased_app (blocks : EqInsertionPath) (f x : ProofShape) :
    blocks.erased (.app f x) = .app (blocks.erased f) (blocks.erased x) := by
  induction blocks generalizing f x with
  | nil => rfl
  | cons p blocks ih =>
    cases p
    simpa only [EqInsertionPath.erased, ProofShape.liftN] using ih (f.liftN _ _) (x.liftN _ _)

variable [Params]

/-- Realize a whole path to a lambda, and align its recovered domain with the
separately recorded annotation computation. The body may be arbitrary and need
not yet be a recognized chosen spine. Both computations stay in their original
upper source scope; reflection compares their realized lower domains. -/
theorem EqFrameInsertionChain.compute_lambda_domain
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hannotation : ErasedScopedPrimitiveCertificateDescent Annotation Annotation)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hf : env.HasType univs Γ f F) (hA : env.HasType univs Γ A (.sort u))
    (RF : ScopedCompute Step (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ f)) (.lam rawA rawBody))
    (RD : ScopedCompute Annotation (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ A)) rawA) :
    ∃ C body, env.IsDefEq univs Γ f (.lam C body) F ∧
      env.IsDefEqU univs Γ C A ∧ blocks.erased (proofErase Γ C) = rawA ∧
      blocks.underBinder.erased (proofErase (C :: Γ) body) = rawBody := by
  obtain ⟨g, HF, _, EG⟩ := J.compute_certificate hstep W hf RF
  obtain ⟨rawC, rawb, Eshape, EC, Eb⟩ := blocks.lam_inv EG
  obtain ⟨C, body, rfl, _, EC₀, Eb₀⟩ := erase_lam_inv Eshape
  obtain ⟨A', HA, _, EA⟩ := J.compute_certificate hannotation W hA RD
  have EC : blocks.erased (proofErase Γ C) = rawA := EC₀ ▸ EC
  have ECA : proofErase Γ C = proofErase Γ A' := blocks.erased_injective (EC.trans EA.symm)
  obtain ⟨⟨v, hC⟩, _, _⟩ := HF.hasType.2.lam_inv henv W.actual.wf
  obtain ⟨n, HC⟩ := (proofErase_reflect W.actual.wf hC HA.hasType.2 ECA).2
    (not_isProof_of_sort W.actual.wf hC)
  exact ⟨C, body, HF, (HC.defeq W.actual.wf).trans henv W.actual.wf HA.symm.toU,
    EC, Eb₀ ▸ Eb⟩

/-- The source typing of an actual application and a native return to a
recorded lambda derive its waiting argument's typing at the original retained
domain. This closes the source-typing premise that raw supply concatenation
could not establish from chosen target images alone. -/
theorem EqFrameInsertionChain.returned_lambda_argument
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hannotation : ErasedScopedPrimitiveCertificateDescent Annotation Annotation)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (happ : env.HasType univs Γ (.app f x) T) (hA : env.HasType univs Γ A (.sort u))
    (RF : ScopedCompute Step (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ f)) (.lam rawA rawBody))
    (RD : ScopedCompute Annotation (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ A)) rawA) :
    env.HasType univs Γ x A := by
  obtain ⟨Af, Bf, hf, hx⟩ := happ.app_inv henv W.actual.wf
  obtain ⟨C, body, HF, HCA, _, _⟩ := J.compute_lambda_domain hstep hannotation W hf hA RF RD
  have hxC := HasType.app_lam_arg W.actual.wf (IsDefEq.appDF HF hx).hasType.2
  exact hxC.defeqU_r henv W.actual.wf HCA

/-- Append a typed waiting supply to a retained frame and restore its enclosing
pending vector. Only an initially empty local vector needs a new head typing;
that premise can be derived from the whole return path. Existing local heads
keep their recorded typing. Upper extras remain after all tracked arguments. -/
theorem EqRetainedArgumentSupply.append_supply
    (H : EqRetainedArgumentSupply Γ Δ σ blocks A y (supplied ++ pending) remaining raw)
    (HS : EqArgumentSupplyAt Γ Δ σ supplied actual)
    (hextra : extra = [] ∨ pending = [])
    (hhead : raw = [] → ∀ x xs, actual = x :: xs → env.HasType univs Γ x A) :
    EqRetainedArgumentSupply Γ Δ σ blocks A y pending remaining
      (raw ++ (((actual.map (proofErase Γ)).map blocks.erased) ++ extra)) := by
  obtain ⟨localChosen, localActual, localExtra, HL, hx, EP, hlocalExtra, ER⟩ := H
  have HSnil : supplied = [] → actual = [] := by
    intro he
    have hlen := HS.2.length_eq
    simp only [he, List.length_nil, List.length_map] at hlen
    exact List.length_eq_zero_iff.mp hlen.symm
  have Horder : localExtra = [] ∨ actual = [] := by
    rcases hlocalExtra with h | h
    · exact .inl h
    · exact .inr (HSnil (List.append_eq_nil_iff.mp h).1)
  refine ⟨localChosen ++ supplied, localActual ++ actual, localExtra ++ extra,
    ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact HL.1 e he
    · exact HS.1 e he
  · simpa only [List.map_append] using HL.2.append' HS.2
  · intro x xs he
    cases localActual with
    | nil =>
      have hactual : actual = x :: xs := he
      have Elocal : localExtra = [] := by
        rcases Horder with h | h
        · exact h
        · rw [h] at hactual; cases hactual
      have Eraw : raw = [] := by simpa only [List.map_nil, List.nil_append, Elocal] using ER.symm
      exact hhead Eraw x xs hactual
    | cons a args =>
      have EX := (List.cons.inj he).1
      subst x
      exact hx a args rfl
  · simpa only [List.append_assoc] using EP
  · rcases hlocalExtra with h | h
    · rcases hextra with h' | h'
      · exact .inl (by simp only [h, h', List.append_nil])
      · exact .inr h'
    · exact .inr (List.append_eq_nil_iff.mp h).2
  · rw [← ER]
    rcases Horder with rfl | rfl
    · simp only [List.map_append, List.nil_append, List.append_nil, List.append_assoc]
    · simp only [List.map_nil, List.nil_append, List.append_nil, List.append_assoc]

/-- Restore a whole waiting supply to a positive retained history. The native
return path is used only when its outer chosen lambda had no local arguments:
source application typing then derives the newly attached head's domain type.
The exact pending vectors, all inner argument records, annotations and binder
counts are preserved. The resulting wrapper equation holds for every body. -/
theorem EqPendingSupplyHistory.append_outer_supply
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (H : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ basePending Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug chosen depth)
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω blocks₀)
    (EP : basePending = supplied ++ pending₀)
    (HS : EqArgumentSupplyAt Γ₀ Δ σ₀ supplied actual)
    (hextra : extra = [] ∨ pending₀ = [])
    (happ : env.HasType univs Γ₀ (VExpr.mkApps f actual) T)
    (RF : ScopedCompute Step (proofEraseCtx Λ₀)
      (blocks₀.erased (proofErase Γ₀ f)) (plug e))
    (hd : 0 < depth) :
    ∃ plug', EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug' chosen depth ∧
      ∀ body, plug' body = ProofShape.mkApps (plug body)
        (((actual.map (proofErase Γ₀)).map blocks₀.erased) ++ extra) := by
  induction H generalizing e with
  | base => omega
  | @retained Γ Λ σ blocks pending Ψ υ plug chosen depth A u y n cd rawA' remaining args H hA hy RD HA ih =>
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base =>
        have HA : EqRetainedArgumentSupply Γ₀ Δ σ₀ blocks₀ A y (supplied ++ pending₀) remaining args := by
          simpa only [EP] using HA
        have HA' := HA.append_supply HS hextra (by
          intro hargs x xs hactual
          have ht : env.HasType univs Γ₀ (VExpr.mkApps (.app f x) xs) T := by
            simpa only [hactual, VExpr.mkApps_cons] using happ
          obtain ⟨Tx, hx⟩ := VExpr.WF.of_mkApps henv W.actual.wf ⟨_, ht⟩
          apply J.returned_lambda_argument hstep (pi_inert_stage_certificate_descent heq hs n) W hx hA
          · simpa only [id_eq, hargs, ProofShape.mkApps] using RF
          · exact RD.forget)
        refine ⟨_, EqPendingSupplyHistory.retained (args := args ++
          (((actual.map (proofErase Γ₀)).map blocks₀.erased) ++ extra)) .base hA hy RD HA', ?_⟩
        intro body; exact ProofShape.mkApps_append _ _ _
    · obtain ⟨plug', HR, EW⟩ := ih RF (by omega)
      exact ⟨_, EqPendingSupplyHistory.retained HR hA hy RD HA,
        fun body => EW (ProofShape.mkApps (.lam rawA' body) args)⟩
  | @unused Γ Λ σ blocks Ψ υ plug chosen depth A u n cd rawA' args H hA RD ih =>
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base =>
        have hp : pending₀ = [] := (List.append_eq_nil_iff.mp EP.symm).2
        subst pending₀
        refine ⟨_, EqPendingSupplyHistory.unused (args := args ++
          (((actual.map (proofErase Γ₀)).map blocks₀.erased) ++ extra)) .base hA RD, ?_⟩
        intro body; exact ProofShape.mkApps_append _ _ _
    · obtain ⟨plug', HR, EW⟩ := ih RF (by omega)
      exact ⟨_, EqPendingSupplyHistory.unused HR hA RD,
        fun body => EW (ProofShape.mkApps (.lam rawA' body) args)⟩

omit [Params] in
/-- Reconstruct an actual source-scope path through a lambda body and its
beta contraction. The body computation stays under its original domain; no
native step is transported by instantiation. This supplies the whole return
path used for source-domain alignment. -/
theorem ProofShape.ScopedCompute.lambda_return
    (HF : ScopedCompute Step Ξ f (.lam A body))
    (RB : ScopedCompute Step (A :: Ξ) body out) :
    ScopedCompute Step Ξ (.app f x) (out.inst x) :=
  (ScopedCompute.app (HF.trans (.lam .refl RB)) .refl).trans (.beta .beta)

/-- Reattach the actual waiting supply and rejoin the older history while
preserving every pending argument record. The exact source return path and
source whole-application typing discharge the new head-domain requirement.
This joins a returned history; producing such returns at every recursive cut
and proving global termination remain separate obligations. -/
theorem EqPendingSupplyHistory.restore_rejoin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (O : EqPendingSupplyHistory D Δ baseΓ baseΛ baseσ baseBlocks basePending baseTarget baseMap
      Γ₀ Λ₀ σ₀ blocks₀ pending₀ oldTarget oldMap oldPlug oldChosen oldDepth)
    (H : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ (supplied ++ pending₀) Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug chosen depth)
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω blocks₀)
    (HS : EqArgumentSupplyAt Γ₀ Δ σ₀ supplied actual)
    (hextra : extra = [] ∨ pending₀ = [])
    (happ : env.HasType univs Γ₀ (VExpr.mkApps f actual) T)
    (RF : ScopedCompute Step (proofEraseCtx Λ₀)
      (blocks₀.erased (proofErase Γ₀ f)) (plug e))
    (hd : 0 < depth) :
    ∃ (returned : ProofShape → ProofShape) (joinedTarget : List ProofShape) (joinedMap : ProofShape.Subst),
      EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
        Γ Λ σ blocks pending Ψ υ returned chosen depth ∧
      EqPendingSupplyHistory D Δ baseΓ baseΛ baseσ baseBlocks basePending baseTarget baseMap
        Γ Λ σ blocks pending joinedTarget joinedMap (fun body => oldPlug (returned body))
        (oldChosen+chosen) (oldDepth+depth) ∧
      ∀ body, returned body = ProofShape.mkApps (plug body)
        (((actual.map (proofErase Γ₀)).map blocks₀.erased) ++ extra) := by
  obtain ⟨returned, HR, EW⟩ := H.append_outer_supply heq hs hstep W J rfl HS hextra happ RF hd
  obtain ⟨joinedTarget, joinedMap, HR'⟩ := HR.rebase_endpoint oldTarget oldMap
  exact ⟨returned, joinedTarget, joinedMap, HR, O.append HR', EW⟩

/-- Restore and rejoin pending supplies after an actually consumed eta body.
The whole return path is reconstructed from the original eta step and body
path, using beta contraction in the original outer scope. Source argument
equalities restore typing of the actual waiting vector. The returned wrapper
and its pending history must still be supplied by recursive body processing;
this theorem does not assert that every body has already been processed. -/
theorem EqPendingSupplyHistory.restore_consumed_rejoin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (O : EqPendingSupplyHistory D Δ baseΓ baseΛ baseσ baseBlocks basePending baseTarget baseMap
      Γ₀ Λ₀ σ₀ blocks₀ pending₀ oldTarget oldMap oldPlug oldChosen oldDepth)
    (H : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ (supplied ++ pending₀) Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug chosen depth)
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω blocks₀)
    (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B))
    (HX : env.IsDefEq univs Γ₀ x actualX A)
    (EX : blocks₀.erased (proofErase Γ₀ actualX) = rawX)
    (HS : EqArgumentSupplyAt Γ₀ Δ σ₀ supplied actual)
    (Hargs : List.Forall₂ (env.IsDefEqU univs Γ₀) previous actual)
    (hextra : extra = [] ∨ pending₀ = [])
    (happ : env.HasType univs Γ₀ (VExpr.mkApps (.app f x) previous) T)
    (hn : ¬ IsProof Γ₀ (VExpr.mkApps (.app f x) previous))
    (HR : PiInertStage D n (proofEraseCtx Λ₀)
      (blocks₀.erased (proofErase Γ₀ f))
      (.lam (blocks₀.erased (proofErase Γ₀ A)) body))
    (RB : ScopedCompute (PiInertStage D m) (proofEraseCtx (blocks₀.actual A :: Λ₀)) body endpoint)
    (ER : endpoint.inst rawX = plug e)
    (hd : 0 < depth) :
    ∃ (returned : ProofShape → ProofShape) (joinedTarget : List ProofShape) (joinedMap : ProofShape.Subst),
      EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
        Γ Λ σ blocks pending Ψ υ returned chosen depth ∧
      EqPendingSupplyHistory D Δ baseΓ baseΛ baseσ baseBlocks basePending baseTarget baseMap
        Γ Λ σ blocks pending joinedTarget joinedMap (fun body => oldPlug (returned body))
        (oldChosen+chosen) (oldDepth+depth) ∧
      env.IsDefEq univs Γ₀ (VExpr.mkApps (.app f x) previous)
        (VExpr.mkApps (.app f actualX) actual) T ∧
      ScopedCompute (PiInertStage D (max n m)) (proofEraseCtx Λ₀)
        (blocks₀.erased (proofErase Γ₀ (.app f actualX))) (plug e) ∧
      ∀ body, returned body = ProofShape.mkApps (plug body)
        (((actual.map (proofErase Γ₀)).map blocks₀.erased) ++ extra) := by
  have HE := (IsDefEqU.mkApps_args W.actual.wf (IsDefEq.appDF hf HX).toU Hargs happ).of_l
    henv W.actual.wf happ
  have hn' : ¬ IsProof Γ₀ (VExpr.mkApps (.app f actualX) actual) :=
    fun hp => hn ((isProof_congr W.actual.wf HE).2 hp)
  have hnf := nonproof_spine_head W.actual.wf HE.hasType.2 hn'
  have RB' : ScopedCompute (PiInertStage D (max n m))
      (blocks₀.erased (proofErase Γ₀ A) :: proofEraseCtx Λ₀) body endpoint := by
    simpa only [proofEraseCtx, J.erase_actual W hA] using
      RB.mono (pi_inert_stage_mono (Nat.le_max_right n m))
  have HR' : ScopedCompute (PiInertStage D (max n m)) (proofEraseCtx Λ₀)
      (blocks₀.erased (proofErase Γ₀ f)) (.lam (blocks₀.erased (proofErase Γ₀ A)) body) :=
    .base (pi_inert_stage_mono (Nat.le_max_left n m) HR)
  have RF : ScopedCompute (PiInertStage D (max n m)) (proofEraseCtx Λ₀)
      (blocks₀.erased (proofErase Γ₀ (.app f actualX))) (plug e) := by
    simpa only [proofErase, if_neg hnf, EqInsertionPath.erased_app, EX, ER] using
      (HR'.lambda_return (x := rawX) RB')
  obtain ⟨returned, Ξ, χ, HRout, Hjoined, EW⟩ := EqPendingSupplyHistory.restore_rejoin
    heq hs (pi_inert_stage_certificate_descent heq hs (max n m)) O H W J HS hextra HE.hasType.2 RF hd
  exact ⟨returned, Ξ, χ, HRout, Hjoined, HE, RF, EW⟩

end Lean4Lean.VEnv.Strengthening
