import Lean4Lean.Theory.Typing.Strengthening.ProofIndexTelescope
import Lean4Lean.Theory.Typing.Strengthening.GuardedSingletonReconstruction

/-! # Typed arguments of opened singleton prefixes

The declared recursor telescope supplies the extraction occurrence at any typed
prefix. Parameters, motive/minor arguments, and indices may already be supplied;
only the residual telescope is opened.
-/
namespace Lean4Lean.VEnv
open VExpr

/-- A typed syntactic telescope walk provides every dependent argument domain. -/
theorem InstForallsC.telInst
    (H : InstForallsC env U Γ (wrapForalls doms body) args res)
    (hlen : args.length = doms.length) : TelInst env U Γ doms args := by
  refine ⟨hlen, ?_⟩
  intro j hj hd
  rw [wrapForalls_split doms body j hd, ← List.take_append_drop j args] at H
  obtain ⟨mid, hpre, htail⟩ := H.append_inv
  have hmid := hpre.wrapForalls_eq (by simp; omega)
  rw [instOuter_forallE] at hmid
  subst mid
  rw [List.drop_eq_getElem_cons hj] at htail
  cases htail with
  | cons ha _ => exact ha

/-- A fully supplied well-typed spine instantiates its literal declaration telescope. -/
theorem HasType.mkApps_telInst (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ f (wrapForalls doms body))
    (H : VExpr.WF env U Γ (mkApps f args)) (hlen : args.length = doms.length) :
    TelInst env U Γ doms args := by
  obtain ⟨_, hwalk, _⟩ := hf.mkApps_telescope henv hΓ H (by
    rw [hlen]; exact takeForalls_wrapForalls _ _)
  exact hwalk.telInst hlen

end Lean4Lean.VEnv

namespace Lean4Lean.VEnv.Strengthening.GuardedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature
variable {S : SingletonLayout} {P X ps xs idx : List VExpr} {E : PropElim}

/-- The major's declaration skips the motive/minor arguments when instantiated. -/
theorem major_instOuter (hfamily : E.family.Closed)
    (hps : ps.length = P.length) (hxs : xs.length = 2) (hidx : idx.length = S.indices.length) :
    (mkApps E.family (vars P.length (2 + S.indices.length) ++ vars S.indices.length 0)).instOuter
      (ps ++ xs ++ idx) = mkApps E.family (ps ++ idx) := by
  have hlen : (ps ++ xs ++ idx).length = P.length + 2 + S.indices.length := by
    simp [hps, hxs, hidx, Nat.add_assoc]
  simp only [instOuter_mkApps, instOuter_closed0 hfamily, List.map_append, vars_eq_bvarRange_add]
  rw [instOuter_bvarRange _ _ _ (by omega) (by omega),
    instOuter_bvarRange _ _ _ (by omega) (by omega), hlen]
  rw [show P.length + 2 + S.indices.length - (P.length + (2 + S.indices.length)) = 0 by omega,
    List.drop_zero, List.append_assoc, List.take_left' hps]
  rw [show P.length + 2 + S.indices.length - (S.indices.length + 0) = (ps ++ xs).length by
    simp [hps, hxs], ← List.append_assoc, List.drop_left, ← hidx, List.take_length]

/-- Remove motive and minor from a typed full recursor argument instance,
retaining the original dependent index and major types. -/
theorem full_major_args (W : E.WF S P env U) (hX : X.length = 2)
    (hps : ps.length = P.length) (hxs : xs.length = X.length) (hidx : idx.length = S.indices.length)
    (H : TelInst env U Γ
      (P ++ X ++ insertBinders S.indices 2 ++
        [mkApps E.family (vars P.length (2 + S.indices.length) ++ vars S.indices.length 0)])
      (ps ++ xs ++ idx ++ [m])) :
    TelInst env U Γ (P ++ X) (ps ++ xs) ∧
    TelInst env U Γ (P ++ S.indices ++ [PropElim.majorTy S P E]) (ps ++ idx ++ [m]) := by
  let M := mkApps E.family (vars P.length (2 + S.indices.length) ++ vars S.indices.length 0)
  have hpre : TelInst env U Γ (P ++ X ++ insertBinders S.indices 2) (ps ++ xs ++ idx) := by
    have h := H.take (doms := P ++ X ++ insertBinders S.indices 2) (more := [M])
    rwa [List.take_left' (by simp [hps, hxs, hX, hidx])] at h
  have hpx : TelInst env U Γ (P ++ X) (ps ++ xs) := by
    have h := hpre.take (doms := P ++ X) (more := insertBinders S.indices 2)
    rwa [List.take_left' (by simp [hps, hxs])] at h
  have hpi : TelInst env U Γ (P ++ S.indices) (ps ++ idx) := by
    apply TelInst.drop_mid (M := X) (m := xs) ?_ hps hxs W.typed.scope.indices
    simpa only [insertBinders_eq_mapIdx, hX] using hpre
  have hm : env.HasType U Γ m (mkApps E.family (ps ++ idx)) := by
    have h := H.getD (j := (P ++ X ++ insertBinders S.indices 2).length) (by simp)
    have hl : (ps ++ xs ++ idx).length = (P ++ X ++ insertBinders S.indices 2).length := by
      simp [hps, hxs, hX, hidx]
    rw [getD_append_right' (by omega), getD_append_right' (Nat.le_refl _),
      show (P ++ X ++ insertBinders S.indices 2).length - (ps ++ xs ++ idx).length = 0 by omega,
      Nat.sub_self, List.getD_cons_zero, List.take_left' hl] at h
    simp only [List.getD_cons_zero] at h
    rwa [major_instOuter W.family_closed hps (hxs.trans hX) hidx] at h
  refine ⟨hpx, hpi.append_one ?_⟩
  rwa [PropElim.majorTy_at W hps hidx]

/-- The generated opened spine ends in the fresh major and splits into exactly
the parameter, motive/minor and index slices used by reconstruction. -/
theorem openedArguments_split {data : RecursorData}
    (hio : data.indexOffset = data.numParams + 2) (hb : args.length ≤ data.majorOffset) :
    let all := data.openedArguments args
    all = all.take data.numParams ++ (all.drop data.numParams).take 2 ++
      (all.drop data.indexOffset).take data.numIndices ++ [.bvar 0] ∧
    (all.take data.numParams).length = data.numParams ∧
    ((all.drop data.numParams).take 2).length = 2 ∧
    ((all.drop data.indexOffset).take data.numIndices).length = data.numIndices := by
  let n := data.majorOffset + 1 - args.length
  have hn : n = (n - 1) + 1 := by dsimp [n]; omega
  have hlast : data.openedArguments args =
      (args.map (·.liftN n) ++ vars (n - 1) 1) ++ [.bvar 0] := by
    unfold RecursorData.openedArguments
    change args.map (·.liftN n) ++ vars n 0 = _
    conv => lhs; arg 2; rw [hn, vars_add]
    rw [← List.append_assoc]
    rfl
  have hpref : (args.map (·.liftN n) ++ vars (n - 1) 1).length = data.majorOffset := by
    simp only [List.length_append, List.length_map, vars, List.length_reverse, List.length_map, List.length_range]
    dsimp [n]; omega
  have hlen : (data.openedArguments args).length = data.majorOffset + 1 := by
    rw [hlast]; simp only [List.length_append, hpref, List.length_singleton]
  have hwhole : (data.openedArguments args).take data.majorOffset ++ [.bvar 0] =
      data.openedArguments args := by
    rw [hlast, List.take_left' hpref]
  have hmajor : data.majorOffset = data.numParams + 2 + data.numIndices := by
    rw [RecursorData.majorOffset, hio]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmajor, List.take_add, List.take_add, ← hio] at hwhole
    exact hwhole.symm
  · simp [List.length_take, hlen, hmajor]; omega
  · simp [List.length_take, List.length_drop, hlen, hmajor]; omega
  · simp [List.length_take, List.length_drop, hlen, hmajor, hio]; omega

/-- A typed prefix's opened spine has the complete literal declaration type.
This statement uses only generation and registration, without reconstruction. -/
theorem opened_spine_typed (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : RecursorRegistered env data) (hw : ∀ l ∈ levels, l.WF U)
    (hg : data.singletonUnfolding env U levels args = some program)
    (ht : VExpr.WF env U Γ (mkApps (.const data.name levels) args)) :
    OnCtx (program.domains.reverse ++ Γ) (env.IsType U) ∧
    env.HasType U (program.domains.reverse ++ Γ)
      (mkApps (.const data.name levels) (data.openedArguments args)) program.result := by
  have hsrc := H.prefixType henv hΓ hw hg ht
  obtain ⟨hctx, hopen⟩ := hsrc.etaOpen_wf henv.ordered hΓ
  obtain ⟨_, _, _, _, hlen, _⟩ := RecursorData.singletonUnfolding_layout hg
  refine ⟨hctx, ?_⟩
  rw [etaOpen_spine, liftN_mkApps] at hopen
  simpa only [liftN, ← mkApps_append, hlen, RecursorData.openedArguments] using hopen

/-- At any typed registered prefix, the opened argument slices instantiate the
extraction telescope. The residual binders and supplied arguments are both
read from the actual generated program. -/
theorem registered_opened_args (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF U) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env U levels args = some program)
    (ht : VExpr.WF env U Γ (mkApps (.const data.name levels) args))
    (W : E.WF S (data.propParams levels) env U) :
    let all := data.openedArguments args
    let ps := all.take data.numParams
    let xs := (all.drop data.numParams).take 2
    let idx := (all.drop data.indexOffset).take data.numIndices
    let Δ := program.domains.reverse ++ Γ
    let X := (data.recursorInstance.motives ++ data.recursorInstance.minors).map (·.instL levels)
    OnCtx Δ (env.IsType U) ∧
    ps.length = (data.propParams levels).length ∧ xs.length = X.length ∧
    idx.length = S.indices.length ∧ all = ps ++ xs ++ idx ++ [.bvar 0] ∧
    TelInst env U Δ (data.propParams levels ++ X) (ps ++ xs) ∧
    TelInst env U Δ (data.propParams levels ++ S.indices ++ [PropElim.majorTy S (data.propParams levels) E])
      (ps ++ idx ++ [.bvar 0]) := by
  have F := RecursorData.singletonSignature H hlarge hzero
  have hcs : data.schema.signature.constructors.size = 1 := by
    have := index.isLt; have := F.constructors; omega
  let X := (data.recursorInstance.motives ++ data.recursorInstance.minors).map (·.instL levels)
  have hX : X.length = 2 := by simp [X, Instance.motives, Instance.minors, F.families, hcs]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hio, _, _⟩ :=
    RecursorData.singleton_equation_syntax H hlarge hzero hlen howner hS hE
  have hp := (RecursorData.singletonLayout_lengths hS).2
  have hi := (RecursorData.singletonLayout_lengths hS).1
  have hio' : data.indexOffset = data.numParams + 2 := by simpa only [hp] using hio
  obtain ⟨hall, hps, hxs, hidx⟩ := openedArguments_split hio' (RecursorData.singletonUnfolding_spec hg).1
  have hps := hps.trans hp.symm
  have hxs := hxs.trans hX.symm
  have hidx := hidx.trans hi.symm
  obtain ⟨hctx, hopen⟩ := opened_spine_typed henv hΓ H hw hg ht
  have hc := HasType.const (Γ := program.domains.reverse ++ Γ) F.recursor hw hlen
  rw [ProofIndexedSingleton.type_shape H hlarge hzero howner hS hE] at hc
  have htel := hc.mkApps_telInst henv hctx (show VExpr.WF env U _ _ from ⟨_, hopen⟩) (by
    rw [hall]
    simp only [List.length_append, List.length_singleton, Instance.length_insertBinders,
      hps, hxs, hidx]
    rfl)
  rw [hall] at htel
  obtain ⟨hpx, hmajor⟩ := full_major_args W hX hps hxs hidx htel
  exact ⟨hctx, hps, hxs, hidx, hall, hpx, hmajor⟩

end Lean4Lean.VEnv.Strengthening.GuardedSingleton
