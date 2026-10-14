import Lean4Lean.Theory.Typing.Strengthening.ProofIndexReconstruction
import Lean4Lean.Theory.Typing.Strengthening.SingletonUnindexedTelescope

/-! # Registered singleton telescopes with proof indices

The actual indexed recursor telescope supplies a generic extraction occurrence.
Propositional indices then validate reconstruction without constructor fields
among the telescope's assumptions.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofIndexedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature
variable {env : VEnv} {data : RecursorData}

/-- The registered recursor's complete telescope, retaining its index binders. -/
theorem type_shape (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E) :
    (data.recursorInstance.recursorType data.owner).instL levels =
      wrapForalls (data.propParams levels ++
        (data.recursorInstance.motives ++ data.recursorInstance.minors).map (·.instL levels) ++
        insertBinders S.indices 2 ++
        [mkApps E.family (vars (data.propParams levels).length (2 + S.indices.length) ++
          vars S.indices.length 0)])
        (mkApps (.bvar (S.indices.length + 2)) (vars S.indices.length 1 ++ [.bvar 0])) := by
  obtain ⟨k, hk, hfam, hcs, hrest, hS0, hE0, hP, hgl, hseq⟩ :=
    RecursorData.singleton_shape H hlarge hzero howner
  rw [hS0] at hS
  cases Option.some.inj hS
  rw [hE0] at hE
  cases Option.some.inj hE
  have hmot : data.recursorInstance.motives =
      [data.recursorInstance.motive data.schema.signature.families[data.owner] 0] := by
    have ho : data.owner.val = 0 := by have := data.owner.isLt; omega
    simp [Instance.motives, Instance.toList_of_size_one data.schema.signature.families hfam data.owner, ho]
  have hmin : data.recursorInstance.minors =
      [data.recursorInstance.minor data.schema.signature.constructors[index] 0] := by
    have hi : index.val = 0 := by have := index.isLt; omega
    simp [Instance.minors, Instance.toList_of_size_one data.schema.signature.constructors hcs index, hi]
  rw [Instance.recursorType_singletonShape data.recursorInstance hfam hcs _ index, hmot, hmin]
  simp only [instL_wrapForalls, List.map_append, List.map_cons, List.map_nil,
    VExpr.instL, instL_mkApps, vars_instL, List.append_assoc]
  simp only [RecursorData.propParams, Instance.singletonElim, Instance.familyApp,
    InductiveSignature.familyApp, Instance.singletonCast, Instance.indicesAt,
    List.length_map, Instance.params, hgl, List.map_map, Function.comp_def, instL_instL]
  simp only [insertBinders, List.zipIdx_map, List.map_map, Function.comp_def, instL_liftN, Prod.map_fst, Prod.map_snd, instL_instL,
    instL_mkApps, instL, vars_instL, List.map_append]
  rfl

/-- Fresh parameters, motive, minor and indices provide the extraction's
parameter/index/major telescope after discarding the motive and minor slots. -/
theorem generic_major_args (henv : env.WF)
    (W : E.WF S P env U) (hX : X.length = 2)
    (ht : env.HasType U [] source (wrapForalls
      (P ++ X ++ insertBinders S.indices 2 ++
        [mkApps E.family (vars P.length (2 + S.indices.length) ++ vars S.indices.length 0)]) result)) :
    let Δ := (P ++ X ++ insertBinders S.indices 2 ++
      [mkApps E.family (vars P.length (2 + S.indices.length) ++ vars S.indices.length 0)]).reverse
    OnCtx Δ (env.IsType U) ∧
      TelInst env U Δ (P ++ X) (vars (P.length + 2) (S.indices.length + 1)) ∧
      TelInst env U Δ (P ++ S.indices ++ [PropElim.majorTy S P E])
        (vars P.length (S.indices.length + 3) ++ vars S.indices.length 1 ++ [.bvar 0]) := by
  let I := S.indices
  let M := mkApps E.family (vars P.length (2 + I.length) ++ vars I.length 0)
  let D := P ++ X ++ insertBinders I 2 ++ [M]
  have hlen : D.length = P.length + 2 + I.length + 1 := by simp [D, hX, Nat.add_assoc]
  have hctx := (ht.etaOpen_wf henv.ordered (by trivial)).1
  simp only [List.append_nil] at hctx
  obtain ⟨_, htype⟩ := ht.isType henv.ordered (by trivial)
  have hclosed := htype.closedN henv.ordered (by trivial)
  have hdoms : ∀ j (hj : j < D.length), D[j].ClosedN j := by
    intro j hj
    simpa only [List.length_nil, Nat.zero_add] using closed_wrapForalls_domain hclosed (i := j) hj
  have hid := TelInst.ident (env := env) (U := U) [] hdoms
  simp only [List.append_nil] at hid
  have hvars : bvarRange D.length D.length =
      vars (P.length + 2 + I.length) 1 ++ [.bvar 0] := by
    rw [hlen, ← vars_eq_bvarRange_add (P.length + 2 + I.length + 1) 0, vars_add]
    rfl
  rw [hvars] at hid
  have HA : TelInst env U D.reverse (P ++ X ++ insertBinders I 2)
      (vars (P.length + 2 + I.length) 1) := by
    have HH := hid.take (doms := P ++ X ++ insertBinders I 2) (more := [M])
    rwa [List.take_left' (by simp [hX, Nat.add_assoc])] at HH
  have hsplit : vars (P.length + 2 + I.length) 1 =
      vars P.length (I.length + 3) ++ vars 2 (I.length + 1) ++ vars I.length 1 := by
    rw [vars_add (P.length + 2), vars_add P.length]
    simp [Nat.add_assoc, Nat.add_comm]
  have HPX : TelInst env U D.reverse (P ++ X) (vars (P.length + 2) (I.length + 1)) := by
    have HH := HA.take (doms := P ++ X) (more := insertBinders I 2)
    rw [vars_add (P.length + 2), List.take_left' (by simp [hX])] at HH
    exact HH
  have HPI : TelInst env U D.reverse (P ++ I)
      (vars P.length (I.length + 3) ++ vars I.length 1) := by
    apply TelInst.drop_mid (M := X) (m := vars 2 (I.length + 1)) ?_ (by simp) (by simp [hX])
      W.typed.scope.indices
    rw [hsplit] at HA
    simpa only [insertBinders_eq_mapIdx, hX] using HA
  have hm : env.HasType U D.reverse (.bvar 0)
      (mkApps E.family (vars P.length (I.length + 3) ++ vars I.length 1)) := by
    have HH : env.HasType U (M :: (P ++ X ++ insertBinders I 2).reverse) (.bvar 0) M.lift :=
      .bvar .zero
    simpa only [D, M, List.reverse_append, List.reverse_singleton, List.singleton_append,
      liftN_mkApps, W.family_closed.liftN_eq (Nat.zero_le _), List.map_append, vars_map_lift,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using HH
  refine ⟨hctx, HPX, HPI.append_one ?_⟩
  rw [W.majorTy_instOuter (by simp) (by simp [I])]
  exact hm

/-- Registration supplies the typed reconstruction at the complete fresh
indexed telescope. The only extra semantic premise says that the declared
index domains are propositions; no occurrence alignment is assumed. -/
theorem registered_reconstruction (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF U) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hindices : PropTelescope env U (data.propParams levels).reverse S.indices) :
    let P := data.propParams levels
    let X := (data.recursorInstance.motives ++ data.recursorInstance.minors).map (·.instL levels)
    let n := S.indices.length
    let Δ := (P ++ X ++ insertBinders S.indices 2 ++
      [mkApps E.family (vars P.length (2 + n) ++ vars n 0)]).reverse
    let ps := vars P.length (n + 3)
    let idx := vars n 1
    let fields := (PropElim.occ S P E ps idx (.bvar 0) S.fields.length).2
    OnCtx Δ (env.IsType U) ∧
      TelInst env U Δ (P ++ X) (vars (P.length + 2) (n + 1)) ∧
      TelInst env U Δ (P ++ S.indices ++ [PropElim.majorTy S P E]) (ps ++ idx ++ [.bvar 0]) ∧
      TelInst env U Δ (P ++ S.fields) (ps ++ fields) ∧
      env.IsDefEq U Δ (.bvar 0) (mkApps E.ctor (ps ++ fields))
        (mkApps E.family (ps ++ idx)) := by
  obtain ⟨S', E', hS', hE', W⟩ := RecursorData.propElim_wf henv H hlarge hzero hw hlen ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  cases Option.some.inj (hE'.symm.trans hE)
  have F := RecursorData.singletonSignature H hlarge hzero
  have hcs : data.schema.signature.constructors.size = 1 := by
    have := index.isLt
    have := F.constructors
    omega
  have hX : ((data.recursorInstance.motives ++ data.recursorInstance.minors).map (·.instL levels)).length = 2 := by
    simp [Instance.motives, Instance.minors, F.families, hcs]
  have ht := HasType.const (Γ := []) F.recursor hw hlen
  rw [type_shape H hlarge hzero howner hS hE] at ht
  obtain ⟨hΔ, hprefix, hargs⟩ := generic_major_args henv W hX ht
  have hslot := RecursorData.singleton_slot_lt H hlarge hzero howner hS
  have hfields := PropElim.proof_indices_occ_typed henv heq W hΔ hindices hslot (by simp) hargs
  have heta := PropElim.proof_indices_singleton_eta henv heq W hΔ hindices hslot (by simp) hargs
  rw [W.majorTy_instOuter (by simp) (by simp)] at heta
  exact ⟨hΔ, hprefix, hargs, hfields, heta⟩

end Lean4Lean.VEnv.Strengthening.ProofIndexedSingleton
