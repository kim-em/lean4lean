import Lean4Lean.Theory.Typing.Strengthening.ProofIndexTelescope
import Lean4Lean.Theory.Typing.Strengthening.ClosedSingletonUnfolding

/-! # Closed unfolding at dependent proof indices

Registration and propositional index domains validate the actual generated
zero-prefix program. Later prefixes specialize that closed equation by beta.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofIndexedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature
variable {env : VEnv} {data : RecursorData}

/-- Substituting the equation's captures retains the reconstructed indices. -/
theorem lhs_instOuter {ci ps xs fs : List VExpr} (hctor : ctor.Closed)
    (hci : ∀ x ∈ ci, x.ClosedN (np + nf))
    (hps : ps.length = np) (hxs : xs.length = 2) (hfs : fs.length = nf) :
    (VExpr.app (mkApps (.const name levels)
      (vars (np + 2) nf ++ ci.map (·.liftN 2 nf)))
      (mkApps ctor (vars np (2 + nf) ++ vars nf 0))).instOuter (ps ++ xs ++ fs) =
      .app (mkApps (.const name levels) (ps ++ xs ++ ci.map (·.instOuter (ps ++ fs))))
        (mkApps ctor (ps ++ fs)) := by
  have hbase := ClosedSingleton.lhs_instOuter (name := name) (levels := levels) hctor hps hxs hfs
  simp only [instOuter_app', instOuter_mkApps, instOuter_const] at hbase ⊢
  have hlen : (ps ++ xs ++ fs).length = np + 2 + nf := by simp [hps, hxs, hfs, Nat.add_assoc]
  have hp : (vars (np + 2) nf).map (·.instOuter (ps ++ xs ++ fs)) = ps ++ xs := by
    rw [ClosedSingleton.vars_instOuter hlen, List.take_left' (by simp [hps, hxs])]
  rw [hp] at hbase
  have hctor' := (VExpr.app.inj hbase).2
  rw [hctor', List.map_append, hp]
  congr 2
  rw [List.map_map]
  apply congrArg (fun ys => ps ++ xs ++ ys)
  apply List.map_congr_left
  intro x hx
  have hh := instOuter_liftN_skip (X := x) (A := ps ++ xs) (B := fs) (P := np) (r := 2)
    (by simpa [hfs] using hci x hx) (by simp [hps, hxs])
  simpa only [hfs, List.take_left' hps, Function.comp_def] using hh

/-- The generated closed program is a valid recursor equation when all declared
indices are propositions. It needs no occurrence-specific unfolding check. -/
theorem zero_equation_exists (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF U) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S)
    (hindices : PropTelescope env U (data.propParams levels).reverse S.indices) :
    ∃ program, data.singletonUnfolding env U levels [] = some program ∧
      env.IsDefEqU U [] (.const data.name levels) program.rhs := by
  obtain ⟨S', E, hS', hE, W⟩ := RecursorData.propElim_wf henv H hlarge hzero hw hlen ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  obtain ⟨D, lb, rb, tb, X, hgen, hseq, hext, hD, hX, hlb, hio, hrt, hXdef⟩ :=
    RecursorData.singleton_equation_syntax H hlarge hzero hlen howner hS hE
  let P := data.propParams levels
  let n := S.indices.length
  let Δ := P ++ X ++ insertBinders S.indices 2 ++
    [mkApps E.family (vars P.length (2 + n) ++ vars n 0)]
  let result := mkApps (.bvar (n + 2)) (vars n 1 ++ [.bvar 0])
  let ps := vars P.length (n + 3)
  let xs := vars 2 (n + 1)
  let idx := vars n 1
  let fs := (PropElim.occ S P E ps idx (.bvar 0) S.fields.length).2
  let caps := ps ++ xs ++ fs
  have hnp : P.length = data.numParams := (RecursorData.singletonLayout_lengths hS).2
  have hni : n = data.numIndices := (RecursorData.singletonLayout_lengths hS).1
  have hmajor : data.majorOffset = P.length + 2 + n := by
    simp only [RecursorData.majorOffset, hio]; rw [← hni]
  have hΔlen : Δ.length = P.length + 2 + n + 1 := by simp [Δ, hX, n, Nat.add_assoc]
  have hflen : fs.length = S.fields.length := (PropElim.occ_length S P E _ _ _ _).2
  have hDlen : D.length = P.length + 2 + S.fields.length := by
    have HH := congrArg List.length hD
    simpa only [List.length_map, List.length_append, Instance.length_insertBinders, hX] using HH
  have hcaplen : caps.length = D.length := by simp [caps, ps, xs, hflen, hDlen, Nat.add_assoc]
  have htype : (data.recursorInstance.recursorType data.owner).instL levels = wrapForalls Δ result := by
    simpa only [Δ, P, result, n, hXdef] using type_shape H hlarge hzero howner hS hE
  have ht : env.HasType U [] (.const data.name levels) (wrapForalls Δ result) := by
    rw [← htype]
    exact .const (H.recursorType hrt) hw hlen
  have hrec := registered_reconstruction henv heq H hlarge hzero hw hlen howner hS hE hindices
  rw [← hXdef] at hrec
  obtain ⟨hctx, hprefix, hargs, hfields, heta⟩ := hrec
  change OnCtx Δ.reverse (env.IsType U) at hctx
  change TelInst env U Δ.reverse (P ++ X) (vars (P.length + 2) (n + 1)) at hprefix
  change TelInst env U Δ.reverse (P ++ S.indices ++ [PropElim.majorTy S P E])
    (ps ++ idx ++ [.bvar 0]) at hargs
  change TelInst env U Δ.reverse (P ++ S.fields) (ps ++ fs) at hfields
  change env.IsDefEq U Δ.reverse (.bvar 0) (mkApps E.ctor (ps ++ fs))
    (mkApps E.family (ps ++ idx)) at heta
  have hsplit : vars (P.length + 2) (n + 1) = ps ++ xs := by
    rw [vars_add P.length 2 (n + 1)]
    simp only [ps, xs, show 2 + (n + 1) = n + 3 by omega]
  rw [hsplit] at hprefix
  have hcapT : TelInst env U Δ.reverse (D.map (·.instL levels)) caps := by
    rw [hD]
    have HH := ClosedSingleton.captures_typed hprefix hfields (by simp [ps])
      (by simp [xs, hX]) W.typed.scope.fields
    simpa only [hX] using HH
  have hC := RecursorData.propElim_closed henv H hlarge hzero hS hE
  have hleft : (lb.instL levels).instOuter caps =
      .app (mkApps (.const data.name levels) (ps ++ xs ++ E.ctorIndices.map (·.instOuter (ps ++ fs))))
        (mkApps E.ctor (ps ++ fs)) := by
    rw [hlb, hio]
    exact lhs_instOuter W.ctor_closed hC.ctorIndices (by simp [ps, P]) (by simp [xs]) hflen
  have hopened : etaOpen Δ.length (.const data.name levels) =
      mkApps (.const data.name levels) (ps ++ xs ++ idx ++ [.bvar 0]) := by
    rw [hΔlen, etaOpen_spine, vars_add (P.length + 2 + n) 1 0,
      vars_add (P.length + 2) n 1, hsplit]
    rfl
  have hopen := (ht.etaOpen_wf henv.ordered (by trivial)).2
  simp only [List.append_nil] at hopen
  rw [hopened] at hopen
  have hia : TelInst env U Δ.reverse (P ++ S.indices) (ps ++ idx) := by
    have HH := hargs.take (doms := P ++ S.indices) (more := [PropElim.majorTy S P E])
    simpa [ps, idx, n, List.take_append, List.take_of_length_le] using HH
  have hidxeq : List.Forall₂ (env.IsDefEqU U Δ.reverse) idx
      (E.ctorIndices.map (·.instOuter (ps ++ fs))) := by
    apply Lean4Lean.List.forall₂_of_getElem (by simp [idx, n, W.ctorIndices_length])
    intro j hj hj'
    have hh := PropElim.proof_indices_eq henv W hctx hindices (by simp [ps, P]) hia hfields
      (k := j) (by simpa [idx, n] using hj)
    rw [getD_of_lt hj, getD_of_lt (by simpa [W.ctorIndices_length, idx, n] using hj)] at hh
    exact ⟨_, by simpa only [List.getElem_map] using hh⟩
  have hprefixeq : List.Forall₂ (env.IsDefEqU U Δ.reverse) (ps ++ xs) (ps ++ xs) :=
    Lean4Lean.List.forall₂_of_getElem rfl fun j hj _ =>
      ⟨_, hprefix.2 j hj (by rw [← hprefix.1]; exact hj)⟩
  have hspine : ConstSpineDefEq env U Δ.reverse
      (mkApps (.const data.name levels) (ps ++ xs ++ idx ++ [.bvar 0]))
      ((lb.instL levels).instOuter caps) := by
    rw [hleft, ← mkApps_snoc]
    exact ⟨_, _, _, _, _, rfl, rfl, hw, hw,
      Lean4Lean.List.Forall₂.rfl (fun _ _ => rfl),
      (hprefixeq.append' hidxeq).append' (.cons ⟨_, heta⟩ .nil)⟩
  have hreplace := hspine.defeq henv hctx hopen
  have hpe := H.patEquation_of_empty henv (RecursorData.singletonSignature H hlarge hzero).restoration hgen
  have hiota := hpe.instOuter hctx hw hlen hext hcaplen
    (by simpa only [List.getElem_map, List.length_map] using hcapT.2)
    (hreplace.of_l henv hctx hopen).hasType.2
  have hbody := (hreplace.trans henv hctx hiota).of_l henv hctx hopen
  rw [← hopened] at hbody
  have he : env.IsDefEq U [] (.const data.name levels)
      (wrapLams Δ ((rb.instL levels).instOuter caps)) (wrapForalls Δ result) :=
    (ht.etaOpen_defeq henv (by trivial)).trans
      ((show env.IsDefEq U (Δ.reverse ++ []) _ _ _ by simpa using hbody).etaOpen_wrapLams
        (by trivial) (by simpa using hctx))
  let program : RecursorData.PrefixUnfolding :=
    ⟨Δ, result, mkApps E.ctor (ps ++ fs),
      ⟨data.uvars, wrapLams D lb, wrapLams D rb, wrapForalls D tb⟩,
      ⟨D, lb, rb, tb⟩, caps, levels⟩
  refine ⟨program, ?_, ?_⟩
  · have hall : vars (data.majorOffset + 1) 0 = ps ++ xs ++ idx ++ [.bvar 0] := by
      rw [hmajor, vars_add (P.length + 2 + n) 1 0, vars_add (P.length + 2) n 1, hsplit]
      rfl
    have htakeP : (ps ++ xs ++ idx ++ [VExpr.bvar 0]).take data.numParams = ps := by
      rw [← hnp, List.append_assoc, List.append_assoc, List.take_left' (by simp [ps])]
    have htakeI : (ps ++ xs ++ idx ++ [VExpr.bvar 0]).take data.indexOffset = ps ++ xs := by
      rw [hio, List.append_assoc (ps ++ xs), List.take_left' (by simp [ps, xs, P])]
    have hidx : ((ps ++ xs ++ idx ++ [VExpr.bvar 0]).drop data.indexOffset).take data.numIndices = idx := by
      rw [hio, List.append_assoc (ps ++ xs), List.drop_left' (by simp [ps, xs, P]),
        List.take_left' (by simp [idx, hni])]
    have hrecon : data.singletonReconstruction env levels (vars (data.majorOffset + 1) 0) =
        some (mkApps E.ctor (ps ++ fs), fs) := by
      simp only [RecursorData.singletonReconstruction, hS, hE, bind, Option.bind_some,
        hall, htakeP, hidx]
      rfl
    have htake := VExpr.takeForalls_wrapForalls Δ result
    rw [hΔlen, ← hmajor] at htake
    unfold RecursorData.singletonUnfolding
    rw [if_neg (by simp [hlen])]
    simp only [bind, hrt, Option.bind_some, RecursorData.supplyType, htype,
      List.length_nil, Nat.sub_zero, htake, List.map_nil, List.nil_append, hrecon,
      hseq, hgen, hext]
    simp only [hall, htakeI]
    rw [if_neg (by change ¬(caps.length != D.length) = true; simp [hcaplen])]
    rfl
  · exact ⟨_, by simpa only [program, RecursorData.PrefixUnfolding.rhs,
      instantiateParams_eq_instOuter] using he⟩

/-- Every successful generated zero prefix has the registered closed equation. -/
theorem zero_equation (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF U) (hlen : levels.length = data.uvars)
    (hS : data.singletonLayout env levels = some S)
    (hindices : PropTelescope env U (data.propParams levels).reverse S.indices)
    (hg : data.singletonUnfolding env U levels [] = some program) :
    env.IsDefEqU U [] (.const data.name levels) program.rhs := by
  obtain ⟨_, _, _, _, hseq, _⟩ := RecursorData.singletonUnfolding_spec hg
  obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq hseq
  obtain ⟨program', hg', he⟩ := zero_equation_exists henv heq H hlarge hzero hw hlen howner hS hindices
  cases RecursorData.singletonUnfolding_unique hg' hg
  exact he

end Lean4Lean.VEnv.Strengthening.ProofIndexedSingleton
