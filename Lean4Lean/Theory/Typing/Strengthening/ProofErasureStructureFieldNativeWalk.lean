import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureNativeWalk
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureMaskedConstructorRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureProjectionTypeResidual

/-! # Recoverable constructor fields supplied by a structure major

A structure expansion already supplies a typed constructor telescope. Its
source's native family certificate recovers every retained field at the literal
field domain. For structures without parameters this supplies the entire walk;
no independent field-native coverage hypothesis is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A typed walk becomes recoverable when the native premise holds at each
literal prefix. Domains selected by arbitrary semantic conversion are not part
of this criterion. -/
theorem RetainedNativeWalk.of_prefixes
    (HW : InstForallsC env univs Γ T args result)
    (HN : ∀ {pre a suffix A B}, args = pre ++ a :: suffix →
      InstForallsC env univs Γ T pre (.forallE A B) →
      ¬ IsProof Γ a → ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ A)) :
    RetainedNativeWalk Step Γ T args result := by
  induction HW with
  | nil => exact .nil
  | @cons a A args result B ha HW ih =>
    refine .cons ha (HN (pre := []) rfl .nil) (ih ?_)
    intro pre x suffix X Y E HP
    exact HN (pre := a :: pre) (suffix := suffix) (by simp only [List.cons_append, E]) (.cons ha HP)

/-- In a closed syntactic telescope, the prefix criterion is the usual
instantiated domain at each argument position. -/
theorem RetainedNativeWalk.of_domains
    (HW : InstForallsC env univs Γ (VExpr.wrapForalls doms body) args result)
    (hlen : args.length = doms.length)
    (HN : ∀ j (hj : j < args.length) (hd : j < doms.length),
      ¬ IsProof Γ args[j] → ScopedTypeRecovery Step (proofEraseCtx Γ)
        (proofErase Γ args[j]) (proofErase Γ (doms[j].instOuter (args.take j)))) :
    RetainedNativeWalk Step Γ (VExpr.wrapForalls doms body) args result := by
  apply RetainedNativeWalk.of_prefixes HW
  intro pre a suffix A B E HP hn
  have hj : pre.length < args.length := by simp only [E, List.length_append, List.length_cons]; omega
  have hd : pre.length < doms.length := by omega
  have Ea : args[pre.length] = a := by simp [E]
  have Ep : args.take pre.length = pre := by simp [E]
  rw [VExpr.wrapForalls_split doms body pre.length hd] at HP
  have ER := HP.wrapForalls_eq (by simp; omega)
  obtain ⟨B', EB'⟩ := VExpr.instOuter_forallE doms[pre.length] _ pre
  rw [EB'] at ER
  have EA := VExpr.forallE.inj ER
  have RN := HN pre.length hj hd (by simpa only [Ea] using hn)
  simpa only [Ea, Ep, ← EA.1] using RN

/-- A parameter-free structure expansion has a completely recoverable literal
constructor walk. A single native certificate for its original major supplies
all retained fields, including dependent later fields; proof fields need none.
The relation used by the certificate is arbitrary. -/
theorem structure_fields_retained_native_walk
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : info.nparams = 0) (hx : info.nindices = 0)
    (HT : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hc : env.HasType univs Γ (structExpand s info ls [] m) U)
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ m) (.const s ls)) :
    RetainedNativeWalk Step Γ (info.ctorType.instL ls) (projsOf s m info.numFields) (.const s ls) := by
  have HW := structure_constructor_native_walk hΓ hi hx
    (args := projsOf s m info.numFields) (by simp [projsOf, hp]) hc
  simp only [hp, List.take_zero, VExpr.mkApps] at HW
  rw [HT.shape] at HW ⊢
  apply RetainedNativeWalk.of_domains HW (by simp [projsOf, hd, hp])
  intro j hj hjd hn
  have hj' : info.nparams + j < doms.length := by simpa only [hp, Nat.zero_add] using hjd
  have hjf : j < info.numFields := by simpa [projsOf] using hj
  have HA := structure_expansion_prefix_telescope hΓ hi (ps := []) (by simp [hp]) HT hd hw hl hc
    (Nat.le_of_lt hjf)
  obtain ⟨u, hF⟩ := HT.doms _ hj'
  have EF := proofErase_projection_template hΓ (HT.ctx _ (Nat.le_of_lt hj')) hF HA
  have Ep : (projsOf s m info.numFields).take j = projsOf s m j := by
    simp only [projsOf, ← List.map_take, List.take_range, Nat.min_eq_left (Nat.le_of_lt hjf)]
  have Ej : (projsOf s m info.numFields)[j] = .proj s j m := by simp [projsOf]
  have NP : ¬ IsProof Γ (.proj s j m) := by simpa only [Ej] using hn
  have RP := ScopedTypeRecovery.proj hi HT hj'
    (args := []) (by simp [hp, hx]) (show ScopedTypeRecovery Step (proofEraseCtx Γ)
      (proofErase Γ m) (ProofShape.mkApps (.const s ls) []) from RN)
  rw [Ej, Ep, show proofErase Γ (.proj s j m) = .proj s j (proofErase Γ m) from if_neg NP]
  simp only [hp, Nat.zero_add, List.nil_append, List.map_nil] at EF
  rw [EF]
  simpa only [projectionType, hp, Nat.zero_add, List.map_nil, List.take_nil] using RP

end Lean4Lean.VEnv.Strengthening
