import Lean4Lean.Verify.Inductive.Constructor.Checked
import Lean4Lean.Verify.Inductive.Constructor.Declare

/-! # Checking invariants across constructor installation

Generic facts for the constructor environment: the checking invariant depends only on the
constant map (`CheckingEnv.of_constants_eq`), and extends along a lockstep fold of fresh,
translated, non-delta constants (`CheckingEnv.insertConsts`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

theorem CheckingEnv.of_constants_eq {safety : DefinitionSafety} {env env' : Environment}
    {venv : VEnv} (H : CheckingEnv safety env venv) (heq : env'.constants = env.constants) :
    CheckingEnv safety env' venv where
  aligned := heq ▸ H.aligned
  wf := H.wf
  of_value := fun hfind => H.of_value (by
    rw [Kernel.Environment.find?, heq] at hfind; exact hfind)

theorem find?_of_constants_eq {env env' : Environment} (heq : env'.constants = env.constants)
    (n : Name) : env'.find? n = env.find? n := by
  simp only [Kernel.Environment.find?, heq]

theorem constants_foldl_add : ∀ (cis : List ConstantInfo) (env : Environment),
    (cis.foldl (fun e ci => Lean.Kernel.Environment.add e ci) env).constants =
      insertConsts env.constants cis
  | [], _ => rfl
  | ci :: cis, env => constants_foldl_add cis (env.add ci)

/-- A lockstep fold of fresh, translated, well-formed, non-delta constants extends a checking
environment, with the constant map extended by `insertConsts`. -/
theorem CheckingEnv.insertConsts {safety : DefinitionSafety} :
    ∀ {env : Environment} {venv venv' : VEnv} {cis : List ConstantInfo} {vs : List VConstVal},
    CheckingEnv safety env venv →
    List.Forall₂ (fun ci v => TrConstVal safety venv ci v ∧ v.toVConstant.WF venv ∧
      ci.deltaValue? = none) cis vs →
    (∀ ci ∈ cis, env.find? ci.name = none) → (cis.map (·.name)).Nodup →
    venv.addConstVals vs = some venv' →
    CheckingEnv safety (cis.foldl (fun e ci => Lean.Kernel.Environment.add e ci) env) venv'
  | _, _, _, [], [], H, .nil, _, _, hadd => by cases hadd; exact H
  | env, venv, venv', ci :: cis, v :: vs, H, .cons ⟨⟨htr, hname⟩, hwf, hdelta⟩ hrest,
      hfr, hnd, hadd => by
    simp only [VEnv.addConstVals] at hadd
    cases hmid : venv.addConst v.name v.toVConstant with
    | none => simp [hmid] at hadd
    | some mid =>
    simp only [hmid, Option.bind_eq_bind, Option.bind_some] at hadd
    have hle := VEnv.addConst_le hmid
    have hfresh : env.find? ci.name = none := hfr ci List.mem_cons_self
    have hmid' : venv.addConst ci.name v.toVConstant = some mid := by rw [hname]; exact hmid
    have H' := H.add hfresh htr hwf hmid' hdelta
    rw [List.map_cons, List.nodup_cons] at hnd
    refine CheckingEnv.insertConsts (env := env.add ci) (cis := cis) (vs := vs) H' ?_ ?_ hnd.2 hadd
    · exact List.Forall₂.imp (fun _ _ ⟨⟨htr, hn⟩, hw, hd⟩ => ⟨⟨htr.mono hle, hn⟩, hw.mono hle, hd⟩) hrest
    · intro d hd
      exact Environment.find?_add_of_ne H.map_wf ci hfresh
        (fun he => hnd.1 (List.mem_map.mpr ⟨d, hd, he.symm⟩)) (hfr d (List.mem_cons_of_mem _ hd))

end VerifyInductive
end Lean4Lean
