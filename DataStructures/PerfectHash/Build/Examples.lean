import DataStructures.PerfectHash.Build.Instance
import DataStructures.PerfectHash.Build.State
import DataStructures.PerfectHash.Build.Placement

namespace PerfectHash.Build.Examples
open WordRam Hashing.MultiplyShift FiniteProbability
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

/-- Distinct small keys force seed one to fail the root energy threshold. -/
def keys : List (Word 10) := [word 10 0,word 10 1,word 10 2,word 10 3,
  word 10 4,word 10 5,word 10 6,word 10 7]

def model := multiplyShiftModel 9 keys

def badSeed : Seed 9 := ⟨0,by decide⟩

def result := model.construct (fun _ => badSeed) (fun _ _ => badSeed)

theorem input_fits : 64*(keys.length+1) < modulus 10 := by decide

theorem input_distinct : keys.Nodup := by decide

theorem root_rejects : rootAccept model.root keys badSeed = false := by decide

theorem forced_root_fallback : model.rootSearch (fun _ => badSeed) = some ⟨11,by decide⟩ := by decide

theorem zero_budget_fallback :
    FiniteSearch.search (rootAccept model.root keys) model.enumeration 0 Fin.elim0 = some ⟨11,by decide⟩ := by decide

theorem forced_child_fallback :
    model.childSearch ⟨11,by decide⟩ ⟨0,by decide⟩ (fun _ => badSeed) = some (.hashed ⟨4,by decide⟩) := by decide

theorem constructor_completes : result.isSome = true := by decide

/-- Check full-key lookup on the conceptual table, including a nonmember that
can hash into an occupied position. RAM lookup is proved separately in M6. -/
def answers : Bool := match result with
  | none => false
  | some dict => keys.all (fun x => model.stored dict (model.position dict x) == some x) &&
      !(model.stored dict (model.position dict (word 10 8)) == some (word 10 8))

theorem membership_answers : answers = true := by decide

theorem model_hypotheses : Hypotheses model := multiplyShift_hypotheses keys input_distinct input_fits

theorem concrete_expected_work : mean (fun samples => (model.work samples : ℝ)) ≤ 810 := by
  have h := expected_work model model_hypotheses
  norm_num [keys] at h
  exact h

theorem empty_completes :
    ((multiplyShiftModel 7 []).construct (fun _ => ⟨0,by decide⟩) (fun _ _ => ⟨0,by decide⟩)).isSome = true := by decide

theorem endpoints_complete :
    ((multiplyShiftModel 9 [word 10 0,word 10 1023]).construct
      (fun _ => ⟨0,by decide⟩) (fun _ _ => ⟨0,by decide⟩)).isSome = true := by decide

end PerfectHash.Build.Examples
