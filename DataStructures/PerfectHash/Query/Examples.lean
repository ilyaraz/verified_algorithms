import DataStructures.PerfectHash.Query.Correctness

namespace PerfectHash.Query.Examples
open WordRam

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

def hashedSet : Finset (Word 8) := {word 8 0,word 8 1}

def hashedData : Table.Data 8 where
  buckets := 1
  rootSeed := word 8 1
  rootShift := word 8 8
  count _ := 2
  seed _ := word 8 129
  shift _ := word 8 5
  slots _ := 8
  contents _ i := if i = 0 then some (word 8 0) else if i = 4 then some (word 8 1) else none

def hashedRegion : Region := ⟨220,24⟩

/-- Only occupied key cells and required metadata are initialized; unused key
cells and every address outside the dictionary remain dirty. -/
def hashedMemory : DataMemory 8 := fun a => word 8 (match a.toNat with
  | 220 => 1 | 221 => 8 | 222 => 1 | 223 => 2
  | 224 => 2 | 225 => 129 | 226 => 5 | 227 => 228
  | 228 => 1 | 229 => 0 | 236 => 1 | 237 => 1
  | 230 | 232 | 234 | 238 | 240 | 242 => 0
  | _ => 255)

theorem hashed_valid : Table.Valid hashedSet hashedData := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · intro b i hi
    fin_cases b
    change i < 8 at hi
    interval_cases i <;> decide

theorem hashed_view : Table.View hashedSet hashedRegion hashedMemory hashedData := by
  constructor
  · exact hashed_valid
  · decide
  · change 220+24 < modulus 8
    decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro b i hi
    fin_cases b
    change i < 8 at hi
    interval_cases i <;> decide
  · intro b i hi x hx
    fin_cases b
    change i < 8 at hi
    interval_cases i <;> simp [hashedData] at hx <;> subst x <;> decide

def registers (r : Region) (q : Word 8) : Registers 8 64 := fun i =>
  if i.val = 0 then word 8 r.base else if i.val = 1 then word 8 r.size
  else if i.val = 2 then q else word 8 255

def execute (q : Word 8) : RunResult 8 64 :=
  run program (fun _ => word 8 255) cost (.initial (registers hashedRegion q) hashedMemory)

theorem input_valid (r : Region) (q : Word 8) : StaticSet.QueryInput r q (registers r q) := by
  simp [StaticSet.QueryInput,registers]

theorem zero_member : (execute (word 8 0)).state.regs ⟨0,by decide⟩ = word 8 1 := by decide

theorem one_member : (execute (word 8 1)).state.regs ⟨0,by decide⟩ = word 8 1 := by decide

theorem occupied_nonmember : (execute (word 8 2)).state.regs ⟨0,by decide⟩ = word 8 0 ∧
    (execute (word 8 2)).steps = 30 := by decide

theorem dirty_empty_slot : (execute (word 8 255)).state.regs ⟨0,by decide⟩ = word 8 0 ∧
    (execute (word 8 255)).steps = 27 := by decide

theorem read_only : (execute (word 8 2)).writeFootprint = [] ∧
    (execute (word 8 2)).randomReads = 0 := by decide

/-- A one-bucket empty dictionary ends at the last representable word. -/
def emptyMemory : DataMemory 8 := fun a => word 8 (match a.toNat with
  | 247 => 1 | 248 => 8 | 249 => 1 | 250 => 0
  | 251 => 0 | 252 => 0 | 253 => 0 | 254 => 255
  | _ => 255)

theorem empty_boundary :
    let r := run program (fun _ => word 8 255) cost
      (.initial (registers ⟨247,8⟩ (word 8 255)) emptyMemory)
    r.reason = .halted ∧ r.state.regs ⟨0,by decide⟩ = word 8 0 ∧ r.steps = 13 := by decide

/-- Two direct singleton slots store zero and the maximum word. -/
def singletonMemory : DataMemory 8 := fun a => word 8 (match a.toNat with
  | 200 => 1 | 201 => 7 | 202 => 2 | 203 => 2
  | 204 => 1 | 205 => 0 | 206 => 0 | 207 => 212
  | 208 => 1 | 209 => 0 | 210 => 0 | 211 => 214
  | 212 => 1 | 213 => 0 | 214 => 1 | 215 => 255
  | _ => 255)

theorem maximum_singleton :
    let r := run program (fun _ => word 8 0) cost
      (.initial (registers ⟨200,16⟩ (word 8 255)) singletonMemory)
    r.reason = .halted ∧ r.state.regs ⟨0,by decide⟩ = word 8 1 ∧ r.steps = 22 := by decide

theorem overwritten_outside (q : Word 8) :
    StaticSet.QueryOutput hashedSet hashedRegion q
      (fun a => if 220 ≤ a.toNat ∧ a.toNat < 244 then hashedMemory a else word 8 0) cost
      (run program (fun _ => word 8 0) cost (.initial (registers hashedRegion q)
        (fun a => if 220 ≤ a.toNat ∧ a.toNat < 244 then hashedMemory a else word 8 0))) := by
  apply after_overwrite hashed_view
  · intro a ha
    change 220 ≤ a.toNat ∧ a.toNat < 244 at ha
    simp [ha]
  · exact input_valid _ _

end PerfectHash.Query.Examples
