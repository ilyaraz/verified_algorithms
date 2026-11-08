import DataStructures.PerfectHash.Query.Program
import DataStructures.PerfectHash.Representation

namespace PerfectHash.Query
open WordRam

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- Read-only permission for the retained representation. -/
def policy (r : Region) : AccessPolicy w := ⟨r.Contains,fun _ => False,fun _ => False⟩

macro "query_reduce" : tactic => `(tactic|
  (simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm] at *
   simp [program,assembly,location,Assembly.assemble,Assembly.instructions,Assembly.labelOffset,
    Assembly.Instruction.resolve,Instr.relocate,run,step,Comparison.test,Operand.eval,
    State.initial,State.put,update,update_shadow,RunResult.prepend,cost,
    Registers.result,Registers.key,Registers.base,Registers.seed,Registers.temp,
    Registers.shift,Registers.index,Registers.directory,Registers.count,Registers.table,
    Registers.slot,Registers.flag,Registers.stored,word_add,word_mul,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm,
    AccessPolicy.AllowsTrace,AccessPolicy.Allows,policy, *]))

variable {w : Nat} {S : Finset (Word w)} {r : Region} {mem mem' : DataMemory w} {d : Table.Data w}

/-- Evaluate every forward branch of the fixed query against the local table
view. No original input, construction workspace, or seed-search history appears. -/
theorem execution (v : Table.View S r mem d) (q : Word w) (rs : Registers w 64)
    (hinput : StaticSet.QueryInput r q rs) (rho : RandomMemory w) :
    let result := run program rho cost (.initial rs mem)
    result.reason = .halted ∧ result.state.regs ⟨0,by decide⟩ = word w (if q ∈ S then 1 else 0) ∧
      result.state.mem = mem ∧ (policy r).AllowsTrace result.trace := by
  obtain ⟨hbase,_,hkey⟩ := hinput
  change rs (0 : Reg 64) = word w r.base at hbase
  change rs (2 : Reg 64) = q at hkey
  let b : Fin d.buckets := ⟨d.rootIndex q,v.valid.rootRange q⟩
  have hroot : unsignedShiftRight (d.rootSeed*q) d.rootShift = word w b.val := by
    change _ = word w (unsignedShiftRight (d.rootSeed*q) d.rootShift).toNat
    simp only [word,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have hseed := v.headerSeed
  have hshift := v.headerShift
  have hcount := v.directoryCount b
  have htable := v.directoryTable b
  have hcseed := v.directorySeed b
  have hcshift := v.directoryShift b
  simp only [Packed.directory] at hcount htable hcseed hcshift
  have hcount0 : word w (d.count b) = word w 0 ↔ d.count b = 0 :=
    word_eq_iff_of_lt (v.count_fit b) (by have := v.four_lt; omega)
  have hcount1 : word w (d.count b) = word w 1 ↔ d.count b = 1 :=
    word_eq_iff_of_lt (v.count_fit b) (by have := v.four_lt; omega)
  have hone : word w 1 ≠ word w 0 := by
    intro he
    have hh := congrArg BitVec.toNat he
    rw [word_toNat_of_lt (by have := v.four_lt; omega : 1 < modulus w),
      word_toNat_of_lt (by have := v.four_lt; omega : 0 < modulus w)] at hh
    omega
  have local0 := v.contains_header (i := 0) (by decide)
  have local1 := v.contains_header (i := 1) (by decide)
  have localDir0 := v.contains_directory b (i := 0) (by decide)
  have localDir1 := v.contains_directory b (i := 1) (by decide)
  have localDir2 := v.contains_directory b (i := 2) (by decide)
  have localDir3 := v.contains_directory b (i := 3) (by decide)
  simp only [Nat.add_zero,Packed.directory] at local0 localDir0 localDir1 localDir2 localDir3
  by_cases hc : d.count b = 0
  · have hnot : q ∉ S := v.valid.empty_bucket b hc rfl
    query_reduce
  · have hpos : 0 < d.count b := Nat.pos_of_ne_zero hc
    let i := d.slotIndex b q
    have hi : i < d.slots b := v.valid.slotRange b hpos q
    have hflag := v.occupancy b i hi
    have localFlag := v.contains_table b hi (j := 0) (by decide)
    have localKey := v.contains_table b hi (j := 1) (by decide)
    simp only [Nat.add_zero] at localFlag
    have hmember := v.valid.selected_slot b hpos (x := q) rfl
    change d.contents b i = some q ↔ q ∈ S at hmember
    cases hcontent : d.contents b i with
    | none =>
      have hnot : q ∉ S := by rw [← hmember,hcontent]; simp
      simp only [hcontent,Option.isSome_none,Bool.false_eq_true,↓reduceIte] at hflag
      by_cases hs : d.count b = 1
      · have hi0 : i = 0 := by simp [i,Table.Data.slotIndex,hs]
        simp only [hi0,Nat.mul_zero,Nat.add_zero] at hflag localFlag localKey
        query_reduce
      · have hhash : unsignedShiftRight (d.seed b*q) (d.shift b) = word w i := by
          change _ = word w (d.slotIndex b q)
          simp only [Table.Data.slotIndex,hs,↓reduceIte,word,BitVec.ofNat_toNat,BitVec.setWidth_eq]
        query_reduce
    | some k =>
      have hstored := v.keys b i hi k hcontent
      simp only [hcontent,Option.isSome_some,↓reduceIte] at hflag
      have hm : q ∈ S ↔ k = q := by simpa only [hcontent,Option.some.injEq] using hmember.symm
      by_cases hs : d.count b = 1
      · have hi0 : i = 0 := by simp [i,Table.Data.slotIndex,hs]
        simp only [hi0,Nat.mul_zero,Nat.add_zero] at hflag hstored localFlag localKey
        by_cases hk : k = q <;> query_reduce
      · have hhash : unsignedShiftRight (d.seed b*q) (d.shift b) = word w i := by
          change _ = word w (d.slotIndex b q)
          simp only [Table.Data.slotIndex,hs,↓reduceIte,word,BitVec.ofNat_toNat,BitVec.setWidth_eq]
        by_cases hk : k = q <;> query_reduce

theorem policy_no_writes {log : List (Access w)} (hp : (policy r).AllowsTrace log) :
    log.filterMap Access.writeAddress = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro e he
  have hh := hp e he
  cases e <;> simp_all [Access.writeAddress,AccessPolicy.Allows,policy]

theorem policy_no_random {log : List (Access w)} (hp : (policy r).AllowsTrace log) :
    log.filterMap Access.randomAddress = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro e he
  have hh := hp e he
  cases e <;> simp_all [Access.randomAddress,AccessPolicy.Allows,policy]

/-- The actual bounded execution meets every frozen public query obligation. -/
theorem correct (v : Table.View S r mem d) (q : Word w) (rs : Registers w 64)
    (hinput : StaticSet.QueryInput r q rs) (rho : RandomMemory w) :
    StaticSet.QueryOutput S r q mem cost (run program rho cost (.initial rs mem)) := by
  obtain ⟨hhalt,hanswer,hmem,htrace⟩ := execution v q rs hinput rho
  refine ⟨hhalt,run_steps_le _ _ _ _,hanswer,hmem,?_,?_,?_⟩
  · simp only [RunResult.writeFootprint,policy_no_writes htrace,List.eraseDups_nil]
  · simp only [RunResult.randomReads,RunResult.randomAddresses,policy_no_random htrace,List.length_nil]
  · intro a ha
    have hm : a ∈ (run program rho cost (.initial rs mem)).trace.filterMap Access.dataAddress :=
      eraseDups_subset _ ha
    obtain ⟨e,he,heq⟩ := List.mem_filterMap.mp hm
    have hh := htrace e he
    cases e <;> simp_all [Access.dataAddress,AccessPolicy.Allows,policy]

/-- Query correctness is independent of which preprocessing program will later
establish the representation. -/
theorem spec (preprocess : Program StaticSet.registerCount) :
    StaticSet.QuerySpec ⟨preprocess,program⟩ Table.representation cost := by
  intro w _ S r mem hrep q rs hinput rho
  obtain ⟨d,hd⟩ := hrep
  exact correct hd q rs hinput rho

/-- Successful queries preserve the same reusable representation. -/
theorem representation_preserved (v : Table.View S r mem d) (q : Word w) (rs : Registers w 64)
    (hinput : StaticSet.QueryInput r q rs) (rho : RandomMemory w) :
    Table.View S r (run program rho cost (.initial rs mem)).state.mem d := by
  rw [(correct v q rs hinput rho).memory]
  exact v

/-- Erasing original input, scratch, and every other unretained address leaves
all query answers and the read-only contract unchanged. -/
theorem after_overwrite (v : Table.View S r mem d) (ha : AgreeOn r mem mem')
    (q : Word w) (rs : Registers w 64) (hinput : StaticSet.QueryInput r q rs) (rho : RandomMemory w) :
    StaticSet.QueryOutput S r q mem' cost (run program rho cost (.initial rs mem')) :=
  correct (v.frame ha) q rs hinput rho

end PerfectHash.Query
