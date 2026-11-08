import Algorithms.Dedup.Correctness
import DataStructures.PerfectHash.Construction.Refinement

namespace PerfectHash.Bounded.Registers
open WordRam

def trialsLeft : Reg 64 := ⟨32,by decide⟩
def randomCursor : Reg 64 := ⟨33,by decide⟩
def stage : Reg 64 := ⟨34,by decide⟩
def compactBase : Reg 64 := ⟨36,by decide⟩
def distinctCount : Reg 64 := ⟨37,by decide⟩
def rootShift : Reg 64 := ⟨38,by decide⟩
def bucketIndex : Reg 64 := ⟨39,by decide⟩
def fallbackMode : Reg 64 := ⟨40,by decide⟩
def directoryCursor : Reg 64 := ⟨41,by decide⟩
def tableCursor : Reg 64 := ⟨42,by decide⟩
def outputBase : Reg 64 := ⟨56,by decide⟩
def occurrenceCount : Reg 64 := ⟨57,by decide⟩
def originalInput : Reg 64 := ⟨58,by decide⟩
def scratchBase : Reg 64 := ⟨59,by decide⟩
def randomBase : Reg 64 := ⟨60,by decide⟩
def machineWidth : Reg 64 := ⟨61,by decide⟩

end PerfectHash.Bounded.Registers

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

inductive Block where
  | dedup | rounding | root | allocation | child
  deriving DecidableEq, Repr

inductive Label where
  | block (name : Block) (pc : Nat)
  | deduplicated | rounded | rootChoose | rootTrial | rootResult | rootAccepted
  | childLoop | allocated | childChoose | directChild | childTrial | childResult
  | finish | failed
  deriving DecidableEq, Repr

/-- Convert local control-flow targets to symbolic block labels. A standalone
halt becomes a charged jump to the caller's named continuation. -/
def inlineInstruction (tag : Block) (continuation : Label) : Instr 64 → Assembly.Instruction 64 Label
  | .branch c x y pc => .branch c x y (.block tag pc)
  | .jump pc => .jump (.block tag pc)
  | .halt => .jump continuation
  | i => .emit i

def inlineAux (tag : Block) (continuation : Label) : Nat → List (Instr 64) → List (Assembly.Item 64 Label)
  | _,[] => []
  | pc,i::rest => .label (.block tag pc)::
      .instruction (inlineInstruction tag continuation i)::inlineAux tag continuation (pc+1) rest

def inlineBlock (tag : Block) (continuation : Label) (p : Program 64) : List (Assembly.Item 64 Label) :=
  inlineAux tag continuation 0 p.toList

/-- One addressed raw sample, transformed to an odd multiplier. Counters and
addresses are updated after the read; a zero budget branches before this block. -/
def sampleCode : List (Assembly.Item 64 Label) := [
  .instruction (.emit (.rload seed (.reg randomCursor))),
  .instruction (.emit (.mod temp (.reg seed) (.imm 2))),
  .instruction (.emit (.sub seed (.reg seed) (.reg temp))),
  .instruction (.emit (.add seed (.reg seed) (.imm 1))),
  .instruction (.emit (.add randomCursor (.reg randomCursor) (.imm 1))),
  .instruction (.emit (.sub trialsLeft (.reg trialsLeft) (.imm 1)))]

/-- A fixed bounded constructor. Every stage has exactly w available random
addresses and halts with status zero if that stage exhausts its budget. -/
def assembly : List (Assembly.Item 64 Label) := [
  .instruction (.emit (.mov outputBase (.reg directory))),
  .instruction (.emit (.mov occurrenceCount (.reg count))),
  .instruction (.emit (.mov originalInput (.reg Construction.Registers.input))),
  .instruction (.emit (.mov scratchBase (.reg width))),
  .instruction (.emit (.mov randomBase (.reg shift))),
  .instruction (.emit (.mov machineWidth (.reg remaining))),
  .instruction (.emit (.mov directory (.reg scratchBase))),
  .instruction (.emit (.mov nodes (.reg randomBase))),
  .instruction (.emit (.mov width (.reg machineWidth)))] ++
  inlineBlock .dedup .deduplicated Dedup.program ++ [
  .label .deduplicated,
  .instruction (.emit (.mov compactBase (.reg Construction.Registers.input))),
  .instruction (.emit (.mov Registers.distinctCount (.reg count))),
  .instruction (.emit (.mov roundTarget (.reg count))),
  .instruction (.emit (.mov size (.imm 1))),
  .instruction (.emit (.mov shift (.reg machineWidth)))] ++
  inlineBlock .rounding .rounded Construction.Round.program ++ [
  .label .rounded,
  .instruction (.emit (.mov buckets (.reg size))),
  .instruction (.emit (.mov rootShift (.reg shift))),
  .instruction (.emit (.add directory (.reg outputBase) (.imm 4))),
  .instruction (.emit (.mov nodes (.reg scratchBase))),
  .instruction (.emit (.mov count (.reg Registers.distinctCount))),
  .instruction (.emit (.mov width (.reg machineWidth))),
  .instruction (.emit (.mov trialsLeft (.reg machineWidth))),
  .instruction (.emit (.add randomCursor (.reg randomBase) (.imm 1))),
  .instruction (.emit (.mov stage (.imm 0))),
  .instruction (.emit (.mov fallbackMode (.imm 0))),
  .label .rootChoose,
  .instruction (.branch .eq (.reg trialsLeft) (.imm 0) .failed)] ++ sampleCode ++ [
  .label .rootTrial,
  .instruction (.emit (.mov Construction.Registers.input (.reg compactBase)))] ++
  inlineBlock .root .rootResult Construction.Root.program ++ [
  .label .rootResult,
  .instruction (.branch .eq (.reg status) (.imm 1) .rootAccepted),
  .instruction (.jump .rootChoose),
  .label .rootAccepted,
  .instruction (.emit (.store (.reg outputBase) (.reg seed))),
  .instruction (.emit (.add temp (.reg outputBase) (.imm 1))),
  .instruction (.emit (.store (.reg temp) (.reg rootShift))),
  .instruction (.emit (.add temp (.reg outputBase) (.imm 2))),
  .instruction (.emit (.store (.reg temp) (.reg buckets))),
  .instruction (.emit (.add temp (.reg outputBase) (.imm 3))),
  .instruction (.emit (.store (.reg temp) (.reg Registers.distinctCount))),
  .instruction (.emit (.mov bucketIndex (.imm 0))),
  .instruction (.emit (.mov directoryCursor (.reg directory))),
  .instruction (.emit (.mul temp (.reg buckets) (.imm 4))),
  .instruction (.emit (.add tableCursor (.reg directory) (.reg temp))),
  .label .childLoop,
  .instruction (.branch .eq (.reg bucketIndex) (.reg buckets) .finish),
  .instruction (.emit (.mov address (.reg directoryCursor))),
  .instruction (.emit (.mov table (.reg tableCursor))),
  .instruction (.emit (.mov width (.reg machineWidth)))] ++
  inlineBlock .allocation .allocated Construction.Allocation.program ++ [
  .label .allocated,
  .instruction (.emit (.mov trialsLeft (.reg machineWidth))),
  .instruction (.emit (.add temp (.reg bucketIndex) (.imm 1))),
  .instruction (.emit (.mul temp (.reg temp) (.reg machineWidth))),
  .instruction (.emit (.add randomCursor (.reg randomBase) (.reg temp))),
  .instruction (.emit (.add randomCursor (.reg randomCursor) (.imm 1))),
  .instruction (.emit (.mov stage (.imm 1))),
  .instruction (.emit (.mov fallbackMode (.imm 0))),
  .instruction (.branch .le (.reg childCount) (.imm 1) .directChild),
  .label .childChoose,
  .instruction (.branch .eq (.reg trialsLeft) (.imm 0) .failed)] ++ sampleCode ++ [
  .instruction (.jump .childTrial),
  .label .directChild,
  .instruction (.emit (.mov seed (.imm 1))),
  .label .childTrial] ++
  inlineBlock .child .childResult Construction.Child.program ++ [
  .label .childResult,
  .instruction (.branch .eq (.reg status) (.imm 0) .childChoose),
  .instruction (.emit (.add temp (.reg directoryCursor) (.imm 1))),
  .instruction (.emit (.store (.reg temp) (.reg seed))),
  .instruction (.emit (.mov tableCursor (.reg tableEnd))),
  .instruction (.emit (.add directoryCursor (.reg directoryCursor) (.imm 4))),
  .instruction (.emit (.add bucketIndex (.reg bucketIndex) (.imm 1))),
  .instruction (.jump .childLoop),
  .label .finish,
  .instruction (.emit (.mov Construction.Registers.input (.reg outputBase))),
  .instruction (.emit (.sub count (.reg tableCursor) (.reg outputBase))),
  .instruction (.emit (.mov directory (.reg Registers.distinctCount))),
  .instruction (.emit (.mov status (.imm 1))),
  .instruction (.emit .halt),
  .label .failed,
  .instruction (.emit (.mov status (.imm 0))),
  .instruction (.emit .halt)]

def location (l : Label) : Nat := (Assembly.labelOffset l assembly).getD 0

def program : Program 64 := Assembly.assemble 0 location (Assembly.instructions assembly).toArray

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

theorem compile_eq : Assembly.compile 0 assembly = some program := by decide

theorem dedup_embedded : BodyEmbedded Dedup.program program (location (.block .dedup 0)) := by
  apply BodyEmbedded.of_check
  decide

theorem rounding_embedded : BodyEmbedded Construction.Round.program program (location (.block .rounding 0)) := by
  apply BodyEmbedded.of_check
  decide

theorem root_embedded : BodyEmbedded Construction.Root.program program (location (.block .root 0)) := by
  apply BodyEmbedded.of_check
  decide

theorem allocation_embedded : BodyEmbedded Construction.Allocation.program program (location (.block .allocation 0)) := by
  apply BodyEmbedded.of_check
  decide

theorem child_embedded : BodyEmbedded Construction.Child.program program (location (.block .child 0)) := by
  apply BodyEmbedded.of_check
  decide

theorem program_size : program.size = 231 := by decide

theorem dedup_returns : HaltsTo Dedup.program program (location (.block .dedup 0)) (location .deduplicated) := by
  apply HaltsTo.of_check
  decide

theorem rounding_returns : HaltsTo Construction.Round.program program
    (location (.block .rounding 0)) (location .rounded) := by
  apply HaltsTo.of_check
  decide

theorem root_returns : HaltsTo Construction.Root.program program
    (location (.block .root 0)) (location .rootResult) := by
  apply HaltsTo.of_check
  decide

theorem allocation_returns : HaltsTo Construction.Allocation.program program
    (location (.block .allocation 0)) (location .allocated) := by
  apply HaltsTo.of_check
  decide

theorem child_returns : HaltsTo Construction.Child.program program
    (location (.block .child 0)) (location .childResult) := by
  apply HaltsTo.of_check
  decide

end PerfectHash.Bounded
