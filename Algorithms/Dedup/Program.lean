import WordRam.Assembly

namespace Dedup.Registers
def input : WordRam.Reg 64 := ⟨0, by decide⟩
def count : WordRam.Reg 64 := ⟨1, by decide⟩
def scratch : WordRam.Reg 64 := ⟨2, by decide⟩
def random : WordRam.Reg 64 := ⟨3, by decide⟩
def width : WordRam.Reg 64 := ⟨4, by decide⟩
def unused : WordRam.Reg 64 := ⟨5, by decide⟩
def remaining : WordRam.Reg 64 := ⟨6, by decide⟩
def distinct : WordRam.Reg 64 := ⟨7, by decide⟩
def size : WordRam.Reg 64 := ⟨8, by decide⟩
def shift : WordRam.Reg 64 := ⟨9, by decide⟩
def heads : WordRam.Reg 64 := ⟨10, by decide⟩
def nodes : WordRam.Reg 64 := ⟨11, by decide⟩
def compact : WordRam.Reg 64 := ⟨12, by decide⟩
def clearCursor : WordRam.Reg 64 := ⟨13, by decide⟩
def clearRemaining : WordRam.Reg 64 := ⟨14, by decide⟩
def seed : WordRam.Reg 64 := ⟨15, by decide⟩
def temp : WordRam.Reg 64 := ⟨16, by decide⟩
def key : WordRam.Reg 64 := ⟨17, by decide⟩
def hash : WordRam.Reg 64 := ⟨18, by decide⟩
def headAddress : WordRam.Reg 64 := ⟨19, by decide⟩
def oldHead : WordRam.Reg 64 := ⟨20, by decide⟩
def cursor : WordRam.Reg 64 := ⟨21, by decide⟩
def pointer : WordRam.Reg 64 := ⟨22, by decide⟩
def loaded : WordRam.Reg 64 := ⟨23, by decide⟩
def compactPointer : WordRam.Reg 64 := ⟨24, by decide⟩
def newNode : WordRam.Reg 64 := ⟨25, by decide⟩
end Dedup.Registers

namespace Dedup
open WordRam Registers

inductive Label where
  | entry | round | rounded | clear | cleared | inputLoop | scan | found | missing | done
  deriving DecidableEq, Repr

/-- One fixed program: round and clear the directory, sample one odd seed, and
search/insert chained nodes while preserving the occurrence array. Node pointers
are one-based indices; zero keys and maximum-word keys are ordinary data. -/
def assembly : List (Assembly.Item 64 Label) := [
  .label .entry,
  .instruction (.emit (.mov heads (.reg scratch))),
  .instruction (.emit (.mov remaining (.reg count))),
  .instruction (.emit (.mov distinct (.imm 0))),
  .instruction (.emit (.mov size (.imm 1))),
  .instruction (.emit (.mov shift (.reg width))),
  .label .round,
  .instruction (.branch .le (.reg count) (.reg size) .rounded),
  .instruction (.emit (.add size (.reg size) (.reg size))),
  .instruction (.emit (.sub shift (.reg shift) (.imm 1))),
  .instruction (.jump .round),
  .label .rounded,
  .instruction (.emit (.add temp (.reg count) (.imm 1))),
  .instruction (.emit (.mul temp (.reg temp) (.imm 2))),
  .instruction (.emit (.add nodes (.reg heads) (.reg temp))),
  .instruction (.emit (.mul temp (.reg count) (.imm 2))),
  .instruction (.emit (.add compact (.reg nodes) (.reg temp))),
  .instruction (.emit (.mov clearCursor (.reg heads))),
  .instruction (.emit (.mov clearRemaining (.reg size))),
  .label .clear,
  .instruction (.branch .eq (.reg clearRemaining) (.imm 0) .cleared),
  .instruction (.emit (.store (.reg clearCursor) (.imm 0))),
  .instruction (.emit (.add clearCursor (.reg clearCursor) (.imm 1))),
  .instruction (.emit (.sub clearRemaining (.reg clearRemaining) (.imm 1))),
  .instruction (.jump .clear),
  .label .cleared,
  .instruction (.emit (.rload seed (.reg random))),
  .instruction (.emit (.mod temp (.reg seed) (.imm 2))),
  .instruction (.emit (.sub seed (.reg seed) (.reg temp))),
  .instruction (.emit (.add seed (.reg seed) (.imm 1))),
  .label .inputLoop,
  .instruction (.branch .eq (.reg remaining) (.imm 0) .done),
  .instruction (.emit (.load key (.reg input))),
  .instruction (.emit (.mul hash (.reg seed) (.reg key))),
  .instruction (.emit (.shr hash (.reg hash) (.reg shift))),
  .instruction (.emit (.add headAddress (.reg heads) (.reg hash))),
  .instruction (.emit (.load oldHead (.reg headAddress))),
  .instruction (.emit (.mov cursor (.reg oldHead))),
  .label .scan,
  .instruction (.branch .eq (.reg cursor) (.imm 0) .missing),
  .instruction (.emit (.sub pointer (.reg cursor) (.imm 1))),
  .instruction (.emit (.mul pointer (.reg pointer) (.imm 2))),
  .instruction (.emit (.add pointer (.reg nodes) (.reg pointer))),
  .instruction (.emit (.load loaded (.reg pointer))),
  .instruction (.branch .eq (.reg key) (.reg loaded) .found),
  .instruction (.emit (.add pointer (.reg pointer) (.imm 1))),
  .instruction (.emit (.load cursor (.reg pointer))),
  .instruction (.jump .scan),
  .label .found,
  .instruction (.emit (.add input (.reg input) (.imm 1))),
  .instruction (.emit (.sub remaining (.reg remaining) (.imm 1))),
  .instruction (.jump .inputLoop),
  .label .missing,
  .instruction (.emit (.mul newNode (.reg distinct) (.imm 2))),
  .instruction (.emit (.add newNode (.reg newNode) (.reg nodes))),
  .instruction (.emit (.store (.reg newNode) (.reg key))),
  .instruction (.emit (.add newNode (.reg newNode) (.imm 1))),
  .instruction (.emit (.store (.reg newNode) (.reg oldHead))),
  .instruction (.emit (.add compactPointer (.reg compact) (.reg distinct))),
  .instruction (.emit (.store (.reg compactPointer) (.reg key))),
  .instruction (.emit (.add distinct (.reg distinct) (.imm 1))),
  .instruction (.emit (.store (.reg headAddress) (.reg distinct))),
  .instruction (.jump .found),
  .label .done,
  .instruction (.emit (.mov input (.reg compact))),
  .instruction (.emit (.mov count (.reg distinct))),
  .instruction (.emit .halt)]

def location (label : Label) : Nat := (Assembly.labelOffset label assembly).getD 0

def program : Program 64 := Assembly.assemble 0 location (Assembly.instructions assembly).toArray

theorem compile_eq : Assembly.compile 0 assembly = some program := by decide

theorem program_size : program.size = 57 := by decide

end Dedup
