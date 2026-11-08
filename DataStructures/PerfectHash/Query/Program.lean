import WordRam.Assembly

namespace PerfectHash.Query.Registers
open WordRam
def result : Reg 64 := ⟨0,by decide⟩
def key : Reg 64 := ⟨2,by decide⟩
def base : Reg 64 := ⟨3,by decide⟩
def seed : Reg 64 := ⟨4,by decide⟩
def temp : Reg 64 := ⟨5,by decide⟩
def shift : Reg 64 := ⟨6,by decide⟩
def index : Reg 64 := ⟨7,by decide⟩
def directory : Reg 64 := ⟨8,by decide⟩
def count : Reg 64 := ⟨9,by decide⟩
def table : Reg 64 := ⟨10,by decide⟩
def slot : Reg 64 := ⟨11,by decide⟩
def flag : Reg 64 := ⟨12,by decide⟩
def stored : Reg 64 := ⟨13,by decide⟩
end PerfectHash.Query.Registers

namespace PerfectHash.Query
open WordRam Registers

inductive Label where
  | singleton | slot | no | yes
  deriving DecidableEq, Repr

/-- A fixed read-only membership query with explicit occupancy and full-key
comparison. Singleton children use their direct slot without a child hash. -/
def assembly : List (Assembly.Item 64 Label) := [
  .instruction (.emit (.mov base (.reg result))),
  .instruction (.emit (.load seed (.reg base))),
  .instruction (.emit (.add temp (.reg base) (.imm 1))),
  .instruction (.emit (.load shift (.reg temp))),
  .instruction (.emit (.mul index (.reg seed) (.reg key))),
  .instruction (.emit (.shr index (.reg index) (.reg shift))),
  .instruction (.emit (.mul directory (.reg index) (.imm 4))),
  .instruction (.emit (.add directory (.reg directory) (.reg base))),
  .instruction (.emit (.add directory (.reg directory) (.imm 4))),
  .instruction (.emit (.load count (.reg directory))),
  .instruction (.branch .eq (.reg count) (.imm 0) .no),
  .instruction (.emit (.add temp (.reg directory) (.imm 3))),
  .instruction (.emit (.load table (.reg temp))),
  .instruction (.branch .eq (.reg count) (.imm 1) .singleton),
  .instruction (.emit (.add temp (.reg directory) (.imm 1))),
  .instruction (.emit (.load seed (.reg temp))),
  .instruction (.emit (.add temp (.reg directory) (.imm 2))),
  .instruction (.emit (.load shift (.reg temp))),
  .instruction (.emit (.mul index (.reg seed) (.reg key))),
  .instruction (.emit (.shr index (.reg index) (.reg shift))),
  .instruction (.emit (.mul slot (.reg index) (.imm 2))),
  .instruction (.emit (.add slot (.reg table) (.reg slot))),
  .instruction (.jump .slot),
  .label .singleton,
  .instruction (.emit (.mov slot (.reg table))),
  .label .slot,
  .instruction (.emit (.load flag (.reg slot))),
  .instruction (.branch .eq (.reg flag) (.imm 0) .no),
  .instruction (.emit (.add slot (.reg slot) (.imm 1))),
  .instruction (.emit (.load stored (.reg slot))),
  .instruction (.branch .eq (.reg stored) (.reg key) .yes),
  .label .no,
  .instruction (.emit (.mov result (.imm 0))),
  .instruction (.emit .halt),
  .label .yes,
  .instruction (.emit (.mov result (.imm 1))),
  .instruction (.emit .halt)]

def location (l : Label) : Nat := (Assembly.labelOffset l assembly).getD 0

def program : Program 64 := Assembly.assemble 0 location (Assembly.instructions assembly).toArray

def cost : Nat := 33

theorem compile_eq : Assembly.compile 0 assembly = some program := by decide

theorem program_size : program.size = 33 := by decide

end PerfectHash.Query
