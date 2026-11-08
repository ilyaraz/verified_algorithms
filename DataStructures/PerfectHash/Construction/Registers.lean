import WordRam.Refinement

namespace PerfectHash.Construction.Registers
open WordRam

def input : Reg 64 := ⟨0,by decide⟩
def count : Reg 64 := ⟨1,by decide⟩
def directory : Reg 64 := ⟨2,by decide⟩
def nodes : Reg 64 := ⟨3,by decide⟩
def width : Reg 64 := ⟨4,by decide⟩
def seed : Reg 64 := ⟨5,by decide⟩
def shift : Reg 64 := ⟨6,by decide⟩
def budget : Reg 64 := ⟨7,by decide⟩
def remaining : Reg 64 := ⟨8,by decide⟩
def distinct : Reg 64 := ⟨9,by decide⟩
def key : Reg 64 := ⟨10,by decide⟩
def hash : Reg 64 := ⟨11,by decide⟩
def address : Reg 64 := ⟨12,by decide⟩
def oldCount : Reg 64 := ⟨13,by decide⟩
def oldHead : Reg 64 := ⟨14,by decide⟩
def increment : Reg 64 := ⟨15,by decide⟩
def node : Reg 64 := ⟨16,by decide⟩
def temp : Reg 64 := ⟨17,by decide⟩
def status : Reg 64 := ⟨18,by decide⟩
def clearCursor : Reg 64 := ⟨19,by decide⟩
def clearRemaining : Reg 64 := ⟨20,by decide⟩
def table : Reg 64 := ⟨21,by decide⟩
def buckets : Reg 64 := ⟨22,by decide⟩
def slots : Reg 64 := ⟨23,by decide⟩
def cursor : Reg 64 := ⟨24,by decide⟩
def slot : Reg 64 := ⟨25,by decide⟩
def flag : Reg 64 := ⟨26,by decide⟩
def rootHead : Reg 64 := ⟨27,by decide⟩
def childCount : Reg 64 := ⟨28,by decide⟩
def tableEnd : Reg 64 := ⟨29,by decide⟩
def roundTarget : Reg 64 := ⟨30,by decide⟩
def size : Reg 64 := ⟨31,by decide⟩

end PerfectHash.Construction.Registers
