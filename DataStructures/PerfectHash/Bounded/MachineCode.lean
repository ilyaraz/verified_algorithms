import DataStructures.PerfectHash.Bounded.Program

namespace PerfectHash.Bounded

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

/-- Kernel-checked decoding of the symbolic source, used to reduce individual
machine blocks without repeatedly expanding the assembler and its inlined code. -/
theorem program_eq : program = #[WordRam.Instr.mov 56 (WordRam.Operand.reg 2), WordRam.Instr.mov 57 (WordRam.Operand.reg 1),
  WordRam.Instr.mov 58 (WordRam.Operand.reg 0), WordRam.Instr.mov 59 (WordRam.Operand.reg 4),
  WordRam.Instr.mov 60 (WordRam.Operand.reg 6), WordRam.Instr.mov 61 (WordRam.Operand.reg 8),
  WordRam.Instr.mov 2 (WordRam.Operand.reg 59), WordRam.Instr.mov 3 (WordRam.Operand.reg 60),
  WordRam.Instr.mov 4 (WordRam.Operand.reg 61), WordRam.Instr.mov 10 (WordRam.Operand.reg 2),
  WordRam.Instr.mov 6 (WordRam.Operand.reg 1), WordRam.Instr.mov 7 (WordRam.Operand.imm 0),
  WordRam.Instr.mov 8 (WordRam.Operand.imm 1), WordRam.Instr.mov 9 (WordRam.Operand.reg 4),
  WordRam.Instr.branch (WordRam.Comparison.le) (WordRam.Operand.reg 1) (WordRam.Operand.reg 8) 18,
  WordRam.Instr.add 8 (WordRam.Operand.reg 8) (WordRam.Operand.reg 8),
  WordRam.Instr.sub 9 (WordRam.Operand.reg 9) (WordRam.Operand.imm 1), WordRam.Instr.jump 14,
  WordRam.Instr.add 16 (WordRam.Operand.reg 1) (WordRam.Operand.imm 1),
  WordRam.Instr.mul 16 (WordRam.Operand.reg 16) (WordRam.Operand.imm 2),
  WordRam.Instr.add 11 (WordRam.Operand.reg 10) (WordRam.Operand.reg 16),
  WordRam.Instr.mul 16 (WordRam.Operand.reg 1) (WordRam.Operand.imm 2),
  WordRam.Instr.add 12 (WordRam.Operand.reg 11) (WordRam.Operand.reg 16), WordRam.Instr.mov 13 (WordRam.Operand.reg 10),
  WordRam.Instr.mov 14 (WordRam.Operand.reg 8),
  WordRam.Instr.branch (WordRam.Comparison.eq) (WordRam.Operand.reg 14) (WordRam.Operand.imm 0) 30,
  WordRam.Instr.store (WordRam.Operand.reg 13) (WordRam.Operand.imm 0),
  WordRam.Instr.add 13 (WordRam.Operand.reg 13) (WordRam.Operand.imm 1),
  WordRam.Instr.sub 14 (WordRam.Operand.reg 14) (WordRam.Operand.imm 1), WordRam.Instr.jump 25,
  WordRam.Instr.rload 15 (WordRam.Operand.reg 3), WordRam.Instr.mod 16 (WordRam.Operand.reg 15) (WordRam.Operand.imm 2),
  WordRam.Instr.sub 15 (WordRam.Operand.reg 15) (WordRam.Operand.reg 16),
  WordRam.Instr.add 15 (WordRam.Operand.reg 15) (WordRam.Operand.imm 1),
  WordRam.Instr.branch (WordRam.Comparison.eq) (WordRam.Operand.reg 6) (WordRam.Operand.imm 0) 63,
  WordRam.Instr.load 17 (WordRam.Operand.reg 0), WordRam.Instr.mul 18 (WordRam.Operand.reg 15) (WordRam.Operand.reg 17),
  WordRam.Instr.shr 18 (WordRam.Operand.reg 18) (WordRam.Operand.reg 9),
  WordRam.Instr.add 19 (WordRam.Operand.reg 10) (WordRam.Operand.reg 18),
  WordRam.Instr.load 20 (WordRam.Operand.reg 19), WordRam.Instr.mov 21 (WordRam.Operand.reg 20),
  WordRam.Instr.branch (WordRam.Comparison.eq) (WordRam.Operand.reg 21) (WordRam.Operand.imm 0) 53,
  WordRam.Instr.sub 22 (WordRam.Operand.reg 21) (WordRam.Operand.imm 1),
  WordRam.Instr.mul 22 (WordRam.Operand.reg 22) (WordRam.Operand.imm 2),
  WordRam.Instr.add 22 (WordRam.Operand.reg 11) (WordRam.Operand.reg 22),
  WordRam.Instr.load 23 (WordRam.Operand.reg 22),
  WordRam.Instr.branch (WordRam.Comparison.eq) (WordRam.Operand.reg 17) (WordRam.Operand.reg 23) 50,
  WordRam.Instr.add 22 (WordRam.Operand.reg 22) (WordRam.Operand.imm 1), WordRam.Instr.load 21 (WordRam.Operand.reg 22),
  WordRam.Instr.jump 41, WordRam.Instr.add 0 (WordRam.Operand.reg 0) (WordRam.Operand.imm 1),
  WordRam.Instr.sub 6 (WordRam.Operand.reg 6) (WordRam.Operand.imm 1), WordRam.Instr.jump 34,
  WordRam.Instr.mul 25 (WordRam.Operand.reg 7) (WordRam.Operand.imm 2),
  WordRam.Instr.add 25 (WordRam.Operand.reg 25) (WordRam.Operand.reg 11),
  WordRam.Instr.store (WordRam.Operand.reg 25) (WordRam.Operand.reg 17),
  WordRam.Instr.add 25 (WordRam.Operand.reg 25) (WordRam.Operand.imm 1),
  WordRam.Instr.store (WordRam.Operand.reg 25) (WordRam.Operand.reg 20),
  WordRam.Instr.add 24 (WordRam.Operand.reg 12) (WordRam.Operand.reg 7),
  WordRam.Instr.store (WordRam.Operand.reg 24) (WordRam.Operand.reg 17),
  WordRam.Instr.add 7 (WordRam.Operand.reg 7) (WordRam.Operand.imm 1),
  WordRam.Instr.store (WordRam.Operand.reg 19) (WordRam.Operand.reg 7), WordRam.Instr.jump 50,
  WordRam.Instr.mov 0 (WordRam.Operand.reg 12), WordRam.Instr.mov 1 (WordRam.Operand.reg 7), WordRam.Instr.jump 66,
  WordRam.Instr.mov 36 (WordRam.Operand.reg 0), WordRam.Instr.mov 37 (WordRam.Operand.reg 1),
  WordRam.Instr.mov 30 (WordRam.Operand.reg 1), WordRam.Instr.mov 31 (WordRam.Operand.imm 1),
  WordRam.Instr.mov 6 (WordRam.Operand.reg 61),
  WordRam.Instr.branch (WordRam.Comparison.le) (WordRam.Operand.reg 30) (WordRam.Operand.reg 31) 75,
  WordRam.Instr.add 31 (WordRam.Operand.reg 31) (WordRam.Operand.reg 31),
  WordRam.Instr.sub 6 (WordRam.Operand.reg 6) (WordRam.Operand.imm 1), WordRam.Instr.jump 71, WordRam.Instr.jump 76,
  WordRam.Instr.mov 22 (WordRam.Operand.reg 31), WordRam.Instr.mov 38 (WordRam.Operand.reg 6),
  WordRam.Instr.add 2 (WordRam.Operand.reg 56) (WordRam.Operand.imm 4), WordRam.Instr.mov 3 (WordRam.Operand.reg 59),
  WordRam.Instr.mov 1 (WordRam.Operand.reg 37), WordRam.Instr.mov 4 (WordRam.Operand.reg 61),
  WordRam.Instr.mov 32 (WordRam.Operand.reg 61), WordRam.Instr.add 33 (WordRam.Operand.reg 60) (WordRam.Operand.imm 1),
  WordRam.Instr.mov 34 (WordRam.Operand.imm 0), WordRam.Instr.mov 40 (WordRam.Operand.imm 0),
  WordRam.Instr.branch (WordRam.Comparison.eq) (WordRam.Operand.reg 32) (WordRam.Operand.imm 0) 229,
  WordRam.Instr.rload 5 (WordRam.Operand.reg 33), WordRam.Instr.mod 17 (WordRam.Operand.reg 5) (WordRam.Operand.imm 2),
  WordRam.Instr.sub 5 (WordRam.Operand.reg 5) (WordRam.Operand.reg 17),
  WordRam.Instr.add 5 (WordRam.Operand.reg 5) (WordRam.Operand.imm 1),
  WordRam.Instr.add 33 (WordRam.Operand.reg 33) (WordRam.Operand.imm 1),
  WordRam.Instr.sub 32 (WordRam.Operand.reg 32) (WordRam.Operand.imm 1), WordRam.Instr.mov 0 (WordRam.Operand.reg 36),
  WordRam.Instr.mov 8 (WordRam.Operand.reg 1), WordRam.Instr.mov 9 (WordRam.Operand.imm 0),
  WordRam.Instr.mul 7 (WordRam.Operand.reg 1) (WordRam.Operand.imm 6), WordRam.Instr.mov 19 (WordRam.Operand.reg 2),
  WordRam.Instr.mul 20 (WordRam.Operand.reg 22) (WordRam.Operand.imm 4),
  WordRam.Instr.branch (WordRam.Comparison.eq) (WordRam.Operand.reg 20) (WordRam.Operand.imm 0) 104,
  WordRam.Instr.store (WordRam.Operand.reg 19) (WordRam.Operand.imm 0),
  WordRam.Instr.add 19 (WordRam.Operand.reg 19) (WordRam.Operand.imm 1),
  WordRam.Instr.sub 20 (WordRam.Operand.reg 20) (WordRam.Operand.imm 1), WordRam.Instr.jump 99,
  WordRam.Instr.branch (WordRam.Comparison.eq) (WordRam.Operand.reg 8) (WordRam.Operand.imm 0) 129,
  WordRam.Instr.load 10 (WordRam.Operand.reg 0), WordRam.Instr.mul 11 (WordRam.Operand.reg 5) (WordRam.Operand.reg 10),
  WordRam.Instr.shr 11 (WordRam.Operand.reg 11) (WordRam.Operand.reg 6),
  WordRam.Instr.mul 12 (WordRam.Operand.reg 11) (WordRam.Operand.imm 4),
  WordRam.Instr.add 12 (WordRam.Operand.reg 2) (WordRam.Operand.reg 12), WordRam.Instr.load 13 (WordRam.Operand.reg 12),
  WordRam.Instr.mul 15 (WordRam.Operand.reg 13) (WordRam.Operand.imm 2),
  WordRam.Instr.add 15 (WordRam.Operand.reg 15) (WordRam.Operand.imm 1),
  WordRam.Instr.branch (WordRam.Comparison.lt) (WordRam.Operand.reg 7) (WordRam.Operand.reg 15) 131,
  WordRam.Instr.sub 7 (WordRam.Operand.reg 7) (WordRam.Operand.reg 15),
  WordRam.Instr.add 17 (WordRam.Operand.reg 12) (WordRam.Operand.imm 1), WordRam.Instr.load 14 (WordRam.Operand.reg 17),
  WordRam.Instr.mul 16 (WordRam.Operand.reg 9) (WordRam.Operand.imm 2),
  WordRam.Instr.add 16 (WordRam.Operand.reg 3) (WordRam.Operand.reg 16),
  WordRam.Instr.store (WordRam.Operand.reg 16) (WordRam.Operand.reg 10),
  WordRam.Instr.add 16 (WordRam.Operand.reg 16) (WordRam.Operand.imm 1),
  WordRam.Instr.store (WordRam.Operand.reg 16) (WordRam.Operand.reg 14),
  WordRam.Instr.add 9 (WordRam.Operand.reg 9) (WordRam.Operand.imm 1),
  WordRam.Instr.store (WordRam.Operand.reg 17) (WordRam.Operand.reg 9),
  WordRam.Instr.add 13 (WordRam.Operand.reg 13) (WordRam.Operand.imm 1),
  WordRam.Instr.store (WordRam.Operand.reg 12) (WordRam.Operand.reg 13),
  WordRam.Instr.add 0 (WordRam.Operand.reg 0) (WordRam.Operand.imm 1),
  WordRam.Instr.sub 8 (WordRam.Operand.reg 8) (WordRam.Operand.imm 1), WordRam.Instr.jump 104,
  WordRam.Instr.mov 18 (WordRam.Operand.imm 1), WordRam.Instr.jump 133, WordRam.Instr.mov 18 (WordRam.Operand.imm 0),
  WordRam.Instr.jump 133,
  WordRam.Instr.branch (WordRam.Comparison.eq) (WordRam.Operand.reg 18) (WordRam.Operand.imm 1) 135,
  WordRam.Instr.jump 86, WordRam.Instr.store (WordRam.Operand.reg 56) (WordRam.Operand.reg 5),
  WordRam.Instr.add 17 (WordRam.Operand.reg 56) (WordRam.Operand.imm 1),
  WordRam.Instr.store (WordRam.Operand.reg 17) (WordRam.Operand.reg 38),
  WordRam.Instr.add 17 (WordRam.Operand.reg 56) (WordRam.Operand.imm 2),
  WordRam.Instr.store (WordRam.Operand.reg 17) (WordRam.Operand.reg 22),
  WordRam.Instr.add 17 (WordRam.Operand.reg 56) (WordRam.Operand.imm 3),
  WordRam.Instr.store (WordRam.Operand.reg 17) (WordRam.Operand.reg 37), WordRam.Instr.mov 39 (WordRam.Operand.imm 0),
  WordRam.Instr.mov 41 (WordRam.Operand.reg 2), WordRam.Instr.mul 17 (WordRam.Operand.reg 22) (WordRam.Operand.imm 4),
  WordRam.Instr.add 42 (WordRam.Operand.reg 2) (WordRam.Operand.reg 17),
  WordRam.Instr.branch (WordRam.Comparison.eq) (WordRam.Operand.reg 39) (WordRam.Operand.reg 22) 224,
  WordRam.Instr.mov 12 (WordRam.Operand.reg 41), WordRam.Instr.mov 21 (WordRam.Operand.reg 42),
  WordRam.Instr.mov 4 (WordRam.Operand.reg 61), WordRam.Instr.load 28 (WordRam.Operand.reg 12),
  WordRam.Instr.add 17 (WordRam.Operand.reg 12) (WordRam.Operand.imm 1), WordRam.Instr.load 27 (WordRam.Operand.reg 17),
  WordRam.Instr.mov 6 (WordRam.Operand.reg 4), WordRam.Instr.mov 23 (WordRam.Operand.reg 28),
  WordRam.Instr.branch (WordRam.Comparison.le) (WordRam.Operand.reg 28) (WordRam.Operand.imm 1) 164,
  WordRam.Instr.mul 30 (WordRam.Operand.reg 28) (WordRam.Operand.reg 28),
  WordRam.Instr.mul 30 (WordRam.Operand.reg 30) (WordRam.Operand.imm 2), WordRam.Instr.mov 31 (WordRam.Operand.imm 1),
  WordRam.Instr.branch (WordRam.Comparison.le) (WordRam.Operand.reg 30) (WordRam.Operand.reg 31) 163,
  WordRam.Instr.add 31 (WordRam.Operand.reg 31) (WordRam.Operand.reg 31),
  WordRam.Instr.sub 6 (WordRam.Operand.reg 6) (WordRam.Operand.imm 1), WordRam.Instr.jump 159,
  WordRam.Instr.mov 23 (WordRam.Operand.reg 31), WordRam.Instr.mul 17 (WordRam.Operand.reg 23) (WordRam.Operand.imm 2),
  WordRam.Instr.add 29 (WordRam.Operand.reg 21) (WordRam.Operand.reg 17),
  WordRam.Instr.add 17 (WordRam.Operand.reg 12) (WordRam.Operand.imm 3),
  WordRam.Instr.store (WordRam.Operand.reg 17) (WordRam.Operand.reg 21),
  WordRam.Instr.add 17 (WordRam.Operand.reg 12) (WordRam.Operand.imm 2),
  WordRam.Instr.store (WordRam.Operand.reg 17) (WordRam.Operand.reg 6), WordRam.Instr.jump 171,
  WordRam.Instr.mov 32 (WordRam.Operand.reg 61), WordRam.Instr.add 17 (WordRam.Operand.reg 39) (WordRam.Operand.imm 1),
  WordRam.Instr.mul 17 (WordRam.Operand.reg 17) (WordRam.Operand.reg 61),
  WordRam.Instr.add 33 (WordRam.Operand.reg 60) (WordRam.Operand.reg 17),
  WordRam.Instr.add 33 (WordRam.Operand.reg 33) (WordRam.Operand.imm 1), WordRam.Instr.mov 34 (WordRam.Operand.imm 1),
  WordRam.Instr.mov 40 (WordRam.Operand.imm 0),
  WordRam.Instr.branch (WordRam.Comparison.le) (WordRam.Operand.reg 28) (WordRam.Operand.imm 1) 187,
  WordRam.Instr.branch (WordRam.Comparison.eq) (WordRam.Operand.reg 32) (WordRam.Operand.imm 0) 229,
  WordRam.Instr.rload 5 (WordRam.Operand.reg 33), WordRam.Instr.mod 17 (WordRam.Operand.reg 5) (WordRam.Operand.imm 2),
  WordRam.Instr.sub 5 (WordRam.Operand.reg 5) (WordRam.Operand.reg 17),
  WordRam.Instr.add 5 (WordRam.Operand.reg 5) (WordRam.Operand.imm 1),
  WordRam.Instr.add 33 (WordRam.Operand.reg 33) (WordRam.Operand.imm 1),
  WordRam.Instr.sub 32 (WordRam.Operand.reg 32) (WordRam.Operand.imm 1), WordRam.Instr.jump 188,
  WordRam.Instr.mov 5 (WordRam.Operand.imm 1), WordRam.Instr.mov 19 (WordRam.Operand.reg 21),
  WordRam.Instr.mul 20 (WordRam.Operand.reg 23) (WordRam.Operand.imm 2),
  WordRam.Instr.branch (WordRam.Comparison.eq) (WordRam.Operand.reg 20) (WordRam.Operand.imm 0) 195,
  WordRam.Instr.store (WordRam.Operand.reg 19) (WordRam.Operand.imm 0),
  WordRam.Instr.add 19 (WordRam.Operand.reg 19) (WordRam.Operand.imm 1),
  WordRam.Instr.sub 20 (WordRam.Operand.reg 20) (WordRam.Operand.imm 1), WordRam.Instr.jump 190,
  WordRam.Instr.mov 24 (WordRam.Operand.reg 27),
  WordRam.Instr.branch (WordRam.Comparison.eq) (WordRam.Operand.reg 24) (WordRam.Operand.imm 0) 213,
  WordRam.Instr.sub 16 (WordRam.Operand.reg 24) (WordRam.Operand.imm 1),
  WordRam.Instr.mul 16 (WordRam.Operand.reg 16) (WordRam.Operand.imm 2),
  WordRam.Instr.add 16 (WordRam.Operand.reg 3) (WordRam.Operand.reg 16), WordRam.Instr.load 10 (WordRam.Operand.reg 16),
  WordRam.Instr.mul 11 (WordRam.Operand.reg 5) (WordRam.Operand.reg 10),
  WordRam.Instr.shr 11 (WordRam.Operand.reg 11) (WordRam.Operand.reg 6),
  WordRam.Instr.mul 25 (WordRam.Operand.reg 11) (WordRam.Operand.imm 2),
  WordRam.Instr.add 25 (WordRam.Operand.reg 21) (WordRam.Operand.reg 25),
  WordRam.Instr.load 26 (WordRam.Operand.reg 25),
  WordRam.Instr.branch (WordRam.Comparison.ne) (WordRam.Operand.reg 26) (WordRam.Operand.imm 0) 215,
  WordRam.Instr.store (WordRam.Operand.reg 25) (WordRam.Operand.imm 1),
  WordRam.Instr.add 25 (WordRam.Operand.reg 25) (WordRam.Operand.imm 1),
  WordRam.Instr.store (WordRam.Operand.reg 25) (WordRam.Operand.reg 10),
  WordRam.Instr.add 16 (WordRam.Operand.reg 16) (WordRam.Operand.imm 1), WordRam.Instr.load 24 (WordRam.Operand.reg 16),
  WordRam.Instr.jump 196, WordRam.Instr.mov 18 (WordRam.Operand.imm 1), WordRam.Instr.jump 217,
  WordRam.Instr.mov 18 (WordRam.Operand.imm 0), WordRam.Instr.jump 217,
  WordRam.Instr.branch (WordRam.Comparison.eq) (WordRam.Operand.reg 18) (WordRam.Operand.imm 0) 179,
  WordRam.Instr.add 17 (WordRam.Operand.reg 41) (WordRam.Operand.imm 1),
  WordRam.Instr.store (WordRam.Operand.reg 17) (WordRam.Operand.reg 5), WordRam.Instr.mov 42 (WordRam.Operand.reg 29),
  WordRam.Instr.add 41 (WordRam.Operand.reg 41) (WordRam.Operand.imm 4),
  WordRam.Instr.add 39 (WordRam.Operand.reg 39) (WordRam.Operand.imm 1), WordRam.Instr.jump 146,
  WordRam.Instr.mov 0 (WordRam.Operand.reg 56), WordRam.Instr.sub 1 (WordRam.Operand.reg 42) (WordRam.Operand.reg 56),
  WordRam.Instr.mov 2 (WordRam.Operand.reg 37), WordRam.Instr.mov 18 (WordRam.Operand.imm 1), WordRam.Instr.halt,
  WordRam.Instr.mov 18 (WordRam.Operand.imm 0), WordRam.Instr.halt] := by decide

@[simp] theorem location_deduplicated : location .deduplicated = 66 := by decide

@[simp] theorem location_rounded : location .rounded = 76 := by decide

@[simp] theorem location_rootChoose : location .rootChoose = 86 := by decide

@[simp] theorem location_rootTrial : location .rootTrial = 93 := by decide

@[simp] theorem location_rootResult : location .rootResult = 133 := by decide

@[simp] theorem location_rootAccepted : location .rootAccepted = 135 := by decide

@[simp] theorem location_childLoop : location .childLoop = 146 := by decide

@[simp] theorem location_allocated : location .allocated = 171 := by decide

@[simp] theorem location_childChoose : location .childChoose = 179 := by decide

@[simp] theorem location_directChild : location .directChild = 187 := by decide

@[simp] theorem location_childTrial : location .childTrial = 188 := by decide

@[simp] theorem location_childResult : location .childResult = 217 := by decide

@[simp] theorem location_finish : location .finish = 224 := by decide

@[simp] theorem location_failed : location .failed = 229 := by decide

@[simp] theorem location_dedup_block : location (.block .dedup 0) = 9 := by decide

@[simp] theorem location_rounding_block : location (.block .rounding 0) = 71 := by decide

@[simp] theorem location_root_block : location (.block .root 0) = 94 := by decide

@[simp] theorem location_allocation_block : location (.block .allocation 0) = 150 := by decide

@[simp] theorem location_child_block : location (.block .child 0) = 188 := by decide

end PerfectHash.Bounded
