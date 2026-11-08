import RamLang.WellFormed
import RamLang.CallingConvention
import WordRam.Assembly

namespace RamLang.Compiler
open WordRam ABI

abbrev Code := List (Instr registers)

/-- Load a source atom into a compiler temporary, with explicit charged slot access. -/
def atom (dst : Reg registers) : Atom → Code
  | .literal n => [.mov dst (.imm n)]
  | .local id => [.add address (.reg fp) (.imm (2+id)), .load dst (.reg address)]

def spill (id : Local) (src : Reg registers) : Code :=
  [.add address (.reg fp) (.imm (2+id)), .store (.reg address) (.reg src)]

def binary (op : Binary) : Instr registers :=
  match op with
  | .add => .add left (.reg left) (.reg right)
  | .sub => .sub left (.reg left) (.reg right)
  | .mul => .mul left (.reg left) (.reg right)
  | .mod => .mod left (.reg left) (.reg right)
  | .shr => .shr left (.reg left) (.reg right)

def primitive : Primitive → Code
  | .move d x => atom left x ++ spill d left
  | .binary d op x y => atom left x ++ atom right y ++ [binary op] ++ spill d left
  | .load d a => atom left a ++ [.load left (.reg left)] ++ spill d left
  | .random d a => atom left a ++ [.rload left (.reg left)] ++ spill d left
  | .store a x => atom left a ++ atom right x ++ [.store (.reg left) (.reg right)]

/-- Copy arguments into the prospective frame while caller fp is still installed. -/
def arguments : Nat → List Atom → Code
  | _, [] => []
  | i, a :: rest => atom left a ++
      [.add address (.reg sp) (.imm (2+i)), .store (.reg address) (.reg left)] ++
      arguments (i+1) rest

/-- Save the incoming link before any nested call can overwrite it. -/
def prologue : Code := [.add address (.reg fp) (.imm 1), .store (.reg address) (.reg link)]

/-- Free the frame without clearing it, restore the caller, and return the result. -/
def epilogue : Code := [
  .add address (.reg fp) (.imm 1), .load link (.reg address), .load caller (.reg fp),
  .mov sp (.reg fp), .mov fp (.reg caller), .jumpReg (.reg link)]

/-- Sizes depend only on finite syntax; function references are never expanded. -/
def size : Stmt → Nat
  | .skip => 0
  | .primitive op => (primitive op).length
  | .seq a b => size a + size b
  | .ite c a b => (atom left c.left).length + (atom right c.right).length + 2 + size a + size b
  | .while c body => (atom left c.left).length + (atom right c.right).length + 3 + size body
  | .call _ _ args => (arguments 0 args).length + 8
  | .ret x => (atom result x).length + epilogue.length

/-- Lower against final linked function addresses. pc is the first instruction
of this statement; exhausted is the shared error wrapper. -/
def lower (frames entries : FunctionId → Nat) (exhausted pc : Nat) : Stmt → Code
  | .skip => []
  | .primitive op => primitive op
  | .seq a b => lower frames entries exhausted pc a ++
      lower frames entries exhausted (pc + size a) b
  | .ite c yes no =>
    let test := atom left c.left ++ atom right c.right
    let noPC := pc + test.length + 1
    let yesPC := noPC + size no + 1
    test ++ [.branch c.comparison (.reg left) (.reg right) yesPC] ++
      lower frames entries exhausted noPC no ++ [.jump (yesPC + size yes)] ++
      lower frames entries exhausted yesPC yes
  | .while c body =>
    let test := atom left c.left ++ atom right c.right
    let bodyPC := pc + test.length + 2
    test ++ [.branch c.comparison (.reg left) (.reg right) bodyPC,
      .jump (bodyPC + size body + 1)] ++
      lower frames entries exhausted bodyPC body ++ [.jump pc]
  | .call dst id args =>
    [.sub left (.reg limit) (.reg sp),
      .branch .lt (.reg left) (.imm (frames id)) exhausted,
      .store (.reg sp) (.reg fp)] ++ arguments 0 args ++
    [.mov fp (.reg sp), .add sp (.reg sp) (.imm (frames id)), .call link (entries id)] ++
      spill dst result
  | .ret x => atom result x ++ epilogue

/-- Every syntax node emits its advertised finite instruction template. -/
theorem lower_length (s : Stmt) (frames entries : FunctionId → Nat) (exhausted pc : Nat) :
    (lower frames entries exhausted pc s).length = size s := by
  induction s generalizing pc with
  | skip => rfl
  | primitive op => rfl
  | seq a b ia ib => simp [lower, size, ia, ib]
  | ite c a b ia ib => simp [lower, size, ia, ib]; omega
  | «while» c body ih => simp [lower, size, ih]; omega
  | call dst id args => simp [lower, size, spill]
  | ret value => simp [lower, size]

end RamLang.Compiler
