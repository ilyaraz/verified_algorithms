import Hashing.Source.Rounding
import DataStructures.PerfectHash.Sizes

namespace PerfectHash.Source.Allocation
open WordRam RamLang RamLang.Compiler RamLang.Logic

set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Allocate one child in the existing packed format. The rounding helper is an
ordinary call and writes the directory's shift field; no table cell is cleared
or overwritten by allocation, so completed siblings are preserved. -/
def program : RamLang.Program := ram_program allocate {
  fn allocate(directory, table, width) {
    let count = load(directory);
    let slots = count;
    if (count <= 1) {
      store(directory + 2, width);
    } else {
      slots = round(2 * count * count, width, directory + 2);
    }
    store(directory + 3, table);
    return table + 2 * slots;
  }
  fn round(target, width, shiftCell) {
    let size = 1;
    while (size < target) {
      size = size + size;
      width = width - 1;
    }
    store(shiftCell, width);
    return size;
  }
}

/-- The source allocation function can be embedded with its declared helper. -/
def function : RamLang.Function := program.functions[0]'(by decide)

/-- The implementation of rounding is exactly the reusable verified function. -/
theorem round_eq : program.functions[1]? = some Hashing.Source.Rounding.function := by rfl

/-- Empty and singleton children store the full width; larger children store the
shift corresponding to twice their squared cardinality rounded upward. -/
def shift (w b : Nat) : Nat := if b ≤ 1 then w else w-Hashing.PowerOfTwo.bits (2*b*b)

/-- Exact application effect: initialize shift and absolute table address. -/
def memory (mem : DataMemory w) (directory table b : Nat) : DataMemory w :=
  update (update mem (word w (directory+2)) (word w (shift w b))) (word w (directory+3)) (word w table)

/-- The three application events are independent of the number of doublings. -/
def trace (w directory table b : Nat) : List (Access w) :=
  [.dataRead (word w directory) (word w b),
   .dataWrite (word w (directory+2)) (word w (shift w b)),
   .dataWrite (word w (directory+3)) (word w table)]

/-- A numerical instruction allowance covers direct and rounded children. -/
def work (b : Nat) : Nat := 160+19*Hashing.PowerOfTwo.bits (2*b*b)

macro "allocation_test" : tactic => `(tactic|
  simp [Condition.eval,Atom.eval,requireSome,Comparison.test,Binary.eval,
    bind,pure,Except.bind,Except.pure,WordRam.word_add,WordRam.word_mul,WordRam.word_toNat_of_lt, *])

/-- Allocation uses the established rounded-size model, with all call work
charged and at most one six-word helper frame. Its only application writes are
the two directory fields, even when neighboring tables are already populated. -/
theorem contract {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (directory table b : Nat)
    (hlookup : p.functions[1]? = some Hashing.Source.Rounding.function)
    (hfree : 6 ≤ free) (hb : b < modulus w) (hdir : (Region.mk directory 4).Fits w)
    (htable : (Region.mk table (2*Sizes.childSlots b)).Fits w)
    (hcount : mem (word w directory) = word w b) :
    Contract p rho free function.body
      ([word w directory,word w table,word w w].map some ++ List.replicate function.locals.length none) mem
      (fun flow mem' log => flow = .returned (word w (table+2*Sizes.childSlots b)) ∧
        mem' = memory mem directory table b ∧ log = trace w directory table b) (work b) 6 := by
  have hone : 1 < modulus w := by have hd : directory+4 < modulus w := hdir; omega
  have hslots : Sizes.childSlots b < modulus w := by
    have ht : table+2*Sizes.childSlots b < modulus w := htable
    omega
  have hbMod : b % modulus w = b := Nat.mod_eq_of_lt hb
  have honeMod : 1 % modulus w = 1 := Nat.mod_eq_of_lt hone
  by_cases hs : b ≤ 1
  · refine ⟨_,_,_,by ram_derive (allocation_test),?_,?_,?_⟩
    · simp [memory,trace,shift,Sizes.childSlots,hs,Binary.eval,WordRam.word_add,WordRam.word_mul,
        hcount,Nat.add_assoc,Nat.mul_comm]
    · ram_cost
      unfold work
      omega
    · ram_cost
  · have hf : Hashing.PowerOfTwo.size (2*b*b) < modulus w := by
      simpa only [Sizes.childSlots,hs,↓reduceIte,Hashing.PowerOfTwo.computeSize_eq] using hslots
    have hc := Hashing.Source.Rounding.contract (free := free-6) p rho mem (2*b*b)
      (word w directory+word w 2) hf
    have hc' : Contract p rho (free-6) Hashing.Source.Rounding.function.body
        ([word w 2 * mem (word w directory) * mem (word w directory),word w w,
          word w directory+word w 2].map some ++ List.replicate Hashing.Source.Rounding.function.locals.length none) mem
        (fun flow mem' log => flow = .returned (word w (Hashing.PowerOfTwo.size (2*b*b))) ∧
          mem' = update mem (word w directory+word w 2) (word w (w-Hashing.PowerOfTwo.bits (2*b*b))) ∧
          log = [.dataWrite (word w directory+word w 2) (word w (w-Hashing.PowerOfTwo.bits (2*b*b)))])
        (19*Hashing.PowerOfTwo.bits (2*b*b)+22) 0 := by
      simpa only [hcount,WordRam.word_mul] using hc
    obtain ⟨flow,mem',log,d,⟨hflow,hmem,hlog⟩,ht,hpeak⟩ := hc'
    subst flow
    subst mem'
    subst log
    refine ⟨_,_,_,by ram_derive (allocation_test),?_,?_,?_⟩
    · simp [memory,trace,shift,Sizes.childSlots,hs,Hashing.PowerOfTwo.computeSize_eq,
        Binary.eval,WordRam.word_add,WordRam.word_mul,hcount,Nat.add_assoc,Nat.mul_comm]
    · ram_cost
      unfold work
      omega
    · ram_cost
      change 6+extraStack d ≤ 6
      omega

/-- The updated directory keeps its count and linked head, and initializes
exactly the shift and absolute table-pointer fields. -/
theorem memory_fields {w : Nat} (mem : DataMemory w) (directory table b : Nat)
    (hf : (Region.mk directory 4).Fits w) :
    memory mem directory table b (word w directory) = mem (word w directory) ∧
    memory mem directory table b (word w (directory+1)) = mem (word w (directory+1)) ∧
    memory mem directory table b (word w (directory+2)) = word w (shift w b) ∧
    memory mem directory table b (word w (directory+3)) = word w table := by
  have hd : directory+4 < modulus w := hf
  have effect (a : Addr w) : memory mem directory table b a =
      if a.toNat = directory+3 then word w table
      else if a.toNat = directory+2 then word w (shift w b) else mem a := by
    unfold memory
    rw [update_word _ _ _ (by omega),update_word _ _ _ (by omega)]
  simp only [effect,word_toNat_of_lt (by omega : directory < modulus w),
    word_toNat_of_lt (by omega : directory+1 < modulus w),
    word_toNat_of_lt (by omega : directory+2 < modulus w),
    word_toNat_of_lt (by omega : directory+3 < modulus w)]
  simp

/-- Every previously allocated table outside this directory survives allocation. -/
theorem memory_outside {w : Nat} (mem : DataMemory w) (directory table b : Nat)
    (hf : (Region.mk directory 4).Fits w) (a : Addr w) (ha : ¬ (Region.mk directory 4).Contains a) :
    memory mem directory table b a = mem a := by
  have hn₂ : a ≠ word w (directory+2) := by
    intro h
    subst a
    exact ha (Region.contains_index hf (by decide : 2 < 4))
  have hn₃ : a ≠ word w (directory+3) := by
    intro h
    subst a
    exact ha (Region.contains_index hf (by decide : 3 < 4))
  simp [memory,update,hn₂,hn₃]

end PerfectHash.Source.Allocation
