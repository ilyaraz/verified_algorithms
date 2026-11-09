import Hashing.Source.MultiplyShift

namespace Hashing.Source.Sampling
open WordRam RamLang RamLang.Compiler RamLang.Logic

/-- One explicitly addressed random read followed by the ordinary arithmetic
odd-seed sampler. No random oracle or mathematical seed is a runtime argument. -/
def program : RamLang.Program := ram_program sample_seed {
  fn sample_seed(address) {
    let raw = random(address);
    return raw - raw % 2 + 1;
  }
}

/-- Callable sampler with one parameter and four charged local slots. -/
def function : RamLang.Function := program.functions[0]'(by decide)

/-- The source sampler agrees with the existing wrapping arithmetic model,
reads exactly the supplied random address, and leaves ordinary memory unchanged. -/
def evaluation {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (address : Word w) :
    Evaluation p rho free function.body
      ([address].map some ++ List.replicate function.locals.length none) mem
      (.returned (Hashing.MultiplyShift.sample (rho address))) mem [.randomRead address (rho address)] := by
  ram_derive (ram_simp)

/-- Sampling charges thirty-two body instructions and no nested stack frame. -/
theorem resources {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (address : Word w) :
    instructions (evaluation (free := free) p rho mem address) = 32 ∧
    extraStack (evaluation (free := free) p rho mem address) = 0 ∧ function.frameSize = 7 := by
  exact ⟨rfl,rfl,rfl⟩

/-- At positive width, the computed result is precisely the existing encoding
of the sampled seed index. Probability and independence are separate theorems. -/
theorem contract {w free : Nat} (p : RamLang.Program) (rho : RandomMemory (w+1))
    (mem : DataMemory (w+1)) (address : Word (w+1)) :
    Contract p rho free function.body
      ([address].map some ++ List.replicate function.locals.length none) mem
      (fun flow mem' trace =>
        flow = .returned (Hashing.MultiplyShift.encode (Hashing.MultiplyShift.rawIndex (rho address))) ∧
        mem' = mem ∧ trace = [.randomRead address (rho address)]) 32 0 := by
  exact Contract.ofEvaluation (evaluation p rho mem address)
    ⟨congrArg Flow.returned (Hashing.MultiplyShift.sample_eq_encode _),rfl,rfl⟩
    (Nat.le_of_eq (resources p rho mem address).1) (Nat.le_of_eq (resources p rho mem address).2.1)

end Hashing.Source.Sampling
