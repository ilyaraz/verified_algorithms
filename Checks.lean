import WordRam
import WordRam.Examples
import DataStructures
import PerfectHashTools
import DataStructures.PerfectHash.Examples
import DataStructures.PerfectHash.Build.Examples
import DataStructures.PerfectHash.Query.Examples
import DataStructures.PerfectHash.Construction.Examples
import DataStructures.PerfectHash.Bounded.Examples
import DataStructures.PerfectHash.Total.Examples
import Hashing
import Hashing.Examples
import Probability
import Probability.Examples
import Algorithms
import Algorithms.Dedup.Examples
import Lean
import RamLang
open WordRam

example : word 4 15 + word 4 1 = word 4 0 := by decide
example : word 4 0 - word 4 1 = word 4 15 := by decide
example : word 4 7 * word 4 3 = word 4 5 := by decide
example : word 4 7 % word 4 3 = word 4 1 := by decide
example : word 4 7 % word 4 1 = word 4 0 := by decide
example : word 4 7 % word 4 0 = word 4 7 := by decide

example : probability (fun rho : RandomMemory 1 => rho (word 1 0) = word 1 1) = 1/2 := by
  rw [probability_cell]
  norm_num [modulus]

example : probability (fun rho : RandomMemory 1 =>
    rho (word 1 0) = word 1 1 ∧ rho (word 1 1) = word 1 0) = 1/4 := by
  rw [probability_two_cells _ _ (by decide)]
  norm_num [modulus]

example : probability (fun rho : RandomMemory 1 =>
    rho (word 1 0) = word 1 1 ∧ rho (word 1 0) = word 1 0) = 0 := by
  rw [probability_repeated_cell]
  norm_num [word]

example : conditionalProbability (fun rho : RandomMemory 1 => rho (word 1 1) = word 1 0)
    (Matches {word 1 0} (fun _ => word 1 1)) = 1/2 := by
  rw [conditional_fresh_cell _ _ _ (by decide)]
  norm_num [modulus]

namespace WordRam.Examples

theorem randomRoundTrip_probability (regs : Registers w 2) (mem : DataMemory w)
    (x : Word w) :
    runProbability randomRoundTrip 4 (.initial regs mem) (fun r => r.state.regs 0 = x) =
      (modulus w : ℝ)⁻¹ := by
  unfold runProbability
  calc
    _ = probability (fun rho => rho (word w 3) = x) := probability_congr (by
      intro rho
      dsimp only
      rw [(randomRoundTrip_spec rho regs mem).2.2.1])
    _ = _ := probability_cell _ _

theorem spin_expectedSteps (w fuel : Nat) :
    expectedSteps spin fuel (State.zero w 0) = fuel := by
  have h : ∀ rho : RandomMemory w, (run spin rho fuel (State.zero w 0)).steps = fuel := by
    intro rho
    exact run_exhausted_steps (spin_diverges rho _ rfl fuel)
  simp [expectedSteps, h]

end WordRam.Examples

-- Audit by source module, including private helpers and all examples.
-- These commands inspect proofs; they do not provide proof terms to the library.
run_cmd do
  let env ← Lean.getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let projectModules := [`WordRam, `RamLang, `DataStructures, `Hashing, `Probability,
    `Algorithms, `PerfectHashTools, `Checks]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    -- Declarations in the current check file have no imported module index.
    let mod := (← Lean.findModuleOf? name).getD `Checks
    if projectModules.contains mod.getRoot then
      for ax in ← Lean.collectAxioms name do
        unless allowed.contains ax do
          throwError "Unexpected axiom in {name}: {ax}"
      checked := checked + 1
  Lean.logInfo m!"Axiom audit passed for {checked} library declarations."
  let executable := [``RamLang.requireSome, ``RamLang.Binary.eval,
      ``RamLang.Function.slots, ``RamLang.Function.frameSize, ``RamLang.duplicate,
      ``RamLang.checkLocal, ``RamLang.checkAtom, ``RamLang.checkCondition,
      ``RamLang.checkPrimitive, ``RamLang.joinInitialized, ``RamLang.checkStmt,
      ``RamLang.checkFunction, ``RamLang.check, ``RamLang.Atom.eval, ``RamLang.writeLocal,
      ``RamLang.Condition.eval, ``RamLang.Primitive.eval, ``RamLang.Config.initial,
      ``RamLang.Config.stackWords, ``RamLang.enter, ``RamLang.step,
      ``RamLang.RunResult.prepend, ``RamLang.run,
      ``RamLang.Examples.sumFunction, ``RamLang.Examples.sum, ``RamLang.Examples.execute,
      ``RamLang.Examples.parityFunction, ``RamLang.Examples.parity,
      ``RamLang.Examples.earlyReturn, ``RamLang.Examples.spin, ``RamLang.Examples.spinState,
      ``word, ``unsignedMod, ``unsignedShiftRight, ``update, ``Operand.eval, ``Comparison.test, ``State.initial,
      ``State.zero, ``State.put, ``step, ``run, ``RunResult.prepend,
      ``RunResult.dataFootprint, ``RunResult.writeFootprint, ``RunResult.randomReads,
      ``RunResult.randomFootprint, ``RunResult.randomBitsExposed,
      ``Examples.arithmetic, ``Examples.mulMod, ``Examples.randomRoundTrip,
      ``Examples.countdown, ``Examples.spin, ``Examples.branchExample,
      ``Instr.pcRelocatable, ``Legacy.step, ``Legacy.run, ``CallExamples.nested,
      ``Instr.relocate, ``Assembly.Instruction.resolve, ``Assembly.assemble,
      ``Assembly.instructions, ``Assembly.labelOffset, ``Assembly.labelsDefined,
      ``Assembly.Instruction.target, ``Assembly.compile, ``State.relocate,
      ``Arrays.readInstruction, ``Arrays.writeInstruction, ``Arrays.assembly, ``Arrays.program,
      ``Examples.shiftAlias, ``Examples.arrayBoundaryState,
      ``Hashing.MultiplyShift.encode, ``Hashing.MultiplyShift.sample, ``Hashing.MultiplyShift.eval,
      ``Hashing.MultiplyShift.first, ``Hashing.MultiplyShift.advance, ``Hashing.MultiplyShift.candidate,
      ``Hashing.MultiplyShiftRam.evaluator, ``Hashing.MultiplyShiftRam.sampler,
      ``Hashing.MultiplyShiftRam.advanceSeed,
      ``Hashing.Examples.collisionCheck, ``Hashing.Examples.evaluatorRegisters,
      ``RandomBlocks.address, ``RandomBlocks.stageBase,
      ``FiniteProbability.Retry.attempts, ``FiniteProbability.Retry.failed, ``FiniteProbability.Retry.find,
      ``FiniteProbability.FiniteSearch.search, ``FiniteProbability.FiniteSearch.enumerationAttempts,
      ``FiniteProbability.FiniteSearch.searchWork, ``FiniteProbability.FiniteSearch.work,
      ``FiniteProbability.Examples.predicateSearch,
      ``Dedup.workspaceCapacity, ``Dedup.assembly, ``Dedup.location, ``Dedup.program, ``Dedup.fuel,
      ``Dedup.Examples.layout, ``Dedup.Examples.memory, ``Dedup.Examples.registers,
      ``Dedup.Examples.execute, ``Dedup.Examples.values,
      ``Hashing.PowerOfTwo.computeBitsAux, ``Hashing.PowerOfTwo.computeBits, ``Hashing.PowerOfTwo.computeSize,
      ``FiniteProbability.consFin, ``FiniteProbability.sequenceFin,
      ``PerfectHash.Buckets.keys, ``PerfectHash.Buckets.count, ``PerfectHash.Buckets.pairs,
      ``PerfectHash.rootAccept, ``PerfectHash.childAccept, ``PerfectHash.Sizes.childSlots,
      ``PerfectHash.Build.Model.rootSearch, ``PerfectHash.Build.Model.childSearch,
      ``PerfectHash.Build.Model.construct, ``PerfectHash.Build.Model.advance, ``PerfectHash.Build.Model.advanceMany,
      ``PerfectHash.Build.Model.position, ``PerfectHash.Build.Model.stored,
      ``PerfectHash.Query.assembly, ``PerfectHash.Query.location, ``PerfectHash.Query.program,
      ``PerfectHash.Query.cost, ``PerfectHash.Query.Examples.hashedMemory,
      ``PerfectHash.Query.Examples.registers, ``PerfectHash.Query.Examples.execute,
      ``PerfectHash.Query.Examples.emptyMemory, ``PerfectHash.Query.Examples.singletonMemory,
      ``StaticSet.registerCount, ``StaticSet.readDescriptor,
      ``PerfectHash.dictionaryCapacity, ``PerfectHash.workspaceCapacity,
      ``PerfectHash.bucketCapacity, ``PerfectHash.randomCapacity,
      ``PerfectHash.Layout.input, ``PerfectHash.Layout.output,
      ``PerfectHash.Layout.scratch, ``PerfectHash.Layout.random,
      ``PerfectHash.buildRegisters, ``PerfectHash.peakWords,
      ``PerfectHash.canonicalLayout, ``PerfectHash.sufficientWidth,
      ``PerfectHash.embedWord, ``PerfectHash.inputMemory,
      ``PerfectHash.worstInstructions, ``PerfectHash.constructionFuel,
      ``PerfectHash.Examples.repeatedBoundaryInput,
      ``WordRam.Instr.destination,
      ``PerfectHash.Construction.Allocation.childShift,
      ``PerfectHash.Construction.Allocation.policy,
      ``PerfectHash.Construction.Allocation.loaded,
      ``PerfectHash.Construction.Allocation.loadTrace,
      ``PerfectHash.Construction.Allocation.initialized,
      ``PerfectHash.Construction.Allocation.rounded,
      ``PerfectHash.Construction.Allocation.finalMemory,
      ``PerfectHash.Construction.Allocation.finished,
      ``PerfectHash.Construction.Allocation.finishTrace,
      ``PerfectHash.Construction.Allocation.assembly,
      ``PerfectHash.Construction.Allocation.location,
      ``PerfectHash.Construction.Allocation.program,
      ``PerfectHash.Construction.Child.initial,
      ``PerfectHash.Construction.Child.startLoop,
      ``PerfectHash.Construction.Child.nodeAddress,
      ``PerfectHash.Construction.Child.hashed,
      ``PerfectHash.Construction.Child.slotAddress,
      ``PerfectHash.Construction.Child.probe,
      ``PerfectHash.Construction.Child.probeTrace,
      ``PerfectHash.Construction.Child.insertedMemory,
      ``PerfectHash.Construction.Child.inserted,
      ``PerfectHash.Construction.Child.insertedTrace,
      ``PerfectHash.Construction.Child.clearStart,
      ``PerfectHash.Construction.Child.cleared,
      ``PerfectHash.Construction.Child.prepared,
      ``PerfectHash.Construction.Child.assembly,
      ``PerfectHash.Construction.Child.location,
      ``PerfectHash.Construction.Child.program,
      ``PerfectHash.Construction.Child.roundNext,
      ``PerfectHash.Construction.Child.roundTrace,
      ``PerfectHash.Construction.Child.policy,
      ``PerfectHash.Construction.Clear.program,
      ``PerfectHash.Construction.Clear.next,
      ``PerfectHash.Construction.Clear.clearMany,
      ``PerfectHash.Construction.Clear.clearTrace,
      ``PerfectHash.Construction.groupAccepted,
      ``PerfectHash.Construction.Enumeration.program,
      ``PerfectHash.Construction.Enumeration.next,
      ``PerfectHash.Construction.Examples.rootMemory,
      ``PerfectHash.Construction.Examples.rootRegisters,
      ``PerfectHash.Construction.Examples.rootRun,
      ``PerfectHash.Construction.Examples.childRegisters,
      ``PerfectHash.Construction.Examples.childRun,
      ``PerfectHash.Construction.Examples.allocationRegisters,
      ``PerfectHash.Construction.Examples.allocationRun,
      ``PerfectHash.Construction.Examples.singletonMemory,
      ``PerfectHash.Construction.Examples.singletonRegisters,
      ``PerfectHash.Construction.Examples.singletonRun,
      ``PerfectHash.Construction.Examples.largeRootMemory,
      ``PerfectHash.Construction.Examples.largeRootRegisters,
      ``PerfectHash.Construction.Examples.largeRootRun,
      ``PerfectHash.Construction.groupMemory,
      ``PerfectHash.Construction.Registers.input,
      ``PerfectHash.Construction.Registers.count,
      ``PerfectHash.Construction.Registers.directory,
      ``PerfectHash.Construction.Registers.nodes,
      ``PerfectHash.Construction.Registers.width,
      ``PerfectHash.Construction.Registers.seed,
      ``PerfectHash.Construction.Registers.shift,
      ``PerfectHash.Construction.Registers.budget,
      ``PerfectHash.Construction.Registers.remaining,
      ``PerfectHash.Construction.Registers.distinct,
      ``PerfectHash.Construction.Registers.key,
      ``PerfectHash.Construction.Registers.hash,
      ``PerfectHash.Construction.Registers.address,
      ``PerfectHash.Construction.Registers.oldCount,
      ``PerfectHash.Construction.Registers.oldHead,
      ``PerfectHash.Construction.Registers.increment,
      ``PerfectHash.Construction.Registers.node,
      ``PerfectHash.Construction.Registers.temp,
      ``PerfectHash.Construction.Registers.status,
      ``PerfectHash.Construction.Registers.clearCursor,
      ``PerfectHash.Construction.Registers.clearRemaining,
      ``PerfectHash.Construction.Registers.table,
      ``PerfectHash.Construction.Registers.buckets,
      ``PerfectHash.Construction.Registers.slots,
      ``PerfectHash.Construction.Registers.cursor,
      ``PerfectHash.Construction.Registers.slot,
      ``PerfectHash.Construction.Registers.flag,
      ``PerfectHash.Construction.Registers.rootHead,
      ``PerfectHash.Construction.Registers.childCount,
      ``PerfectHash.Construction.Registers.tableEnd,
      ``PerfectHash.Construction.Registers.roundTarget,
      ``PerfectHash.Construction.Registers.size,
      ``PerfectHash.Construction.Root.initial,
      ``PerfectHash.Construction.Root.hashed,
      ``PerfectHash.Construction.Root.bucketAddress,
      ``PerfectHash.Construction.Root.probe,
      ``PerfectHash.Construction.Root.probeTrace,
      ``PerfectHash.Construction.Root.newNode,
      ``PerfectHash.Construction.Root.insertedMemory,
      ``PerfectHash.Construction.Root.inserted,
      ``PerfectHash.Construction.Root.insertedTrace,
      ``PerfectHash.Construction.Root.clearStart,
      ``PerfectHash.Construction.Root.cleared,
      ``PerfectHash.Construction.Root.assembly,
      ``PerfectHash.Construction.Root.location,
      ``PerfectHash.Construction.Root.program,
      ``PerfectHash.Construction.Root.roundNext,
      ``PerfectHash.Construction.Root.roundTrace,
      ``PerfectHash.Construction.Root.policy,
      ``PerfectHash.Construction.Round.program,
      ``PerfectHash.Construction.Round.roundNext,
      ``PerfectHash.Construction.slotContents,
      ``PerfectHash.Construction.slotMemory,
      ``PerfectHash.Construction.childAccepted,
      ``WordRam.consecutiveAddresses,
      ``PerfectHash.Bounded.inlineInstruction, ``PerfectHash.Bounded.inlineAux,
      ``PerfectHash.Bounded.inlineBlock, ``PerfectHash.Bounded.sampleCode,
      ``PerfectHash.Bounded.assembly, ``PerfectHash.Bounded.location, ``PerfectHash.Bounded.program,
      ``PerfectHash.Bounded.fuel,
      ``PerfectHash.Bounded.Examples.repeatedKeys, ``PerfectHash.Bounded.Examples.memory,
      ``PerfectHash.Bounded.Examples.execute, ``PerfectHash.Bounded.Examples.goodRun,
      ``PerfectHash.Bounded.Examples.queryAnswer, ``PerfectHash.Bounded.Examples.overwritten,
      ``PerfectHash.Bounded.Examples.rootFailure, ``PerfectHash.Bounded.Examples.childFailure,
      ``PerfectHash.Bounded.Examples.lastRootAttempt, ``PerfectHash.Bounded.Examples.emptyRun,
      ``PerfectHash.Bounded.Examples.equalRun, ``PerfectHash.Bounded.Examples.boundaryRun,
      ``PerfectHash.Total.fallbackCode, ``PerfectHash.Total.program,
      ``PerfectHash.Total.seedCount, ``PerfectHash.Total.candidate, ``PerfectHash.Total.bounds,
      ``PerfectHash.Total.Examples.fallbackKeys, ``PerfectHash.Total.Examples.execute,
      ``PerfectHash.Total.Examples.rootImage, ``PerfectHash.Total.Examples.emptyBudgetState,
      ``PerfectHash.Total.Examples.checkRun,
      ``PerfectHash.fksCode, ``PerfectHash.Exported.preprocess, ``PerfectHash.Exported.query,
      ``PerfectHash.Export.register, ``PerfectHash.Export.operand, ``PerfectHash.Export.comparison,
      ``PerfectHash.Export.instruction, ``PerfectHash.Export.program, ``PerfectHash.Export.source,
      ``PerfectHash.Export.write, ``PerfectHash.Demo.keys, ``PerfectHash.Demo.layout,
      ``PerfectHash.Demo.memory, ``PerfectHash.Demo.initial, ``PerfectHash.Demo.built,
      ``PerfectHash.Demo.query, ``PerfectHash.Demo.run, ``main]
  for name in executable do
    let axioms ← Lean.collectAxioms name
    unless axioms.isEmpty do
      throwError "Executable definition {name} uses axioms: {axioms}"
  Lean.logInfo m!"Executable audit passed for {executable.length} definitions: no axiom dependencies."
