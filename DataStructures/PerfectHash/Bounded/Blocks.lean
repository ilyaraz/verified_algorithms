import DataStructures.PerfectHash.Bounded.Prelude

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

def roundEntry (s : State w 64) : State w 64 :=
  ⟨71,update (update (update (update (update s.regs compactBase (s.regs Construction.Registers.input))
    Registers.distinctCount (s.regs count)) roundTarget (s.regs count)) size (word w 1))
    shift (s.regs machineWidth),s.mem⟩

theorem round_entry (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .deduplicated) :
    Steps program rho 5 s (roundEntry s) [] := by
  change s.pc = 66 at hp
  apply steps_iff_run.mpr
  unfold roundEntry
  bounded_reduce

def rootSetup (s : State w 64) : State w 64 :=
  ⟨86,update (update (update (update (update (update (update (update (update (update s.regs
    buckets (s.regs size)) rootShift (s.regs shift)) directory (s.regs outputBase+word w 4))
    nodes (s.regs scratchBase)) count (s.regs Registers.distinctCount)) width (s.regs machineWidth))
    trialsLeft (s.regs machineWidth)) randomCursor (s.regs randomBase+word w 1))
    stage (word w 0)) fallbackMode (word w 0),s.mem⟩

theorem root_setup (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .rounded) :
    Steps program rho 10 s (rootSetup s) [] := by
  change s.pc = 76 at hp
  apply steps_iff_run.mpr
  unfold rootSetup
  bounded_reduce

def sampled (rho : RandomMemory w) (s : State w 64) (pc : Nat) : State w 64 :=
  ⟨pc,update (update (update (update s.regs temp (unsignedMod (rho (s.regs randomCursor)) (word w 2)))
    seed (Hashing.MultiplyShift.sample (rho (s.regs randomCursor))))
    randomCursor (s.regs randomCursor+word w 1)) trialsLeft (s.regs trialsLeft-word w 1),s.mem⟩

def sampleTrace (rho : RandomMemory w) (s : State w 64) : List (Access w) :=
  [.randomRead (s.regs randomCursor) (rho (s.regs randomCursor))]

theorem root_sample (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .rootChoose)
    (hn : s.regs trialsLeft ≠ word w 0) :
    Steps program rho 7 s (sampled rho s (location .rootTrial)) (sampleTrace rho s) := by
  change s.pc = 86 at hp
  change s.regs (32 : Reg 64) ≠ word w 0 at hn
  apply steps_iff_run.mpr
  unfold sampled sampleTrace Hashing.MultiplyShift.sample
  bounded_reduce
  funext r
  simp [update]
  split <;> simp_all [update]

theorem child_sample (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .childChoose)
    (hn : s.regs trialsLeft ≠ word w 0) :
    Steps program rho 8 s (sampled rho s (location .childTrial)) (sampleTrace rho s) := by
  change s.pc = 179 at hp
  change s.regs (32 : Reg 64) ≠ word w 0 at hn
  apply steps_iff_run.mpr
  unfold sampled sampleTrace Hashing.MultiplyShift.sample
  bounded_reduce
  funext r
  simp [update]
  split <;> simp_all [update]

theorem root_budget (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .rootChoose)
    (hn : s.regs trialsLeft = word w 0) :
    Steps program rho 1 s {s with pc := location .failed} [] := by
  change s.pc = 86 at hp
  change s.regs (32 : Reg 64) = word w 0 at hn
  apply steps_iff_run.mpr
  bounded_reduce

theorem child_budget (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .childChoose)
    (hn : s.regs trialsLeft = word w 0) :
    Steps program rho 1 s {s with pc := location .failed} [] := by
  change s.pc = 179 at hp
  change s.regs (32 : Reg 64) = word w 0 at hn
  apply steps_iff_run.mpr
  bounded_reduce

theorem failed (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .failed) :
    TerminatesIn program rho s 2 ⟨230,update s.regs status (word w 0),s.mem⟩ [] := by
  change s.pc = 229 at hp
  apply terminatesIn_iff_run.mpr
  bounded_reduce

def rootEntry (s : State w 64) : State w 64 :=
  ⟨94,update s.regs Construction.Registers.input (s.regs compactBase),s.mem⟩

theorem root_entry (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .rootTrial) :
    Steps program rho 1 s (rootEntry s) [] := by
  change s.pc = 93 at hp
  apply steps_iff_run.mpr
  unfold rootEntry
  bounded_reduce

theorem root_yes (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .rootResult)
    (hy : s.regs status = word w 1) :
    Steps program rho 1 s {s with pc := location .rootAccepted} [] := by
  change s.pc = 133 at hp
  change s.regs (18 : Reg 64) = word w 1 at hy
  apply steps_iff_run.mpr
  bounded_reduce

theorem root_no (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .rootResult)
    (hn : s.regs status ≠ word w 1) :
    Steps program rho 2 s {s with pc := location .rootChoose} [] := by
  change s.pc = 133 at hp
  change s.regs (18 : Reg 64) ≠ word w 1 at hn
  apply steps_iff_run.mpr
  bounded_reduce

def headerMemory (s : State w 64) : DataMemory w :=
  update (update (update (update s.mem (s.regs outputBase) (s.regs seed))
    (s.regs outputBase+word w 1) (s.regs rootShift))
    (s.regs outputBase+word w 2) (s.regs buckets))
    (s.regs outputBase+word w 3) (s.regs Registers.distinctCount)

def headerTrace (s : State w 64) : List (Access w) :=
  [.dataWrite (s.regs outputBase) (s.regs seed),
   .dataWrite (s.regs outputBase+word w 1) (s.regs rootShift),
   .dataWrite (s.regs outputBase+word w 2) (s.regs buckets),
   .dataWrite (s.regs outputBase+word w 3) (s.regs Registers.distinctCount)]

def afterRoot (s : State w 64) : State w 64 :=
  ⟨146,update (update (update (update s.regs temp (s.regs buckets*word w 4))
    bucketIndex (word w 0)) directoryCursor (s.regs directory))
    tableCursor (s.regs directory+s.regs buckets*word w 4),headerMemory s⟩

theorem root_header (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .rootAccepted) :
    Steps program rho 11 s (afterRoot s) (headerTrace s) := by
  change s.pc = 135 at hp
  apply steps_iff_run.mpr
  unfold afterRoot headerMemory headerTrace
  bounded_reduce
  funext r
  simp [update]
  split <;> simp_all [update] <;> split <;> simp_all <;> split <;> simp_all

def childCall (s : State w 64) : State w 64 :=
  ⟨150,update (update (update s.regs address (s.regs directoryCursor)) table (s.regs tableCursor))
    width (s.regs machineWidth),s.mem⟩

theorem child_next (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .childLoop)
    (hn : s.regs bucketIndex ≠ s.regs buckets) : Steps program rho 4 s (childCall s) [] := by
  change s.pc = 146 at hp
  change s.regs (39 : Reg 64) ≠ s.regs (22 : Reg 64) at hn
  apply steps_iff_run.mpr
  unfold childCall
  bounded_reduce

theorem child_done (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .childLoop)
    (hn : s.regs bucketIndex = s.regs buckets) :
    Steps program rho 1 s {s with pc := location .finish} [] := by
  change s.pc = 146 at hp
  change s.regs (39 : Reg 64) = s.regs (22 : Reg 64) at hn
  apply steps_iff_run.mpr
  bounded_reduce

def allocatedState (s : State w 64) (pc : Nat) : State w 64 :=
  ⟨pc,update (update (update (update (update s.regs trialsLeft (s.regs machineWidth))
    temp ((s.regs bucketIndex+word w 1)*s.regs machineWidth))
    randomCursor (s.regs randomBase+(s.regs bucketIndex+word w 1)*s.regs machineWidth+word w 1))
    stage (word w 1)) fallbackMode (word w 0),s.mem⟩

theorem allocated_direct (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .allocated)
    (hb : (s.regs childCount).toNat ≤ (word w 1).toNat) :
    Steps program rho 8 s (allocatedState s (location .directChild)) [] := by
  change s.pc = 171 at hp
  change (s.regs (28 : Reg 64)).toNat ≤ (word w 1).toNat at hb
  simp only [word_toNat] at hb
  apply steps_iff_run.mpr
  unfold allocatedState
  bounded_reduce
  funext r
  simp [update]
  split <;> simp_all [update]

theorem allocated_hashed (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .allocated)
    (hb : (word w 1).toNat < (s.regs childCount).toNat) :
    Steps program rho 8 s (allocatedState s (location .childChoose)) [] := by
  change s.pc = 171 at hp
  change (word w 1).toNat < (s.regs (28 : Reg 64)).toNat at hb
  simp only [word_toNat] at hb
  have hn := Nat.not_le.mpr hb
  apply steps_iff_run.mpr
  unfold allocatedState
  bounded_reduce
  funext r
  simp [update]
  split <;> simp_all [update]

def directState (s : State w 64) : State w 64 :=
  ⟨188,update s.regs seed (word w 1),s.mem⟩

theorem direct_child (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .directChild) :
    Steps program rho 1 s (directState s) [] := by
  change s.pc = 187 at hp
  apply steps_iff_run.mpr
  unfold directState
  bounded_reduce

def childSuccess (s : State w 64) : State w 64 :=
  ⟨146,update (update (update (update s.regs temp (s.regs directoryCursor+word w 1))
    tableCursor (s.regs tableEnd)) directoryCursor (s.regs directoryCursor+word w 4))
    bucketIndex (s.regs bucketIndex+word w 1),
    update s.mem (s.regs directoryCursor+word w 1) (s.regs seed)⟩

theorem child_yes (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .childResult)
    (hn : s.regs status ≠ word w 0) :
    Steps program rho 7 s (childSuccess s) [.dataWrite (s.regs directoryCursor+word w 1) (s.regs seed)] := by
  change s.pc = 217 at hp
  change s.regs (18 : Reg 64) ≠ word w 0 at hn
  apply steps_iff_run.mpr
  unfold childSuccess
  bounded_reduce

theorem child_no (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .childResult)
    (hn : s.regs status = word w 0) :
    Steps program rho 1 s {s with pc := location .childChoose} [] := by
  change s.pc = 217 at hp
  change s.regs (18 : Reg 64) = word w 0 at hn
  apply steps_iff_run.mpr
  bounded_reduce

def finished (s : State w 64) : State w 64 :=
  ⟨228,update (update (update (update s.regs Construction.Registers.input (s.regs outputBase))
    count (s.regs tableCursor-s.regs outputBase)) directory (s.regs Registers.distinctCount))
    status (word w 1),s.mem⟩

theorem finish (s : State w 64) (rho : RandomMemory w) (hp : s.pc = location .finish) :
    TerminatesIn program rho s 5 (finished s) [] := by
  change s.pc = 224 at hp
  apply terminatesIn_iff_run.mpr
  unfold finished
  bounded_reduce

end PerfectHash.Bounded
