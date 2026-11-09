import DataStructures.PerfectHash.Source.Search.Child

namespace PerfectHash.Source.Search.Root
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Construction
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Live parameters and preserved input at a capped-search boundary. -/
def PrefixInvariant (input N dir nodes m start total : Nat) (shift : Word w) (keys : List (Word w))
    (c n : Nat) (ls : Locals w) (memory : DataMemory w) : Prop :=
    start ≤ c ∧ c+n ≤ start+total ∧ ArrayAt memory input keys ∧
      ∃ oldSeed oldAccepted, ls = locals input keys.length dir nodes m shift c n oldSeed oldAccepted

/-- The capped phase exposes its failure state so a verified continuation can enumerate seeds. -/
theorem prefix_contract {w free input dir nodes m start total : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Word w → Fin m) (shift : Word w) (keys : List (Word w))
    (hsample : p.functions[3]? = some Hashing.Source.Sampling.function)
    (hroot : p.functions[6]? = some Source.Root.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 34 ≤ free)
    (hspace : GroupSpace w m keys.length dir nodes) (hlinear : 64*(keys.length+1) < modulus w)
    (hinput : ArrayAt mem input keys)
    (hhash : ∀ seed key, unsignedShiftRight (seed*key) shift = word w (hash seed key).val)
    (hfit : (Region.mk input keys.length).Fits w)
    (hdir : (Region.mk input keys.length).Separated ⟨dir,4*m⟩)
    (hnodes : (Region.mk input keys.length).Separated ⟨nodes,2*keys.length⟩)
    (hrandom : (Region.mk start total).Fits w) :
    Contract p rho free loop (locals input keys.length dir nodes m shift start total none none) mem
      (fun flow mem' log =>
        RamLang.Library.Search.Post (sample rho) (accept hash keys) (PrefixInvariant input keys.length dir nodes m start total shift keys)
          (fun seed memory => Grouped (hash seed) dir nodes keys.reverse memory ∧ ArrayAt memory input keys) start total flow mem' ∧
        (policy input keys.length dir nodes m start total).AllowsTrace log ∧
        RamLang.Library.Retry.randomAddresses log = RamLang.Library.Retry.addresses w start
          (RamLang.Library.Search.attempts (sample rho) (accept hash keys) start total))
      ((300*(keys.length+m+1)+150+5)*RamLang.Library.Search.attempts (sample rho) (accept hash keys) start total+5) 34 := by
  let I := PrefixInvariant input keys.length dir nodes m start total shift keys
  have counterValue : ∀ c n ls memory, I c n ls memory →
      (.local 7 : Atom).eval ls = .ok (word w n) ∧ n < modulus w := by
    rintro c n ls memory ⟨hc,hn,ha,seed,accepted,rfl⟩
    refine ⟨rfl,?_⟩
    have hr : start+total < modulus w := hrandom
    omega
  have trial : ∀ c n ls memory, I c (n+1) ls memory →
      Contract p rho free iteration ls memory
        (fun flow mem' log => (policy input keys.length dir nodes m start total).AllowsTrace log ∧
          RamLang.Library.Retry.randomAddresses log = [word w c] ∧
          if accept hash keys (sample rho c) then
            flow = .returned (sample rho c) ∧ Grouped (hash (sample rho c)) dir nodes keys.reverse mem' ∧ ArrayAt mem' input keys
          else ∃ out, flow = .next out ∧ I (c+1) n out mem') (300*(keys.length+m+1)+150) 34 := by
    rintro c n ls memory ⟨hc,hn,ha,seed,accepted,rfl⟩
    apply (iteration_contract p rho memory hash shift keys seed accepted hsample hroot hfill hfree
      hspace hlinear ha hhash hfit hdir hnodes hrandom hc (by omega)).consequence (work' := 300*(keys.length+m+1)+150) (peak' := 34)
    · rintro flow mem' log ⟨hp,hr,ha',hq⟩
      refine ⟨hp,hr,?_⟩
      cases hy : accept hash keys (sample rho c) with
      | true => simpa [hy,and_assoc] using And.intro hq ha'
      | false =>
        simp only [hy,Bool.false_eq_true,↓reduceIte] at hq ⊢
        exact ⟨_,hq,by dsimp [I,PrefixInvariant]; exact ⟨by omega,by omega,ha',_,_,rfl⟩⟩
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  have hi : I start total (locals input keys.length dir nodes m shift start total none none) mem :=
    ⟨Nat.le_refl _,Nat.le_refl _,hinput,none,none,rfl⟩
  exact
    RamLang.Library.Search.loop_contract 7 iteration (sample rho) (accept hash keys) I
      (fun seed memory => Grouped (hash seed) dir nodes keys.reverse memory ∧ ArrayAt memory input keys)
      (policy input keys.length dir nodes m start total) (300*(keys.length+m+1)+150) 34
      counterValue trial start total _ mem hi

end PerfectHash.Source.Search.Root

namespace PerfectHash.Source.Search.Child
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Construction
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Live parameters and preserved input at a capped-search boundary. -/
def PrefixInvariant (nodes N table q start total : Nat) (shift : Word w) (chain : List (Word w × Nat))
    (c n : Nat) (ls : Locals w) (memory : DataMemory w) : Prop :=
    start ≤ c ∧ c+n ≤ start+total ∧ Dedup.ChainAt memory nodes chain ∧
      ∃ oldSeed oldAccepted, ls = locals nodes (Dedup.firstIndex chain) table q shift c n oldSeed oldAccepted

/-- The capped phase exposes its failure state so a verified continuation can enumerate seeds. -/
theorem prefix_contract {w free nodes N table q start total : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Word w → Nat) (shift : Word w) (chain : List (Word w × Nat))
    (hsample : p.functions[3]? = some Hashing.Source.Sampling.function)
    (hchild : p.functions[7]? = some Source.Child.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 26 ≤ free)
    (hchain : Dedup.ChainAt mem nodes chain) (hb : ∀ item ∈ chain, 0 < item.2 ∧ item.2 ≤ N)
    (hh : ∀ seed key, hash seed key < q)
    (hhash : ∀ seed key, unsignedShiftRight (seed*key) shift = word w (hash seed key))
    (hnode : (Region.mk nodes (2*N)).Fits w) (htable : (Region.mk table (2*q)).Fits w)
    (hsep : (Region.mk nodes (2*N)).Separated ⟨table,2*q⟩)
    (hq : 1 < q)
    (hrandom : (Region.mk start total).Fits w) :
    Contract p rho free loop (locals nodes (Dedup.firstIndex chain) table q shift start total none none) mem
      (fun flow mem' log =>
        RamLang.Library.Search.Post (Root.sample rho) (accept hash chain) (PrefixInvariant nodes N table q start total shift chain)
          (fun seed memory => SlotsAt (hash seed) q table (chain.map Prod.fst).reverse memory ∧ Dedup.ChainAt memory nodes chain) start total flow mem' ∧
        (policy nodes N table q start total).AllowsTrace log ∧
        RamLang.Library.Retry.randomAddresses log = RamLang.Library.Retry.addresses w start
          (RamLang.Library.Search.attempts (Root.sample rho) (accept hash chain) start total))
      ((200*(q+chain.length+1)+150+5)*RamLang.Library.Search.attempts (Root.sample rho) (accept hash chain) start total+5) 26 := by
  let I := PrefixInvariant nodes N table q start total shift chain
  have counterValue : ∀ c n ls memory, I c n ls memory →
      (.local 6 : Atom).eval ls = .ok (word w n) ∧ n < modulus w := by
    rintro c n ls memory ⟨hc,hn,ha,seed,accepted,rfl⟩
    refine ⟨rfl,?_⟩
    have hr : start+total < modulus w := hrandom
    omega
  have trial : ∀ c n ls memory, I c (n+1) ls memory →
      Contract p rho free iteration ls memory
        (fun flow mem' log => (policy nodes N table q start total).AllowsTrace log ∧
          RamLang.Library.Retry.randomAddresses log = [word w c] ∧
          if accept hash chain (Root.sample rho c) then
            flow = .returned (Root.sample rho c) ∧ SlotsAt (hash (Root.sample rho c)) q table (chain.map Prod.fst).reverse mem' ∧ Dedup.ChainAt mem' nodes chain
          else ∃ out, flow = .next out ∧ I (c+1) n out mem') (200*(q+chain.length+1)+150) 26 := by
    rintro c n ls memory ⟨hc,hn,ha,seed,accepted,rfl⟩
    apply (iteration_contract p rho memory hash shift chain seed accepted hsample hchild hfill hfree
      ha hb hh hhash hnode htable hsep hrandom hc (by omega)).consequence (work' := 200*(q+chain.length+1)+150) (peak' := 26)
    · rintro flow mem' log ⟨hp,hr,ha',hq⟩
      refine ⟨hp,hr,?_⟩
      cases hy : accept hash chain (Root.sample rho c) with
      | true => simpa [hy,and_assoc] using And.intro hq ha'
      | false =>
        simp only [hy,Bool.false_eq_true,↓reduceIte] at hq ⊢
        exact ⟨_,hq,by dsimp [I,PrefixInvariant]; exact ⟨by omega,by omega,ha',_,_,rfl⟩⟩
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  have hi : I start total (locals nodes (Dedup.firstIndex chain) table q shift start total none none) mem :=
    ⟨Nat.le_refl _,Nat.le_refl _,hchain,none,none,rfl⟩
  exact
    RamLang.Library.Search.loop_contract 6 iteration (Root.sample rho) (accept hash chain) I
      (fun seed memory => SlotsAt (hash seed) q table (chain.map Prod.fst).reverse memory ∧ Dedup.ChainAt memory nodes chain)
      (policy nodes N table q start total) (200*(q+chain.length+1)+150) 26
      counterValue trial start total _ mem hi

end PerfectHash.Source.Search.Child
