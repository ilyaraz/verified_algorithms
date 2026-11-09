import DataStructures.PerfectHash.Source.Total.EnumerationLoop

namespace PerfectHash.Source.Search.Root
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Construction
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Capped random trials followed by exhaustive deterministic search return the
first successful seed, charge both phases, and use only the random prefix. -/
theorem total_contract {w free input dir nodes m start total H : Nat}
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
    (hrandom : (Region.mk start total).Fits w)
    (fallback : Word w)
    (hf : RamLang.Library.Search.choice (PerfectHash.Total.candidate w) (accept hash keys) 0 H = some fallback) :
    Contract p rho free Total.rootFunction.body
      ([word w input,word w keys.length,word w dir,word w nodes,word w m,shift,word w start,word w total].map some ++ List.replicate Total.rootFunction.locals.length none) mem
      (fun flow mem' log => let value := (RamLang.Library.Search.choice (sample rho) (accept hash keys) start total).getD fallback
        flow = .returned value ∧ Grouped (hash value) dir nodes keys.reverse mem' ∧ ArrayAt mem' input keys ∧
        (policy input keys.length dir nodes m start total).AllowsTrace log ∧ RamLang.Library.Retry.randomAddresses log =
          RamLang.Library.Retry.addresses w start (RamLang.Library.Search.attempts (sample rho) (accept hash keys) start total))
      ((300*(keys.length+m+1)+155)*(RamLang.Library.Search.attempts (sample rho) (accept hash keys) start total + if (RamLang.Library.Search.choice (sample rho) (accept hash keys) start total).isNone then H else 0)+40) 34 := by
  have hone : 1 < modulus w := by omega
  obtain ⟨flow,mem',log,d,⟨hresult,hp,hr⟩,ht,hs⟩ := prefix_contract p rho mem hash shift keys hsample hroot hfill hfree hspace hlinear hinput hhash hfit hdir hnodes hrandom
  cases he : RamLang.Library.Search.choice (sample rho) (accept hash keys) start total with
  | none =>
    simp only [RamLang.Library.Search.Post,he,PrefixInvariant] at hresult
    obtain ⟨out,rfl,_,_,ha,seed,accepted,hout⟩ := hresult
    subst out
    obtain ⟨flow,mem'',log',de,⟨rfl,⟨hgood,ha'⟩,hp',hr'⟩,ht',hs'⟩ :=
      enumeration_contract (start := start) (total := total) (c := start+total) (n := 0) p rho mem' hash shift keys accepted fallback hroot hfill hfree hspace hlinear ha hhash hfit hdir hnodes hone hf
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simp only [he,Option.getD_none,Option.toList_none,List.nil_append,List.append_nil]
      refine ⟨trivial,hgood,ha', (AccessPolicy.allowsTrace_append _).mpr ⟨hp,hp'⟩,?_⟩
      rw [RamLang.Library.Retry.randomAddresses_append,hr,hr',List.append_nil]
    · ram_cost
      simp only [he,Option.isNone_none,↓reduceIte,Nat.mul_add,Nat.add_assoc,Nat.reduceAdd] at ht ht' ⊢
      nlinarith
    · ram_cost
      exact ⟨hs,hs'⟩
  | some value =>
    simp only [RamLang.Library.Search.Post,he] at hresult
    obtain ⟨rfl,hgood,ha⟩ := hresult
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simpa [he] using And.intro hgood (And.intro ha (And.intro hp hr))
    · ram_cost
      simp only [he,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd] at ht ⊢
      omega
    · ram_cost
      exact hs

end PerfectHash.Source.Search.Root

namespace PerfectHash.Source.Search.Child
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Construction
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Capped random trials followed by exhaustive deterministic search return the
first successful seed, charge both phases, and use only the random prefix. -/
theorem total_contract {w free nodes N table q start total H : Nat}
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
    (hrandom : (Region.mk start total).Fits w)
    (fallback : Word w)
    (hf : RamLang.Library.Search.choice (PerfectHash.Total.candidate w) (accept hash chain) 0 H = some fallback) :
    Contract p rho free Total.childFunction.body
      ([word w nodes,word w (Dedup.firstIndex chain),word w table,word w q,shift,word w start,word w total].map some ++ List.replicate Total.childFunction.locals.length none) mem
      (fun flow mem' log => let value := (RamLang.Library.Search.choice (Root.sample rho) (accept hash chain) start total).getD fallback
        flow = .returned value ∧ SlotsAt (hash value) q table (chain.map Prod.fst).reverse mem' ∧ Dedup.ChainAt mem' nodes chain ∧
        (policy nodes N table q start total).AllowsTrace log ∧ RamLang.Library.Retry.randomAddresses log =
          RamLang.Library.Retry.addresses w start (RamLang.Library.Search.attempts (Root.sample rho) (accept hash chain) start total))
      ((200*(q+chain.length+1)+155)*(RamLang.Library.Search.attempts (Root.sample rho) (accept hash chain) start total + if (RamLang.Library.Search.choice (Root.sample rho) (accept hash chain) start total).isNone then H else 0)+40) 26 := by
  have hqfit : q < modulus w := by have hf : table+2*q < modulus w := htable; omega
  have hone : 1 < modulus w := by omega
  have hzero : word w q ≠ word w 0 := by
    intro he
    have := (word_eq_iff_of_lt hqfit (by omega : 0 < modulus w)).mp he
    omega
  have hqMod : q % modulus w = q := Nat.mod_eq_of_lt hqfit
  have hOneMod : 1 % modulus w = 1 := Nat.mod_eq_of_lt hone
  obtain ⟨flow,mem',log,d,⟨hresult,hp,hr⟩,ht,hs⟩ := prefix_contract p rho mem hash shift chain hsample hchild hfill hfree hchain hb hh hhash hnode htable hsep hq hrandom
  cases he : RamLang.Library.Search.choice (Root.sample rho) (accept hash chain) start total with
  | none =>
    simp only [RamLang.Library.Search.Post,he,PrefixInvariant] at hresult
    obtain ⟨out,rfl,_,_,ha,seed,accepted,hout⟩ := hresult
    subst out
    obtain ⟨flow,mem'',log',de,⟨rfl,⟨hgood,ha'⟩,hp',hr'⟩,ht',hs'⟩ :=
      enumeration_contract (start := start) (total := total) (c := start+total) (n := 0) p rho mem' hash shift chain accepted fallback hchild hfill hfree ha hb hh hhash hnode htable hsep hone hf
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simp only [he,Option.getD_none,Option.toList_none,List.nil_append,List.append_nil]
      refine ⟨trivial,hgood,ha', (AccessPolicy.allowsTrace_append _).mpr ⟨hp,hp'⟩,?_⟩
      rw [RamLang.Library.Retry.randomAddresses_append,hr,hr',List.append_nil]
    · ram_cost
      simp only [he,Option.isNone_none,↓reduceIte,Nat.mul_add,Nat.add_assoc,Nat.reduceAdd] at ht ht' ⊢
      nlinarith
    · ram_cost
      exact ⟨hs,hs'⟩
  | some value =>
    simp only [RamLang.Library.Search.Post,he] at hresult
    obtain ⟨rfl,hgood,ha⟩ := hresult
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simpa [he] using And.intro hgood (And.intro ha (And.intro hp hr))
    · ram_cost
      simp only [he,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd] at ht ⊢
      omega
    · ram_cost
      exact hs

/-- Empty children return the conventional seed one without touching ordinary
or random memory. There are no zero-length hash-range assumptions. -/
theorem total_empty_contract {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (nodes cursor table shift address tries : Word w) :
    Contract p rho free Total.childFunction.body
      ([nodes,cursor,table,word w 0,shift,address,tries].map some ++ List.replicate Total.childFunction.locals.length none) mem
      (fun flow mem' log => flow = .returned (word w 1) ∧ mem' = mem ∧ log = []) 11 0 := by
  refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
  · exact ⟨rfl,rfl,rfl⟩
  · ram_cost
  · ram_cost

/-- A singleton's direct seed is executed by the ordinary child helper. Its
slot invariant is the same one used by hashed children, with no random read. -/
theorem total_singleton_contract {w free nodes N table : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Nat) (shift address tries : Word w) (chain : List (Word w × Nat))
    (hchild : p.functions[7]? = some Source.Child.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 26 ≤ free)
    (hchain : Dedup.ChainAt mem nodes chain) (hb : ∀ item ∈ chain, 0 < item.2 ∧ item.2 ≤ N)
    (hh : ∀ key, hash key < 1)
    (hhash : ∀ key, unsignedShiftRight (word w 1*key) shift = word w (hash key))
    (hnode : (Region.mk nodes (2*N)).Fits w) (htable : (Region.mk table 2).Fits w)
    (hsep : (Region.mk nodes (2*N)).Separated ⟨table,2⟩)
    (haccept : childAccepted hash [] (chain.map Prod.fst) = true) :
    Contract p rho free Total.childFunction.body
      ([word w nodes,word w (Dedup.firstIndex chain),word w table,word w 1,shift,address,tries].map some ++
        List.replicate Total.childFunction.locals.length none) mem
      (fun flow mem' log => flow = .returned (word w 1) ∧
        SlotsAt hash 1 table (chain.map Prod.fst).reverse mem' ∧ Dedup.ChainAt mem' nodes chain ∧
        (Source.Child.policy nodes N table 1).AllowsTrace log ∧ RamLang.Library.Retry.randomAddresses log = [])
      (200*(chain.length+2)+60) 26 := by
  obtain ⟨flow,mem',log,child,⟨hf,hs,hp⟩,ht,hpeak⟩ := Source.Child.contract (free := free-21)
    p rho mem hash (word w 1) shift chain hfill (by omega) hchain hb hh hhash hnode htable hsep
  simp only [haccept,↓reduceIte] at hf
  subst flow
  have hslots := hs haccept
  have hchain' := hchain.frame hb hnode (fun a ha =>
    (child.frame_of_policy hp (Region.not_contains_of_separated hsep ha)).symm)
  have hr : RamLang.Library.Retry.randomAddresses log = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro e he
    have hh := hp e he
    cases e <;> simp_all [Source.Child.policy,AccessPolicy.Allows,Access.randomAddress]
  have hone : 1 < modulus w := by have ht : table+2 < modulus w := htable; omega
  have hne : word w 1 ≠ word w 0 := by
    intro he
    have := (word_eq_iff_of_lt hone (by omega : 0 < modulus w)).mp he
    omega
  have hchildSpace : 21 ≤ free := by omega
  refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
  · simpa using And.intro hslots (And.intro hchain' (And.intro hp hr))
  · ram_cost
    omega
  · ram_cost
    change 21+extraStack child ≤ 26
    omega

end PerfectHash.Source.Search.Child
