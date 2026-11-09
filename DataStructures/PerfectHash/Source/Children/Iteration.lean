import DataStructures.PerfectHash.Source.Children.Memory

namespace PerfectHash.Source.Children
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Ten scratch slots retain arbitrary values at child-loop boundaries. -/
abbrev Scratch (w : Nat) := Fin 10 → Option (Word w)

/-- The caller keeps the current directory/table cursors and remaining count;
all expression temporaries are charged fixed local slots. -/
def locals (xs : List (Word w)) (l : Layout) (a : Word w) (j remaining : Nat) (old : Scratch w) : Locals w :=
  [some (word w (l.outputBase+4+4*j)),some (word w l.scratchBase),some (word w remaining),
   some (word w (childRandomBase l w j)),some (word w w),some (word w (tableCursorAt xs l a j)),
   old 0,old 1,old 2,old 3,old 4,old 5,old 6,old 7,old 8,old 9]

/-- One complete outer iteration calls allocation and search, then installs the
accepted seed. Failure returns normally before consuming another random block. -/
theorem iteration_contract {w free : Nat} {p : RamLang.Program} {rho : RandomMemory w}
    {xs : List (Word w)} {l : Layout} {a : Word w} {f : RamLang.Function}
    {choice : Fin (rootSlots xs) → Option (Word w)} {cost : Fin (rootSlots xs) → Nat}
    (ha : Admissible w xs.length l) (spec : SearchSpec p rho xs l a f choice cost)
    (hround : p.functions[1]? = some Hashing.Source.Rounding.function)
    (hallocate : p.functions[8]? = some Source.Allocation.function)
    (hfree : 40 ≤ free) (b : Fin (rootSlots xs)) (mem : DataMemory w)
    (hpartial : Partial xs l a b.val mem) (old : Scratch w) :
    Contract p rho free iteration (locals xs l a b.val (rootSlots xs-b.val) old) mem
      (fun flow mem' log => (Source.policy w xs.length l).AllowsTrace log ∧
        (RamLang.Library.Retry.randomAddresses log).Sublist (consecutiveAddresses w (childRandomBase l w b.val) w) ∧
        match choice b with
        | none => flow = .returned (word w 0)
        | some _ => ∃ saved, flow = .next (locals xs l a (b.val+1) (rootSlots xs-(b.val+1)) saved) ∧
            Partial xs l a (b.val+1) mem') (work xs a cost b-5) 40 := by
  let dir := Packed.directory l.outputBase b
  let table := Packed.table l.outputBase (childCapacity xs a) b
  let q := childCapacity xs a b
  let count := bucketCount xs a b
  let allocated := Source.Allocation.memory mem dir table count
  let allocLog := Source.Allocation.trace w dir table count
  let next := table+2*q
  have hd : (Region.mk dir 4).Fits w := directory_fit ha b
  have ht : (Region.mk table (2*q)).Fits w := (childContext ha hpartial.accepted b).table_fit
  have hc : count < modulus w := (bucket_fit ha hpartial.accepted b).1
  have hcount : mem (word w dir) = word w count := hpartial.counts b
  obtain ⟨flow,mem₁,log₁,allocate,⟨hf,hm,hl⟩,ht₁,hp₁⟩ :=
    Source.Allocation.contract (free := free-14) p rho mem dir table count hround (by omega) hc hd ht hcount
  subst flow
  subst mem₁
  subst log₁
  have hallocPart : Partial xs l a b.val allocated := allocated_partial ha hpartial
  have hfields := Source.Allocation.memory_fields mem dir table count hd
  have hhead : allocated (word w (dir+1)) = word w (Dedup.firstIndex (bucketChain xs a b)) :=
    hfields.2.1.trans (hpartial.heads b (Nat.le_refl _))
  have hshift : allocated (word w (dir+2)) = word w (Source.Allocation.shift w count) := hfields.2.2.1
  have htable : allocated (word w (dir+3)) = word w table := hfields.2.2.2
  have hnext : next = tableCursorAt xs l a (b.val+1) := (cursor_next xs l a b).symm
  have htableNat : table < modulus w := by have ht' : table+2*q < modulus w := ht; omega
  have hqNat : 2*q < modulus w := by have ht' : table+2*q < modulus w := ht; omega
  have hone : 1 < modulus w := by have hh := ha.arithmetic.linearSizes; omega
  have hslots : unsignedShiftRight (word w next-word w table) (word w 1) = word w q := by
    rw [WordRam.word_sub next table htableNat (by dsimp [next]; omega)]
    simp only [next,Nat.add_sub_cancel_left,unsignedShiftRight,word_toNat_of_lt hqNat,
      word_toNat_of_lt hone,Nat.shiftRight_eq_div_pow]
    congr 1
    omega
  have hsearchFree : 26 ≤ free-f.frameSize := by have hh := spec.frame; omega
  have hsearch := spec.body (free-f.frameSize) allocated b hsearchFree (hallocPart.chains b)
  have hsearch' : Contract p rho (free-f.frameSize) f.body
      ([word w l.scratchBase,allocated (word w dir+word w 1),word w table,
        unsignedShiftRight (word w next-word w table) (word w 1),allocated (word w dir+word w 2),
        word w (childRandomBase l w b.val),word w w].map some ++ List.replicate f.locals.length none) allocated
      (fun flow mem' log => flow = .returned ((choice b).getD (word w 0)) ∧
        (∀ seed, choice b = some seed → childAccepted xs a b seed = true ∧
          Construction.SlotsAt (childHash w count seed) q table (bucketKeys xs a b).reverse mem') ∧
        (Source.Search.Child.policy l.scratchBase (values xs).length table q (childRandomBase l w b.val) w).AllowsTrace log ∧
        (RamLang.Library.Retry.randomAddresses log).Sublist (consecutiveAddresses w (childRandomBase l w b.val) w))
      (cost b) 26 := by
    simpa only [WordRam.word_add,hhead,hshift,hslots] using hsearch
  obtain ⟨flow,mem₂,log₂,search,⟨hf₂,hgood,hp₂,hr₂⟩,ht₂,hs₂⟩ := hsearch'
  subst flow
  have hpart₂ := searched_partial ha hallocPart search hp₂
  have hfieldFrame (i : Nat) (hi : i < 4) : mem₂ (word w (dir+i)) = allocated (word w (dir+i)) :=
    search.frame_of_policy hp₂ (Region.not_contains_of_separated (Packed.directory_table_separated _ _ b b)
      (Region.contains_index hd hi))
  have hpol₁ := allocation_policy (a := a) ha b
  have hpol₂ := search_policy ha hpartial.accepted b hp₂
  have hread₁ : (Source.policy w xs.length l).read (word w (dir+1)) := Or.inr (Or.inl (directory_inside ha b (by decide : 1 < 4)))
  have hread₂ : (Source.policy w xs.length l).read (word w (dir+2)) := Or.inr (Or.inl (directory_inside ha b (by decide : 2 < 4)))
  have hlookup := spec.lookup
  have hparams := spec.parameters
  have hframe : f.frameSize ≤ free := by have hh := spec.frame; omega
  have hallocateSpace : 14 ≤ free := by omega
  cases he : choice b with
  | none =>
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · refine ⟨?_,?_,rfl⟩
      · intro e hevent
        simp only [Option.toList_none,Option.toList_some,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or] at hevent
        rcases hevent with hevent | rfl | rfl | hevent
        · exact hpol₁ e hevent
        · simpa only [AccessPolicy.Allows,Binary.eval,WordRam.word_add] using hread₁
        · simpa only [AccessPolicy.Allows,Binary.eval,WordRam.word_add] using hread₂
        · exact hpol₂ e hevent
      · simpa [RamLang.Library.Retry.randomAddresses_append,Source.Allocation.trace,
          RamLang.Library.Retry.randomAddresses,Access.randomAddress] using hr₂
    · ram_cost
      unfold work
      dsimp only [count] at ht₁
      omega
    · ram_cost
      change 14+extraStack allocate ≤ 40 ∧ f.frameSize+extraStack search ≤ 40
      have hh := spec.frame
      omega
  | some seed =>
    have hnonzero := spec.nonzero b seed he
    have hgood' := hgood seed he
    have hcomplete := completed_partial ha hpart₂ hgood'.1
      ((hfieldFrame 2 (by decide)).trans hshift) ((hfieldFrame 3 (by decide)).trans htable) hgood'.2
    have hremain : word w (rootSlots xs-b.val)-word w 1 = word w (rootSlots xs-(b.val+1)) := by
      rw [WordRam.word_sub _ 1 hone (by have hb := b.isLt; omega)]
      congr 1
    have haddress : word w (childRandomBase l w b.val)+word w w = word w (childRandomBase l w (b.val+1)) := by
      rw [WordRam.word_add]
      congr 1
      unfold childRandomBase
      ring
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · refine ⟨?_,?_,?_⟩
      · intro e hevent
        simp only [Option.toList_none,Option.toList_some,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or] at hevent
        rcases hevent with hevent | rfl | rfl | hevent | rfl
        · exact hpol₁ e hevent
        · simpa only [AccessPolicy.Allows,Binary.eval,WordRam.word_add] using hread₁
        · simpa only [AccessPolicy.Allows,Binary.eval,WordRam.word_add] using hread₂
        · exact hpol₂ e hevent
        · apply Or.inl
          simpa only [Binary.eval,WordRam.word_add] using directory_inside ha b (by decide : 1 < 4)
      · simpa [RamLang.Library.Retry.randomAddresses_append,Source.Allocation.trace,
          RamLang.Library.Retry.randomAddresses,Access.randomAddress] using hr₂
      · have hslotsRaw : unsignedShiftRight
            (word w (table+2*Sizes.childSlots count)-word w (tableCursorAt xs l a b.val)) (word w 1) = word w q := hslots
        have hnextRaw : word w (table+2*Sizes.childSlots count) = word w (tableCursorAt xs l a (b.val+1)) := congrArg (word w) hnext
        have hdirNext : word w (l.outputBase+4+4*b.val)+word w 4 = word w (l.outputBase+4+4*(b.val+1)) := by
          rw [WordRam.word_add]
          congr 1
        simp only [he,Option.getD_some,Binary.eval,hslotsRaw,hnextRaw,hremain,haddress,hdirNext]
        exact ⟨![_,_,_,_,_,_,_,_,_,_],rfl,by simpa only [WordRam.word_add] using hcomplete⟩
    · ram_cost
      unfold work
      dsimp only [count] at ht₁
      omega
    · ram_cost
      change 14+extraStack allocate ≤ 40 ∧ f.frameSize+extraStack search ≤ 40
      have hh := spec.frame
      omega

end PerfectHash.Source.Children
