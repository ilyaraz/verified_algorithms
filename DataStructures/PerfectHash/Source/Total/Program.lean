import DataStructures.PerfectHash.Source.Bounded.Program

namespace PerfectHash.Source.Total
open WordRam RamLang RamLang.Compiler
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- The successful constructor extends the capped searches with ordinary odd
seed enumeration. Candidate updates, trials and control flow are all charged;
no fallback seed array, additional runtime budget or oracle is supplied. -/
def source : RamLang.Program := ram_program unused {
  fn unused() { return 0; }
  fn round(target, width, shiftCell) {
    let size = 1;
    while (size < target) {
      size = size + size;
      width = width - 1;
    }
    store(shiftCell, width);
    return size;
  }
  fn fill(p, n, value) {
    while (n != 0) { store(p, value); p = p + 1; n = n - 1; }
    return 0;
  }
  fn sample_seed(address) {
    let raw = random(address);
    return raw - raw % 2 + 1;
  }
  fn find_key(nodes, cursor, key) {
    let pointer;
    let loaded;
    while (cursor != 0) {
      pointer = nodes + 2 * (cursor - 1);
      loaded = load(pointer);
      if (loaded == key) { return 1; }
      cursor = load(pointer + 1);
    }
    return 0;
  }
  fn deduplicate(input, count, scratch, buckets, seed, shift) {
    let nodes = scratch + 2 * (count + 1);
    let compact = nodes + 2 * count;
    let distinct = 0;
    fill(scratch, buckets, 0);
    while (count != 0) {
      let key = load(input);
      let bucket = (seed * key) >> shift;
      let headCell = scratch + bucket;
      let head = load(headCell);
      let found = find_key(nodes, head, key);
      if (found == 0) {
        let node = nodes + 2 * distinct;
        store(node, key);
        store(node + 1, head);
        store(compact + distinct, key);
        store(headCell, distinct + 1);
        distinct = distinct + 1;
      }
      input = input + 1;
      count = count - 1;
    }
    return distinct;
  }
  fn root(input, count, directory, nodes, buckets, seed, shift) {
    let distinct = 0;
    let budget = 6 * count;
    fill(directory, 4 * buckets, 0);
    while (count != 0) {
      let key = load(input);
      let bucket = (seed * key) >> shift;
      let entry = directory + 4 * bucket;
      let oldCount = load(entry);
      let increment = 2 * oldCount + 1;
      if (budget < increment) { return 0; }
      budget = budget - increment;
      let head = load(entry + 1);
      let node = nodes + 2 * distinct;
      store(node, key);
      store(node + 1, head);
      store(entry + 1, distinct + 1);
      store(entry, oldCount + 1);
      distinct = distinct + 1;
      input = input + 1;
      count = count - 1;
    }
    return 1;
  }
  fn child(nodes, cursor, table, slots, seed, shift) {
    fill(table, 2 * slots, 0);
    while (cursor != 0) {
      let node = nodes + 2 * (cursor - 1);
      let key = load(node);
      let index = (seed * key) >> shift;
      let slot = table + 2 * index;
      let occupied = load(slot);
      if (occupied != 0) { return 0; }
      store(slot, 1);
      store(slot + 1, key);
      cursor = load(node + 1);
    }
    return 1;
  }
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
  fn root_search(input, count, directory, nodes, buckets, shift, address, tries) {
    let seed;
    let accepted;
    while (tries != 0) {
      seed = sample_seed(address);
      accepted = root(input, count, directory, nodes, buckets, seed, shift);
      if (accepted != 0) { return seed; }
      address = address + 1;
      tries = tries - 1;
    }
    seed = 1;
    while (1 != 0) {
      accepted = root(input, count, directory, nodes, buckets, seed, shift);
      if (accepted != 0) { return seed; }
      seed = seed + 2;
    }
    return 0;
  }
  fn child_search(nodes, cursor, table, slots, shift, address, tries) {
    if (slots == 0) { return 1; }
    if (slots <= 1) {
      child(nodes, cursor, table, slots, 1, shift);
      return 1;
    }
    let seed;
    let accepted;
    while (tries != 0) {
      seed = sample_seed(address);
      accepted = child(nodes, cursor, table, slots, seed, shift);
      if (accepted != 0) { return seed; }
      address = address + 1;
      tries = tries - 1;
    }
    seed = 1;
    while (1 != 0) {
      accepted = child(nodes, cursor, table, slots, seed, shift);
      if (accepted != 0) { return seed; }
      seed = seed + 2;
    }
    return 0;
  }
  fn children(directory, nodes, buckets, address, width) {
    let table = directory + 4 * buckets;
    while (buckets != 0) {
      let nextTable = allocate(directory, table, width);
      let slots = (nextTable - table) >> 1;
      let cursor = load(directory + 1);
      let shift = load(directory + 2);
      let seed = child_search(nodes, cursor, table, slots, shift, address, width);
      if (seed == 0) { return 0; }
      store(directory + 1, seed);
      table = nextTable;
      directory = directory + 4;
      address = address + width;
      buckets = buckets - 1;
    }
    return table;
  }
  fn construct(input, count, output, outputCapacity, scratch, scratchCapacity, randomBase, randomCapacity, width) {
    if (count == 0) { return empty(output, width); }
    let distinct = prepare(input, count, output, scratch, randomBase, width);
    let compact = scratch + 4 * count + 2;
    let buckets = round(distinct, width, output + 1);
    let shift = load(output + 1);
    let seed = root_search(compact, distinct, output + 4, scratch, buckets, shift, randomBase + 1, width);
    if (seed == 0) { return 0; }
    store(output, seed);
    store(output + 1, shift);
    store(output + 2, buckets);
    store(output + 3, distinct);
    return children(output + 4, scratch, buckets, randomBase + 1 + width, width);
  }
  fn prepare(input, count, output, scratch, randomBase, width) {
    let buckets = round(count, width, output + 1);
    let shift = load(output + 1);
    let seed = sample_seed(randomBase);
    return deduplicate(input, count, scratch, buckets, seed, shift);
  }
  fn empty(output, width) {
    fill(output, 8, 0);
    store(output, 1);
    store(output + 1, width);
    store(output + 2, 1);
    store(output + 5, 1);
    store(output + 6, width);
    store(output + 7, output + 8);
    return output + 8;
  }
}

/-- The outer constructor body and all preparation/allocation helpers are
unchanged from the bounded source implementation. -/
theorem shared : source.functions[12]? = some Bounded.function ∧
    source.functions[1]? = Bounded.source.functions[1]? ∧
    source.functions[2]? = Bounded.source.functions[2]? ∧
    source.functions[3]? = Bounded.source.functions[3]? ∧
    source.functions[4]? = Bounded.source.functions[4]? ∧
    source.functions[5]? = Bounded.source.functions[5]? ∧
    source.functions[6]? = Bounded.source.functions[6]? ∧
    source.functions[7]? = Bounded.source.functions[7]? ∧
    source.functions[8]? = Bounded.source.functions[8]? ∧
    source.functions[11]? = Bounded.source.functions[11]? ∧
    source.functions[13]? = Bounded.source.functions[13]? ∧
    source.functions[14]? = Bounded.source.functions[14]? := by repeat constructor

/-- Ordinary root search reuses two locals across both phases. -/
def rootFunction : RamLang.Function := source.functions[9]'(by decide)

/-- Ordinary child search keeps the same frame size as the capped version. -/
def childFunction : RamLang.Function := source.functions[10]'(by decide)

/-- The deterministic root loop follows the random loop and candidate initialization. -/
def rootLoop : Stmt := match rootFunction.body with | .seq _ (.seq _ (.seq body _)) => body | _ => .skip

/-- One deterministic root trial followed by a charged odd-seed increment. -/
def rootIteration : Stmt := match rootLoop with | .while _ body => body | _ => .skip

/-- The deterministic child loop follows the two direct cases and random phase. -/
def childLoop : Stmt := match childFunction.body with
  | .seq _ (.seq _ (.seq _ (.seq _ (.seq body _)))) => body | _ => .skip

/-- One deterministic child trial followed by a charged odd-seed increment. -/
def childIteration : Stmt := match childLoop with | .while _ body => body | _ => .skip

/-- Deterministic compilation emits every shared body once. -/
def compiled : CompiledProgram := match compile source with | .ok c => c | .error _ => ⟨#[],[],0⟩

/-- The complete DSL program passes all static checks. -/
theorem compiles : compile source = .ok compiled := rfl

end PerfectHash.Source.Total
