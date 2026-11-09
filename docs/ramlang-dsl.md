# Writing and verifying RamLang programs

Import `RamLang.DSL` for the C-like notation and proof tactics, or `RamLang` for
the complete source language, compiler, logic, and generic library.

```lean
import RamLang
open RamLang

def exampleProgram : Program := ram_program main {
  fn main(n) {
    let answer = recursive_sum(n);
    return answer;
  }

  fn recursive_sum(n) {
    if (n == 0) { return 0; }
    let saved = n;
    let rest = recursive_sum(n - 1);
    return rest + saved;
  }
}

#eval (Compiler.compile exampleProgram).map Compiler.CompiledProgram.report
#eval report exampleProgram
```

The name after `ram_program` selects the entry function. All function signatures
are collected before any body is lowered, so forward references, self recursion,
and mutual recursion work. A body is emitted once by the baseline compiler. The
entry accepts up to four words through the public ABI; ordinary calls can have
more parameters, subject to the checked function's declared arity.

## Expressions and effects

Expressions support names, natural-number literals, parentheses, `+`, `-`, `*`,
`%`, `>>`, calls, `load(address)`, and `random(address)`. Comparisons are `==`,
`!=`, `<`, and `<=`, with unsigned word semantics. Multiplication and remainder
bind more tightly than addition and subtraction; shifts bind less tightly.
Arithmetic and literals wrap according to the word width at execution time.

```lean
def visit : Program := ram_program visit {
  fn visit(p, n) {
    while (n != 0) {
      let old = load(p);
      store(p, old + 1);
      p = p + 1;
      n = n - 1;
    }
    return 0;
  }
}
```

`load` and `store` access ordinary RAM. `random` reads the separate immutable
random image at the supplied word address. Nested expressions and function
arguments evaluate from left to right. Intermediate results occupy ordinary
caller-owned frame slots, survive calls, and contribute to frame size and
instruction costs. Assignments such as `n = n - 1` lower directly to their
primitive operation without an extra temporary move.

A rich loop condition is evaluated before entry and again after each continuing
iteration. For example, `while (load(p) != 0) { store(p, load(p) - 1); }` rereads
memory for every test. Early return discards the surrounding loop and pending
statements, including the next test.

## Locals and diagnostics

`let x = expression;` declares an initialized mutable local. `let x;` reserves a
local slot that must be assigned before it is read. Blocks have lexical scope;
a block-local name does not escape. Parameters and local declarations must have
unique names throughout a function: shadowing is rejected. Repeated loop visits
reuse the same slots; they do not allocate additional frames.

The elaborator checks names, duplicate declarations, call arities, definite
initialization, and returns. Diagnostics identify the source function and local
for uninitialized reads. Initialization after conditionals accounts for both
continuing branches. A loop may execute zero times. Every function must return
on each continuing path. `DSL/Diagnostics.lean` checks these failures during the
normal build.

The output is an ordinary constructor term of type `RamLang.Program`, not a
runtime parser or interpreter. The existing core checker runs before that term
is accepted, and the compiler checks it again. Compiler theorems apply to the
resulting core. `DSL.Examples.sum_core` and `fill_core` prove by reflexivity that
the readable programs are exactly the cores used by their general proofs.

## Proofs and resources

`Logic.Contract` describes a source execution, its outcome/memory/trace
postcondition, an instruction allowance, and a stack peak. Source proofs use
`Contract.sequence`, `Contract.call`, `while_total`, and well-founded contract
induction. `Contract.compiled` transfers them to actual machine executions,
including wrapper work and the entry frame.

Three small tactics produce ordinary checked Lean proof terms:

- `ram_simp` reduces source operand lookup, assignment, and primitive semantics.
- `ram_primitive` proves a primitive source step with its optional access event.
- `ram_cost` reduces instruction-template charges and stack peaks.

They leave nontrivial arithmetic, memory separation, invariants, and recursive
contract obligations visible. There is no proof oracle or unchecked
verification-condition generator.

The generic library contains:

| Routine or rule | Source and proof | Target instruction bound | Stack bound |
| --- | --- | --- | --- |
| Fill | `Library.Fill.program`, `Logic.Fill.compiled_correct` | `22*n + 30` | 5 words |
| Disjoint copy | `Library.Copy.program`, `compiled_correct` | `33*n + 30` | 6 words |
| Traversal | `Library.Traversal.contract` | `(visitWork+5)*n+5` for the loop | supplied visit peak |
| Bounded retry | `Library.Retry.contract` | `(trialWork+5)*n+12` for the body | supplied trial peak |
| First nonzero sample | `Library.FirstNonzero.program`, `compiled_correct` | `28*n+28` | 5 words |

Fill and copy initialize dirty memory and preserve cells outside their declared
write regions. Copy requires disjoint source and destination arrays. All address
and counter bounds are explicit theorem hypotheses. Source/random access
policies transfer to interrupted target prefixes.

Retry separates runtime success from algorithmic budget failure: status one
means ordinary termination, and a zero result signals failure to accept within
the supplied attempt budget. The generic rule supports attempts that make
recursive calls, provided their contracts establish return and resource bounds.
Its application trace records exactly one addressed sample per attempt. A
representable reservation proves those addresses are fresh. The execution
proofs import no probability or hashing modules.

`report` displays linked instruction addresses, each function's code range and
frame size, and the instruction array. These are computable code/layout reports;
input-dependent execution bounds come from the source contracts above.

## Register-only compilation

`RegisterOnly.compile capacity program` is an alternative for a checked subset:
straight-line entry functions may call straight-line helpers whose bodies have
only primitives and a final return. Entry branches/loops, helper calls, and
recursion are rejected with eligibility errors. The baseline compiler remains
available for all those programs. Nested entry expressions `f(g(x))` are eligible
when `f` and `g` themselves are eligible helpers.

The argument is a budget of local registers; two additional registers hold the
result and status. Caller slots precede a separate reusable helper interval.
All arguments are copied before a helper starts, preserving repeated arguments,
permutations, and caller locals across calls. A result may overwrite an argument.
Insufficient register demand is rejected instead of silently aliasing slots.

```lean
#eval (RegisterOnly.compile 9 RegisterOnly.Examples.program).map
  RegisterOnly.Compiled.report
-- 15 instructions; 9/9 local registers; entry=5; helper=4; stack=0
```

`RegisterOnly.compiled_returns` preserves the full source trace and memory in
exactly the emitted code length. `compiled_readOnly` additionally transfers a
source no-write proof to every machine prefix. Neither theorem requires a stack
region. `RegisterOnly.contract` transfers the source contract interface to this
backend and retains the source access policy without extra memory permissions.
