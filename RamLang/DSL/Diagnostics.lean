import RamLang.DSL.Elaborate

/-! Elaboration failures are checked as part of the ordinary Lean build. These
commands assert diagnostics without adding invalid programs to the library. -/

/-- error: unknown local 'missing' -/
#guard_msgs in
#check ram_program main { fn main() { return missing; } }

/-- error: uninitialized local 'value' in function 'main' -/
#guard_msgs in
#check ram_program main { fn main() { let value; return value; } }

/-- error: function 'helper' expects 1 arguments, got 0 -/
#guard_msgs in
#check ram_program main {
  fn main() { return helper(); }
  fn helper(x) { return x; }
}

/-- error: unknown local 'inside' -/
#guard_msgs in
#check ram_program main { fn main() { if (1 == 1) { let inside = 2; } return inside; } }

/-- error: function 'main' does not return on every path -/
#guard_msgs in
#check ram_program main { fn main(n) { if (n == 0) { return 0; } } }

/-- error: duplicate local 'n' (shadowing is not supported) -/
#guard_msgs in
#check ram_program main { fn main(n) { let n = 2; return n; } }

/-- error: unknown function 'missing' -/
#guard_msgs in
#check ram_program main { fn main() { return missing(1); } }

/-- error: duplicate function 'main' -/
#guard_msgs in
#check ram_program main { fn main() { return 0; } fn main() { return 1; } }

/-- error: entry function has 5 parameters; the public ABI supports at most 4 -/
#guard_msgs in
#check ram_program main { fn main(a,b,c,d,e) { return a; } }

/-- error: function 'helper' expects 1 arguments, got 0 -/
#guard_msgs in
#check ram_program main {
  fn main() { helper(); return 0; }
  fn helper(x) { return x; }
}
