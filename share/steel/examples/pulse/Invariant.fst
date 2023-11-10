module Invariant

open Pulse.Lib.Pervasives
open Pulse.Lib.Reference

```pulse
fn package (r:ref int)
   requires pts_to r 123
   returns i : inv (pts_to r 123)
   ensures emp
{
  let i : inv (pts_to r 123) = new_invariant' (pts_to r 123);
  i
}
```

// Fails as it is not atomic
[@@expect_failure]
```pulse
fn test2 (_:unit)
  requires emp
  returns v:(v:int{v == 2})
  ensures emp
{
  let r = alloc 123;
  let i = package r;
  with_invariants i ensures pure True {
    r := 124;
    r := 123;
    ()
  };
  2
}
```

#set-options "--error_contexts true"
#set-options "--print_implicits --print_universes"
// #set-options "--trace_error"

let test (i:inv emp) = assert  (
  (add_inv emp_inames i)
  ==
  ((join_inames (((add_inv #emp) emp_inames) i)) emp_inames)
)

#set-options "--ugly"
 ```pulse
 ghost
 fn t0 (_:unit) (i:inv emp)
   requires emp
   ensures emp
   opens (add_inv emp_inames i)
 {
   with_invariants i {
     ()
   }
 }
```

#set-options "--ext pulse:guard_policy=SMTSync"
#set-options "--debug Invariant --debug_level SMTQuery"

assume val i : inv emp

// ```pulse
// ghost
// fn zz (_:unit)
//   requires emp
//   ensures emp
// {
//   (); ()
// }
// ```

(* Using invariants while claiming not to. *)
[@@expect_failure]
```pulse
ghost
fn t1 (_:unit)
  requires emp
  ensures emp
  opens emp_inames
{
  with_invariants i {
    ()
  }
}
```

(* Fails due to bad scoping *)
```pulse
fn t2 (_:unit) (i : inv emp)
  requires emp
  returns _:int
  ensures emp
  // opens (add_inv emp_inames i)
{
  with_invariants i ensures emp {
    ()
  };
  123
}
```
