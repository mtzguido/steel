module Invariant

open Pulse.Lib.Pervasives
open Pulse.Lib.Reference

let inames_ext (is1 is2 : inames)
  : Lemma (requires forall i. Set.mem i is1 <==> Set.mem i is2)
          (ensures is1 == is2)
          [SMTPat (is1 == is2)]
  = Set.lemma_equal_intro is1 is2

```pulse
fn package (r:ref int)
   requires pts_to r 123
   returns i : inv (pts_to r 123)
   ensures emp
{
  let i : inv (pts_to r 123) =
    new_invariant' #emp_inames (pts_to r 123);
  i
}
```

// Incredibly basic  with_invariant test
// (and bogus, since it's in stt and the body is not atomic)
// ```pulse
// fn test2 (_:unit)
//   requires emp
//   returns v:(v:int{v == 2})
//   ensures emp
// {
//   let r = alloc 123;
//   let i = package r;
//   with_invariants i ensures pure True {
//     r := 124;
//     r := 123;
//     ()
//   };
//   2
// }
// ```

#set-options "--error_contexts true"
#set-options "--print_implicits --print_universes"
// #set-options "--trace_error"

//[@@expect_failure [19; 228]]
// ```pulse
// ghost
// fn t0 (_:unit) (i:inv emp)
//   requires emp
//   ensures emp
//   opens emp_inames
// {
//   with_invariants i {
//     ()
//   }
// }
// ```

#set-options "--ext pulse:guard_policy=SMTSync"
#set-options "--debug Invariant --debug_level SMTQuery"

assume val i : inv emp

```pulse
ghost
fn t1 (_:unit)
  requires emp
  ensures emp
  opens (add_inv (add_inv emp_inames i) i)
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
  ensures emp
{
  with_invariants i ensures emp {
    ()
  };
  ()
}
```
