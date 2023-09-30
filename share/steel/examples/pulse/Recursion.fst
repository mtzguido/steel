module Recursion

open Pulse.Lib.Pervasives
open Pulse.Lib.Fixpoints

```pulse
fn rec test1
  (x:unit)
  requires emp
  ensures pure False
{
  let x = perform (fun () -> test1 ());
  ()
}
```

let _ = test1 

```pulse
fn rec test2
  (y:nat)
  requires emp
  ensures emp
{
  if (y > 0) {
    perform (fun () -> test2 (y-1));
    ()
  }
}
```

```pulse
fn rec test3
  (z:nat)
  (y:nat)
  requires emp
  returns _:int
  ensures emp
{
  if (y > 0) {
    perform (fun () -> test3 (z+1) (y-1));
  } else {
    z
  }
}
```

// SMT encoding failure...? not sure if fixpoints here are the problem
// ```pulse
// fn rec test4
//   (r : ref int)
//   (v : erased int)
//   (y : nat)
//   requires pts_to r v
//   ensures pts_to r (v+y)
// {
//   if (y > 0) {
//     perform (fun () -> test4 r v (y-1));
//     let v = !r;
//     r := v+1;
//   }
// }
// ```

```pulse
ghost
fn rec test5
  (z:nat)
  (y:nat)
  requires emp
  ensures emp
  decreases (y+z)
{
  perform_ghost (fun () -> test5 z y)
}
```



(*
let x = test2

open Pulse.Lib.Core
friend Pulse.Lib.Core

val fix_stt
  (#a #pre #post : _)
  (f : (stt a pre post -> stt a pre post))
  : stt a pre post
let fix_stt #a #pre #post f =
  let rec r : stt a pre post = fun () ->
    f r ()
  in
  r
  
val dvstt (#a #pre #post : _) (f : unit -> stt a pre post) : stt a pre post
let dvstt #a #pre #post f = fun () -> f () ()

val fix_test2 : (x:unit) -> Dv (stt unit emp (fun _ -> pure False))
let fix_test2 (x:unit) =
  let rec r (x:unit) : Dv (stt unit emp (fun _ -> pure False)) =
    test2 x r
  in
  dvstt r


```pulse
fn rec test3
  (x:unit) (y:int)
  requires emp
  ensures pure False
{
  let now x = test3 () (y+1);
  ()
}
```
