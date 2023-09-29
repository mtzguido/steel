module Recursion

open Pulse.Lib.Pervasives
open Pulse.Lib.Fixpoints

```pulse
fn __test1
  (x:unit)
  (__test1 : (unit -> stt unit emp (fun _ -> pure False)))
  requires emp
  ensures pure False
{
  let x = perform (fun () -> __test1 ());
  ()
}
```
let test1 = fix_stt_1 __test1

```pulse
fn rec test2
  (x:unit)
  requires emp
  ensures pure False
{
  let x = perform (fun () -> test2 ());
  ()
}
```

let _ = test2

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
