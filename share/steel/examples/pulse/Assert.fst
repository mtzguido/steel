module Assert
open Pulse.Lib.Pervasives


// assume val p : x:int -> v1:int -> v2:int -> vprop

// assume val f : x:int -> #v1:int -> #v2:int{v2 > v1} -> 
//                 stt unit (p x v1 v2) (fun _ -> emp)


// ```pulse
// fn test (_:unit)
//   requires p 1 2 4
//   ensures emp
//   {
//     f 1 #2
//   }
// ```


assume val p : prop
assume val q : prop
assume val r : prop
assume val s : prop


open FStar.Tactics

assume
val pp : vprop

assume
val test (x:unit) (#[exact (`())] y:unit) (z:unit) : stt unit emp (fun _ -> pp)

#set-options "--debug Assert --debug_level SMTQuery"


```pulse
fn test2 (_:unit)
  requires emp
  ensures pp
  {
    let _x = test () ();
    ()
  }
```
(*

assume val l1 : unit -> Lemma (requires p) (ensures q)
assume val l2 : unit -> Lemma (requires q) (ensures r)
assume val l3 : unit -> Lemma (requires r) (ensures s)

let l4 () : Lemma (requires p) (ensures r) =
  l1 ();
  l2()

```pulse
ghost
fn ll3 (_:unit)
  requires pure p
  ensures pure s
  {
    let x = l1();
    let y = l2();
    let z = l3();
    ()
  }
```


```pulse
fn test_assert (r0 r1: ref nat)
               (#p0 #p1:perm)
               (#v0:nat)
    requires 
        pts_to r0 #p0 v0 **
        (exists v1. pts_to r1 #p1 v1)
    ensures
        pts_to r0 #p0 v0 **
        (exists v1. pts_to r1 #p1 v1)
{
    //assert_ (pts_to r1 ?p1 ?v1); would be nice to have a version that also binds witnesses
    assert_ (pts_to r0 #p0 (v0 + 0));
    ()
}
```
