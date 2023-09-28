module TaskPool.Examples

open Pulse.Lib.Pervasives
open Promises
open TaskPool

assume
val qsv : nat -> vprop
assume
val qsc : n:nat -> stt unit emp (fun _ -> qsv n)

let spawn_ #pre #post p f = spawn_ #full_perm #pre #post p f

```pulse
fn qs (n:nat)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2 ** qsv 3 ** qsv 4
{
  let p = setup_pool 42;
  spawn_ p (fun () -> qsc 1);
  spawn_ p (fun () -> qsc 2);
  spawn_ p (fun () -> qsc 3);
  spawn_ p (fun () -> qsc 4);
  teardown_pool p;
  redeem_promise (pool_done p) (qsv 1);
  redeem_promise (pool_done p) (qsv 2);
  redeem_promise (pool_done p) (qsv 3);
  redeem_promise (pool_done p) (qsv 4);
  drop_ (pool_done p);
  ()
}
```

```pulse
fn qs_joinpromises (n:nat)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2 ** qsv 3 ** qsv 4
{
  let p = setup_pool 42;
  spawn_ p (fun () -> qsc 1);
  spawn_ p (fun () -> qsc 2);
  spawn_ p (fun () -> qsc 3);
  spawn_ p (fun () -> qsc 4);
  join_promise #(pool_done p) (qsv 1) (qsv 2);
  join_promise #(pool_done p) (qsv 3) (qsv 4);
  teardown_pool p;
  redeem_promise (pool_done p) (qsv 1 ** qsv 2);
  redeem_promise (pool_done p) (qsv 3 ** qsv 4);
  drop_ (pool_done p);
  ()
}
```

```pulse
fn qspair (i j : nat) (_:unit)
  requires emp
  returns _:unit
  ensures qsv i ** qsv j
  {
    qsc i;
    qsc j
  }
```

```pulse
fn qsh (n:nat)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2 ** qsv 3 ** qsv 4
{
  let p = setup_pool 42;
  spawn_ p (qspair 1 2);
  spawn_ p (qspair 3 4);
  teardown_pool p;
  redeem_promise (pool_done p) (qsv 1 ** qsv 2);
  redeem_promise (pool_done p) (qsv 3 ** qsv 4);
  drop_ (pool_done p);
  ()
}
```

```pulse
fn qs12_par (p:pool)
  requires pool_alive p
  returns _:unit
  ensures pool_alive p ** promise (pool_done p) (qsv 1) ** promise (pool_done p) (qsv 2)
  {
    spawn_ p (fun () -> qsc 1);
    spawn_ p (fun () -> qsc 2);
    ()
  }
```

[@@expect_failure]
```pulse
fn qsh_par (n:nat)
  requires emp
  returns _:unit
  ensures qsv 1 ** qsv 2 ** qsv 3 ** qsv 4
{
  let p = setup_pool 42;
  spawn p (fun () -> qs12_par p);
  (* Ah! This cannot work right now since we need to share part
  of the pool_alive vprop to the spawned task, so we have
  to index pool_alive with a permission, and allow
  share/gather. *)
  
  spawn p (fun () -> qsc 3);
  spawn p (fun () -> qsc 4);
  teardown_pool p;
  redeem_promise (pool_done p) (qsv 1)
  redeem_promise (pool_done p) (qsv 2);
  redeem_promise (pool_done p) (qsv 3);
  redeem_promise (pool_done p) (qsv 4);
  drop_ (pool_done p);
  ()
}
```