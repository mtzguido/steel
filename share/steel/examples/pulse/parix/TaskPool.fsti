module TaskPool

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open Promises
module T = FStar.Tactics

val pool : Type0
val pool_alive : (#[T.exact (`full_perm)]p : perm) -> pool -> vprop
val pool_done : pool -> vprop

val setup_pool (n:nat)
  : stt pool emp (fun p -> pool_alive #full_perm p)

val task_handle : pool -> a:Type0 -> (a -> vprop) -> Type0
val joinable : #p:pool -> #a:Type0 -> #post:_ -> th:(task_handle p a post) -> vprop
val joined   : #p:pool -> #a:Type0 -> #post:_ -> th:(task_handle p a post) -> vprop

val handle_solved
  (#p : pool) 
  (#a : Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : vprop

(* Spawn only requires an *epsilon* of permission over the pool.
We do not have to be exclusive owners of it in order to queue a job. *)
val spawn
  (#e : perm)
  (#a : Type0)
  (#pre : vprop) (#post : a -> vprop)
  (p:pool)
  ($f : unit -> stt a pre (fun (x:a) -> post x))
  : stt (task_handle p a post)
        (pool_alive #e p ** pre)
        (fun th -> pool_alive #e p ** joinable th ** promise (joined th) post)

(* Spawn of a unit-returning task with no intention to join, simpler. *)
val spawn_
  (#e : perm)
  (#pre #post : _)
  (p:pool) (f : unit -> stt unit pre (fun _ -> post))
  : stt unit (pool_alive #e p ** pre)
             (fun prom -> pool_alive #e p ** promise (pool_done p) post)

(* If the pool is done, all pending joinable threads must be done *)
val must_be_done
  (#p : pool)
  (#a: Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : stt_ghost unit emp_inames (pool_done p ** joinable th) (fun () -> pool_done p ** handle_solved th)

val join0
  (#p:pool)
  (#a:Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : stt unit (joinable th) (fun () -> handle_solved th)

val extract
  (#p:pool)
  (#a:Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : stt a (handle_solved th) (fun x -> post x)
  
val split_alive
  (p:pool)
  (e:perm)
  : stt_ghost unit emp_inames
              (pool_alive #e p)
              (fun () -> pool_alive #(half_perm e) p ** pool_alive #(half_perm e) p)

val join_alive
  (p:pool)
  (e:perm)
  : stt_ghost unit emp_inames
              (pool_alive #(half_perm e) p ** pool_alive #(half_perm e) p)
              (fun () -> pool_alive #e p)

val join
  (#p:pool)
  (#a:Type0)
  (#post : a -> vprop)
  (th : task_handle p a post)
  : stt a (joinable th) (fun x -> post x)

(* We must exclusively own the pool in order to terminate it. *)
val teardown_pool
  (p:pool)
  : stt unit (pool_alive #full_perm p) (fun _ -> pool_done p)


(* In other cases, however, some of the ownership may be in tasks within
the pool, so we require *some* permission plus a *promise* of the rest. *)
val teardown_pool_partial
  (p:pool) (e:perm{lesser_perm e full_perm})
  : stt unit (pool_alive #e p ** promise (pool_done p) (pool_alive #(comp e) p))
             (fun _ -> pool_done p)
