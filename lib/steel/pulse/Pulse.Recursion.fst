module Pulse.Recursion

module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
open FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
module P = Pulse.Syntax.Printer

let tie_knot (g : env)  (rng : R.range)
             (body : st_term) (c : comp)
             (nm : string) (nm_orig : string)
: Tac (list (RT.sigelt_for (fstar_env g)))
=
  (* This is a temporary implementation. It will just create
  a new letbinding at the appropriate type with a `magic()` body. *)

  let f_ty : host_term =
    match c with
    | C_Tot t ->
      begin match t.t with
      | Tm_FStar t -> t
      | _ -> fail g (Some rng) "not a Tm_Fstar?"
      end
    | _ -> fail g (Some rng) "not a C_Tot?"
  in

  let bs, c = collect_arr_ln_bs f_ty in
  if Nil? bs then
    fail g (Some rng) "no binders";
  if Nil? (List.Tot.Base.init bs) then
    fail g (Some rng) "only one binder??";

  let ty = Reflection.V2.Derived.mk_arr_ln (List.Tot.Base.init bs) c in

  [RT.mk_unchecked_let (fstar_env g) nm_orig (`(magic())) ty]
