module Pulse.Recursion

module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
open FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
module P = Pulse.Syntax.Printer

type tm_abs_zip = binder & option qualifier & comp

let add_knot (g : env) (rng : R.range)
             (body : st_term)
             (nm : string) (nm_orig : string)
: Tac (st:st_term{Tm_Abs? st.term})
= 
  let rec aux (scope:list tm_abs_zip) (st:st_term) : Tac st_term =
    match st.term with
    | Tm_Abs {b;q;ascription;body} ->
      aux ((b,q,ascription) :: scope) body
    | _ ->
      Tactics.fail ""
  in
  let r = aux [] body in
  assume (Tm_Abs? r.term);
  r

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
