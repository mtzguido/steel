module Pulse.Checker.Admit

module T = FStar.Tactics
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common

module FV = Pulse.Typing.FV

#push-options "--z3rlimit_factor 4"
let check_admit
  (g:env)
  (t:st_term{Tm_Admit? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c) =

  let Tm_Admit { ctag = c; typ=t; post } = t.term in
  let x = fresh g in
  let px = v_as_nv x in
  let res
    : (t:term & u:universe & universe_of g t u &
       post:vprop & tot_typing (extend x (Inl t) g) post Tm_VProp)
    = match post, post_hint with
      | None, None
      | Some _, Some _ ->
        T.fail "T_Admit: either no post or two posts"
      
      | Some post, _ ->
        let (| u, t_typing |) = check_universe g t in    
        let post_opened = open_term_nv post px in      
        let (| post, post_typing |) = 
            check_term_with_expected_type (extend x (Inl t) g) post_opened Tm_VProp
        in
        (| t, u, t_typing, post, E post_typing |)

      | _, Some post ->
        let post : post_hint_t = post in
        if x `Set.mem` freevars post.post
        then T.fail "Unexpected freevar clash in Tm_Admit"
        else (
          let post_typing_rec = post_hint_typing g post x in
          let post_opened = open_term_nv post.post px in              
          (| post.ret_ty, post.u, post_typing_rec.ty_typing, post_opened, post_typing_rec.post_typing |)
        )
  in
  let (| t, u, t_typing, post_opened, post_typing |) = res in
  let post = close_term post_opened x in
  let s : st_comp = {u;res=t;pre;post} in
  assume (open_term (close_term post_opened x) x == post_opened);
  (|
     _, //Tm_Admit c u t None,
     comp_admit c s,
     T_Admit _ _ c (STC _ s x t_typing pre_typing post_typing)
  |)
#pop-options