open Prims
type ('g, 't) vprop_typing = unit
type ('g, 'ctxt, 'gu, 'ctxtu) continuation_elaborator =
  unit Pulse_Checker_Common.post_hint_opt ->
    (unit, unit, unit) Pulse_Checker_Common.checker_result_t ->
      ((unit, unit, unit) Pulse_Checker_Common.checker_result_t, unit)
        FStar_Tactics_Effect.tac_repr
let (k_elab_unit :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (unit, unit, unit, unit) continuation_elaborator)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun ctxt ->
           fun p ->
             fun r ->
               Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> r)))
        uu___1 uu___
let (k_elab_trans :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Typing_Env.env ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit) continuation_elaborator ->
                (unit, unit, unit, unit) continuation_elaborator ->
                  (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g0 ->
    fun g1 ->
      fun g2 ->
        fun ctxt0 ->
          fun ctxt1 ->
            fun ctxt2 ->
              fun k0 ->
                fun k1 ->
                  fun post_hint ->
                    fun res ->
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                                 (Prims.of_int (26)) (Prims.of_int (39))
                                 (Prims.of_int (26)) (Prims.of_int (57)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                                 (Prims.of_int (26)) (Prims.of_int (26))
                                 (Prims.of_int (26)) (Prims.of_int (57)))))
                        (Obj.magic (k1 post_hint res))
                        (fun uu___ ->
                           (fun uu___ -> Obj.magic (k0 post_hint uu___))
                             uu___)
let (comp_st_with_post :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp_st)
  =
  fun c ->
    fun post ->
      match c with
      | Pulse_Syntax_Base.C_ST st ->
          Pulse_Syntax_Base.C_ST
            {
              Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
              Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
              Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
              Pulse_Syntax_Base.post = post
            }
      | Pulse_Syntax_Base.C_STGhost (i, st) ->
          Pulse_Syntax_Base.C_STGhost
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
                Pulse_Syntax_Base.post = post
              })
      | Pulse_Syntax_Base.C_STAtomic (i, st) ->
          Pulse_Syntax_Base.C_STAtomic
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
                Pulse_Syntax_Base.post = post
              })
let (st_equiv_post :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.term ->
            unit -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t ->
      fun c ->
        fun d ->
          fun post ->
            fun veq ->
              let c' = comp_st_with_post c post in
              let uu___ =
                Pulse_Typing_Metatheory.st_comp_typing_inversion g
                  (Pulse_Syntax_Base.st_comp_of_comp c)
                  (Pulse_Typing_Metatheory.comp_typing_inversion g c
                     (Pulse_Typing_Metatheory.st_typing_correctness g t c d)) in
              match uu___ with
              | FStar_Pervasives.Mkdtuple4 (u_of, pre_typing, x, post_typing)
                  ->
                  let st_equiv =
                    Pulse_Typing.ST_VPropEquiv
                      (g, c, c', x, (), (), (), (), ()) in
                  Pulse_Typing.T_Equiv (g, t, c, c', d, st_equiv)
let (simplify_post :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.term -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t -> fun c -> fun d -> fun post -> st_equiv_post g t c d post ()
let (k_elab_equiv_continutation :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            (unit, unit, unit, unit) continuation_elaborator ->
              unit -> (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g1 ->
    fun g2 ->
      fun ctxt ->
        fun ctxt1 ->
          fun ctxt2 ->
            fun k ->
              fun d ->
                fun post_hint ->
                  fun res ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                               (Prims.of_int (74)) (Prims.of_int (60))
                               (Prims.of_int (77)) (Prims.of_int (33)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                               (Prims.of_int (78)) (Prims.of_int (4))
                               (Prims.of_int (88)) (Prims.of_int (34)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ ->
                            FStar_Pervasives.Mkdtuple3
                              (Pulse_Syntax_Base.tm_emp, (), ())))
                      (fun uu___ ->
                         (fun framing_token ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.Common.fst"
                                          (Prims.of_int (79))
                                          (Prims.of_int (26))
                                          (Prims.of_int (79))
                                          (Prims.of_int (29)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.Common.fst"
                                          (Prims.of_int (78))
                                          (Prims.of_int (4))
                                          (Prims.of_int (88))
                                          (Prims.of_int (34)))))
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ -> res))
                                 (fun uu___ ->
                                    (fun uu___ ->
                                       match uu___ with
                                       | FStar_Pervasives.Mkdtuple3
                                           (st, c, st_d) ->
                                           if
                                             Prims.op_Negation
                                               (Pulse_Syntax_Base.stateful_comp
                                                  c)
                                           then
                                             Obj.magic
                                               (k post_hint
                                                  (FStar_Pervasives.Mkdtuple3
                                                     (st, c, st_d)))
                                           else
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Prover.Common.fst"
                                                           (Prims.of_int (83))
                                                           (Prims.of_int (18))
                                                           (Prims.of_int (83))
                                                           (Prims.of_int (95)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Prover.Common.fst"
                                                           (Prims.of_int (81))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (88))
                                                           (Prims.of_int (34)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                          g2
                                                          (Pulse_Syntax_Base.st_comp_of_comp
                                                             c)
                                                          (Pulse_Typing_Metatheory.comp_typing_inversion
                                                             g2 c
                                                             (Pulse_Typing_Metatheory.st_typing_correctness
                                                                g2 st c st_d))))
                                                  (fun uu___2 ->
                                                     (fun uu___2 ->
                                                        match uu___2 with
                                                        | FStar_Pervasives.Mkdtuple4
                                                            (uu___3,
                                                             pre_typing,
                                                             uu___4, uu___5)
                                                            ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (95)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (34)))))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___6 ->
                                                                    Pulse_Checker_Framing.apply_frame
                                                                    g2 st
                                                                    ctxt1 ()
                                                                    c st_d
                                                                    framing_token))
                                                                 (fun uu___6
                                                                    ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c',
                                                                    st_d') ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    simplify_post
                                                                    g2 st c'
                                                                    st_d'
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    st_d'1 ->
                                                                    Obj.magic
                                                                    (k
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (st,
                                                                    (comp_st_with_post
                                                                    c'
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)),
                                                                    st_d'1))))
                                                                    uu___7)))
                                                                    uu___6)))
                                                       uu___2))) uu___)))
                           uu___)
let (k_elab_equiv_prefix :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            (unit, unit, unit, unit) continuation_elaborator ->
              unit -> (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g1 ->
    fun g2 ->
      fun ctxt1 ->
        fun ctxt2 ->
          fun ctxt ->
            fun k ->
              fun d ->
                fun post_hint ->
                  fun res ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                               (Prims.of_int (97)) (Prims.of_int (60))
                               (Prims.of_int (99)) (Prims.of_int (31)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                               (Prims.of_int (100)) (Prims.of_int (4))
                               (Prims.of_int (115)) (Prims.of_int (11)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ ->
                            FStar_Pervasives.Mkdtuple3
                              (Pulse_Syntax_Base.tm_emp, (), ())))
                      (fun uu___ ->
                         (fun framing_token ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.Common.fst"
                                          (Prims.of_int (101))
                                          (Prims.of_int (12))
                                          (Prims.of_int (101))
                                          (Prims.of_int (27)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.Common.fst"
                                          (Prims.of_int (101))
                                          (Prims.of_int (30))
                                          (Prims.of_int (115))
                                          (Prims.of_int (11)))))
                                 (Obj.magic (k post_hint res))
                                 (fun res1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ ->
                                         match res1 with
                                         | FStar_Pervasives.Mkdtuple3
                                             (st, c, st_d) ->
                                             if
                                               Prims.op_Negation
                                                 (Pulse_Syntax_Base.stateful_comp
                                                    c)
                                             then
                                               FStar_Pervasives.Mkdtuple3
                                                 (st, c, st_d)
                                             else
                                               (match Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                        g1
                                                        (Pulse_Syntax_Base.st_comp_of_comp
                                                           c)
                                                        (Pulse_Typing_Metatheory.comp_typing_inversion
                                                           g1 c
                                                           (Pulse_Typing_Metatheory.st_typing_correctness
                                                              g1 st c st_d))
                                                with
                                                | FStar_Pervasives.Mkdtuple4
                                                    (uu___2, pre_typing,
                                                     uu___3, uu___4)
                                                    ->
                                                    (match Pulse_Checker_Framing.apply_frame
                                                             g1 st ctxt2 () c
                                                             st_d
                                                             framing_token
                                                     with
                                                     | Prims.Mkdtuple2
                                                         (c', st_d') ->
                                                         FStar_Pervasives.Mkdtuple3
                                                           (st,
                                                             (comp_st_with_post
                                                                c'
                                                                (Pulse_Syntax_Base.comp_post
                                                                   c)),
                                                             (simplify_post
                                                                g1 st c'
                                                                st_d'
                                                                (Pulse_Syntax_Base.comp_post
                                                                   c)))))))))
                           uu___)
let (k_elab_equiv :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit) continuation_elaborator ->
                unit ->
                  unit -> (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g1 ->
    fun g2 ->
      fun ctxt1 ->
        fun ctxt1' ->
          fun ctxt2 ->
            fun ctxt2' ->
              fun k ->
                fun d1 ->
                  fun d2 ->
                    let k1 =
                      k_elab_equiv_continutation g1 g2 ctxt1 ctxt2 ctxt2' k
                        () in
                    let k2 =
                      k_elab_equiv_prefix g1 g2 ctxt1 ctxt1' ctxt2' k1 () in
                    k2
let rec (list_as_vprop' :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.vprop Prims.list -> Pulse_Syntax_Base.vprop)
  =
  fun vp ->
    fun fvps ->
      match fvps with
      | [] -> vp
      | hd::tl -> list_as_vprop' (Pulse_Syntax_Base.tm_star vp hd) tl
let rec (canon_right_aux :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop Prims.list ->
      (Pulse_Syntax_Base.vprop ->
         (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
        ->
        ((Pulse_Syntax_Base.vprop Prims.list,
           Pulse_Syntax_Base.vprop Prims.list, unit) FStar_Pervasives.dtuple3,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun vps ->
             fun f ->
               match vps with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ ->
                              FStar_Pervasives.Mkdtuple3 ([], [], ()))))
               | hd::rest ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Common.fst"
                                    (Prims.of_int (144)) (Prims.of_int (7))
                                    (Prims.of_int (144)) (Prims.of_int (11)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Common.fst"
                                    (Prims.of_int (144)) (Prims.of_int (4))
                                    (Prims.of_int (168)) (Prims.of_int (7)))))
                           (Obj.magic (f hd))
                           (fun uu___ ->
                              (fun uu___ ->
                                 if uu___
                                 then
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Prover.Common.fst"
                                                 (Prims.of_int (146))
                                                 (Prims.of_int (32))
                                                 (Prims.of_int (146))
                                                 (Prims.of_int (56)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Prover.Common.fst"
                                                 (Prims.of_int (145))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (162))
                                                 (Prims.of_int (34)))))
                                        (Obj.magic (canon_right_aux g rest f))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                match uu___1 with
                                                | FStar_Pervasives.Mkdtuple3
                                                    (vps', fvps, uu___3) ->
                                                    FStar_Pervasives.Mkdtuple3
                                                      (vps', (hd :: fvps),
                                                        ()))))
                                 else
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Prover.Common.fst"
                                                 (Prims.of_int (165))
                                                 (Prims.of_int (33))
                                                 (Prims.of_int (165))
                                                 (Prims.of_int (57)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Prover.Common.fst"
                                                 (Prims.of_int (164))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (167))
                                                 (Prims.of_int (33)))))
                                        (Obj.magic (canon_right_aux g rest f))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                match uu___2 with
                                                | FStar_Pervasives.Mkdtuple3
                                                    (vps', pures, uu___4) ->
                                                    FStar_Pervasives.Mkdtuple3
                                                      ((hd :: vps'), pures,
                                                        ()))))) uu___))))
          uu___2 uu___1 uu___
let (canon_right :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        (Pulse_Syntax_Base.vprop ->
           (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
          ->
          ((Pulse_Syntax_Base.term, unit,
             (unit, unit, unit, unit) continuation_elaborator)
             FStar_Pervasives.dtuple3,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun f ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                     (Prims.of_int (178)) (Prims.of_int (33))
                     (Prims.of_int (178)) (Prims.of_int (73)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                     (Prims.of_int (178)) (Prims.of_int (3))
                     (Prims.of_int (183)) (Prims.of_int (104)))))
            (Obj.magic
               (canon_right_aux g
                  (Pulse_Checker_VPropEquiv.vprop_as_list ctxt) f))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    match uu___ with
                    | FStar_Pervasives.Mkdtuple3 (vps', pures, veq) ->
                        FStar_Pervasives.Mkdtuple3
                          ((list_as_vprop'
                              (Pulse_Checker_VPropEquiv.list_as_vprop vps')
                              pures), (),
                            (k_elab_equiv g g ctxt ctxt ctxt
                               (list_as_vprop'
                                  (Pulse_Checker_VPropEquiv.list_as_vprop
                                     vps') pures) (k_elab_unit g ctxt) () ()))))
let (continuation_elaborator_with_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.st_term ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            unit ->
              ((Pulse_Syntax_Base.var,
                 (unit, unit, unit, unit) continuation_elaborator)
                 Prims.dtuple2,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun ctxt ->
                   fun c1 ->
                     fun e1 ->
                       fun e1_typing ->
                         fun ctxt_pre1_typing ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   match Pulse_Checker_Framing.apply_frame g
                                           e1
                                           (Pulse_Syntax_Base.tm_star ctxt
                                              (Pulse_Syntax_Base.comp_pre c1))
                                           () c1 e1_typing
                                           (FStar_Pervasives.Mkdtuple3
                                              (ctxt, (), ()))
                                   with
                                   | Prims.Mkdtuple2 (c11, e1_typing1) ->
                                       (match Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                g
                                                (Pulse_Syntax_Base.st_comp_of_comp
                                                   c11)
                                                (Pulse_Typing_Metatheory.comp_typing_inversion
                                                   g c11
                                                   (Pulse_Typing_Metatheory.st_typing_correctness
                                                      g e1 c11 e1_typing1))
                                        with
                                        | FStar_Pervasives.Mkdtuple4
                                            (u_of_1, pre_typing, uu___1,
                                             uu___2)
                                            ->
                                            Prims.Mkdtuple2
                                              ((Pulse_Typing_Env.fresh g),
                                                ((fun post_hint ->
                                                    fun res ->
                                                      FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Prover.Common.fst"
                                                                 (Prims.of_int (216))
                                                                 (Prims.of_int (34))
                                                                 (Prims.of_int (216))
                                                                 (Prims.of_int (37)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Prover.Common.fst"
                                                                 (Prims.of_int (215))
                                                                 (Prims.of_int (24))
                                                                 (Prims.of_int (248))
                                                                 (Prims.of_int (5)))))
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___3 -> res))
                                                        (fun uu___3 ->
                                                           (fun uu___3 ->
                                                              match uu___3
                                                              with
                                                              | FStar_Pervasives.Mkdtuple3
                                                                  (e2, c2,
                                                                   e2_typing)
                                                                  ->
                                                                  if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.stateful_comp
                                                                    c2)
                                                                  then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V1_Derived.fail
                                                                    "Unexpected non-stateful comp in continuation elaborate"))
                                                                  else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    e2_typing))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    e2_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    e2
                                                                    (Pulse_Typing_Env.fresh
                                                                    g)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    e2_closed
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    (Pulse_Typing_Env.fresh
                                                                    g)
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c2))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V1_Derived.fail
                                                                    "Impossible"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Bind.bind_res_and_post_typing
                                                                    g
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)
                                                                    (Pulse_Typing_Env.fresh
                                                                    g)
                                                                    post_hint))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (t_typing,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Bind.mk_bind
                                                                    g
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c1)) e1
                                                                    e2_closed
                                                                    c11 c2
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    (Pulse_Typing_Env.fresh
                                                                    g))
                                                                    e1_typing1
                                                                    ()
                                                                    e2_typing1
                                                                    () ()))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e, c,
                                                                    e_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e, c,
                                                                    e_typing)))))
                                                                    uu___6))))
                                                                    uu___5)))
                                                                    uu___5))))
                                                             uu___3))))))))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
type mk_t =
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        ((Pulse_Syntax_Base.ppname, Pulse_Syntax_Base.st_term,
           Pulse_Syntax_Base.comp, (unit, unit, unit) Pulse_Typing.st_typing)
           FStar_Pervasives.dtuple4 FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr
let (elim_one :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.vprop ->
        unit ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Syntax_Base.comp ->
                (unit, unit, unit) Pulse_Typing.st_typing ->
                  ((Pulse_Typing_Env.env, Pulse_Syntax_Base.term, unit,
                     (unit, unit, unit, unit) continuation_elaborator)
                     FStar_Pervasives.dtuple4,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun p ->
        fun ctxt_p_typing ->
          fun nx ->
            fun e1 ->
              fun c1 ->
                fun e1_typing ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                             (Prims.of_int (264)) (Prims.of_int (20))
                             (Prims.of_int (264)) (Prims.of_int (57)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                             (Prims.of_int (264)) (Prims.of_int (60))
                             (Prims.of_int (278)) (Prims.of_int (34)))))
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))
                    (fun uu___ ->
                       (fun ctxt_typing ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Prover.Common.fst"
                                        (Prims.of_int (266))
                                        (Prims.of_int (19))
                                        (Prims.of_int (266))
                                        (Prims.of_int (81)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Prover.Common.fst"
                                        (Prims.of_int (264))
                                        (Prims.of_int (60))
                                        (Prims.of_int (278))
                                        (Prims.of_int (34)))))
                               (Obj.magic
                                  (continuation_elaborator_with_bind g ctxt
                                     c1 e1 e1_typing ()))
                               (fun uu___ ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 ->
                                       match uu___ with
                                       | Prims.Mkdtuple2 (x, k) ->
                                           FStar_Pervasives.Mkdtuple4
                                             ((Pulse_Typing_Env.push_binding
                                                 g x nx
                                                 (Pulse_Syntax_Base.comp_res
                                                    c1)),
                                               (Pulse_Syntax_Base.tm_star
                                                  (Pulse_Syntax_Naming.open_term_nv
                                                     (Pulse_Syntax_Base.comp_post
                                                        c1)
                                                     (Pulse_Syntax_Base.v_as_nv
                                                        x)) ctxt), (), k)))))
                         uu___)
let rec (elim_all :
  Pulse_Typing_Env.env ->
    (Pulse_Syntax_Base.vprop ->
       (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
      ->
      mk_t ->
        Pulse_Syntax_Base.term ->
          unit ->
            ((Prims.bool * (Pulse_Typing_Env.env, Pulse_Syntax_Base.term,
               unit, (unit, unit, unit, unit) continuation_elaborator)
               FStar_Pervasives.dtuple4),
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun g ->
               fun f ->
                 fun mk ->
                   fun ctxt ->
                     fun ctxt_typing ->
                       match ctxt.Pulse_Syntax_Base.t with
                       | Pulse_Syntax_Base.Tm_Star (ctxt', p) ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Prover.Common.fst"
                                            (Prims.of_int (291))
                                            (Prims.of_int (22))
                                            (Prims.of_int (291))
                                            (Prims.of_int (70)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Prover.Common.fst"
                                            (Prims.of_int (292))
                                            (Prims.of_int (7))
                                            (Prims.of_int (304))
                                            (Prims.of_int (10)))))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ -> ()))
                                   (fun uu___ ->
                                      (fun p_typing ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Prover.Common.fst"
                                                       (Prims.of_int (292))
                                                       (Prims.of_int (10))
                                                       (Prims.of_int (292))
                                                       (Prims.of_int (13)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Prover.Common.fst"
                                                       (Prims.of_int (292))
                                                       (Prims.of_int (7))
                                                       (Prims.of_int (304))
                                                       (Prims.of_int (10)))))
                                              (Obj.magic (f p))
                                              (fun uu___ ->
                                                 (fun uu___ ->
                                                    if uu___
                                                    then
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (35)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (64)))))
                                                              (Obj.magic
                                                                 (mk g p ()))
                                                              (fun uu___1 ->
                                                                 (fun uu___1
                                                                    ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (nx, e1,
                                                                    c1,
                                                                    e1_typing))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (elim_one
                                                                    g ctxt' p
                                                                    () nx e1
                                                                    c1
                                                                    e1_typing))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g',
                                                                    uu___3,
                                                                    ctxt_typing',
                                                                    k) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (elim_all
                                                                    g' f mk
                                                                    uu___3 ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (uu___6,
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g'',
                                                                    ctxt'',
                                                                    ctxt_typing'',
                                                                    k')) ->
                                                                    (true,
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (g'',
                                                                    ctxt'',
                                                                    (),
                                                                    (k_elab_trans
                                                                    g g' g''
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt' p)
                                                                    uu___3
                                                                    ctxt'' k
                                                                    k'))))))))
                                                                    uu___2)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (false,
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (g, ctxt,
                                                                    (),
                                                                    (k_elab_unit
                                                                    g ctxt))))))))
                                                                   uu___1)))
                                                    else
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 (false,
                                                                   (FStar_Pervasives.Mkdtuple4
                                                                    (g, ctxt,
                                                                    (),
                                                                    (k_elab_unit
                                                                    g ctxt))))))))
                                                   uu___))) uu___)))
                       | uu___ ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      (false,
                                        (FStar_Pervasives.Mkdtuple4
                                           (g, ctxt, (),
                                             (k_elab_unit g ctxt))))))))
              uu___4 uu___3 uu___2 uu___1 uu___
let (add_elims_aux :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (Pulse_Syntax_Base.vprop ->
         (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
        ->
        mk_t ->
          unit ->
            ((Prims.bool * (Pulse_Typing_Env.env, Pulse_Syntax_Base.term,
               unit, (unit, unit, unit, unit) continuation_elaborator)
               FStar_Pervasives.dtuple4),
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun f ->
        fun mk ->
          fun ctxt_typing ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                       (Prims.of_int (317)) (Prims.of_int (40))
                       (Prims.of_int (317)) (Prims.of_int (65)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                       (Prims.of_int (317)) (Prims.of_int (4))
                       (Prims.of_int (320)) (Prims.of_int (66)))))
              (Obj.magic (canon_right g ctxt () f))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | FStar_Pervasives.Mkdtuple3 (ctxt', ctxt'_typing, k) ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Prover.Common.fst"
                                      (Prims.of_int (319)) (Prims.of_int (9))
                                      (Prims.of_int (319))
                                      (Prims.of_int (35)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Prover.Common.fst"
                                      (Prims.of_int (317))
                                      (Prims.of_int (68))
                                      (Prims.of_int (320))
                                      (Prims.of_int (66)))))
                             (Obj.magic (elim_all g f mk ctxt' ()))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 ->
                                     match uu___1 with
                                     | (progress, FStar_Pervasives.Mkdtuple4
                                        (g', ctxt'', ctxt''_typing, k')) ->
                                         (progress,
                                           (FStar_Pervasives.Mkdtuple4
                                              (g', ctxt'', (),
                                                (k_elab_trans g g g' ctxt
                                                   ctxt' ctxt'' k k'))))))))
                   uu___)
let rec (add_elims :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (Pulse_Syntax_Base.vprop ->
         (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
        ->
        mk_t ->
          unit ->
            ((Pulse_Typing_Env.env, Pulse_Syntax_Base.term, unit,
               (unit, unit, unit, unit) continuation_elaborator)
               FStar_Pervasives.dtuple4,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun f ->
        fun mk ->
          fun ctxt_typing ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                       (Prims.of_int (330)) (Prims.of_int (25))
                       (Prims.of_int (330)) (Prims.of_int (55)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                       (Prims.of_int (330)) (Prims.of_int (4))
                       (Prims.of_int (337)) (Prims.of_int (6)))))
              (Obj.magic (add_elims_aux g ctxt f mk ()))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | (progress, res) ->
                        if Prims.op_Negation progress
                        then
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 -> res)))
                        else
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Prover.Common.fst"
                                           (Prims.of_int (334))
                                           (Prims.of_int (45))
                                           (Prims.of_int (334))
                                           (Prims.of_int (48)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Prover.Common.fst"
                                           (Prims.of_int (333))
                                           (Prims.of_int (10))
                                           (Prims.of_int (337))
                                           (Prims.of_int (6)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> res))
                                  (fun uu___2 ->
                                     (fun uu___2 ->
                                        match uu___2 with
                                        | FStar_Pervasives.Mkdtuple4
                                            (g', ctxt', ctxt'_typing, k) ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Prover.Common.fst"
                                                          (Prims.of_int (335))
                                                          (Prims.of_int (49))
                                                          (Prims.of_int (335))
                                                          (Prims.of_int (76)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Prover.Common.fst"
                                                          (Prims.of_int (334))
                                                          (Prims.of_int (51))
                                                          (Prims.of_int (336))
                                                          (Prims.of_int (57)))))
                                                 (Obj.magic
                                                    (add_elims g' ctxt' f mk
                                                       ()))
                                                 (fun uu___3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 ->
                                                         match uu___3 with
                                                         | FStar_Pervasives.Mkdtuple4
                                                             (g'', ctxt'',
                                                              ctxt''_typing,
                                                              k')
                                                             ->
                                                             FStar_Pervasives.Mkdtuple4
                                                               (g'', ctxt'',
                                                                 (),
                                                                 (k_elab_trans
                                                                    g g' g''
                                                                    ctxt
                                                                    ctxt'
                                                                    ctxt'' k
                                                                    k'))))))
                                       uu___2)))) uu___)
type preamble =
  {
  g0: Pulse_Typing_Env.env ;
  ctxt: Pulse_Syntax_Base.vprop ;
  ctxt_typing: unit ;
  goals: Pulse_Syntax_Base.vprop }
let (__proj__Mkpreamble__item__g0 : preamble -> Pulse_Typing_Env.env) =
  fun projectee ->
    match projectee with | { g0; ctxt; ctxt_typing; goals;_} -> g0
let (__proj__Mkpreamble__item__ctxt : preamble -> Pulse_Syntax_Base.vprop) =
  fun projectee ->
    match projectee with | { g0; ctxt; ctxt_typing; goals;_} -> ctxt

let (__proj__Mkpreamble__item__goals : preamble -> Pulse_Syntax_Base.vprop) =
  fun projectee ->
    match projectee with | { g0; ctxt; ctxt_typing; goals;_} -> goals
let (op_Array_Access :
  Pulse_Prover_Substs.t -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  = fun ss -> fun t -> Pulse_Prover_Substs.subst_term t ss
let (op_Star :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.vprop -> Pulse_Syntax_Base.term)
  = Pulse_Syntax_Base.tm_star
type ('ss, 'uvs, 'g) well_typed_ss = unit
type 'preamble1 prover_state =
  {
  pg: Pulse_Typing_Env.env ;
  remaining_ctxt: Pulse_Syntax_Base.vprop Prims.list ;
  uvs: Pulse_Typing_Env.env ;
  ss: Pulse_Prover_Substs.t ;
  solved: Pulse_Syntax_Base.vprop ;
  unsolved: Pulse_Syntax_Base.vprop Prims.list ;
  k: (unit, unit, unit, unit) continuation_elaborator ;
  goals_inv: unit ;
  solved_inv: unit }
let (__proj__Mkprover_state__item__pg :
  preamble -> unit prover_state -> Pulse_Typing_Env.env) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> pg
let (__proj__Mkprover_state__item__remaining_ctxt :
  preamble -> unit prover_state -> Pulse_Syntax_Base.vprop Prims.list) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> remaining_ctxt
let (__proj__Mkprover_state__item__uvs :
  preamble -> unit prover_state -> Pulse_Typing_Env.env) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> uvs
let (__proj__Mkprover_state__item__ss :
  preamble -> unit prover_state -> Pulse_Prover_Substs.t) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> ss
let (__proj__Mkprover_state__item__solved :
  preamble -> unit prover_state -> Pulse_Syntax_Base.vprop) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> solved
let (__proj__Mkprover_state__item__unsolved :
  preamble -> unit prover_state -> Pulse_Syntax_Base.vprop Prims.list) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> unsolved
let (__proj__Mkprover_state__item__k :
  preamble ->
    unit prover_state -> (unit, unit, unit, unit) continuation_elaborator)
  =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> k
type ('preamble1, 'st) is_terminal = unit
let (prove :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              ((Pulse_Typing_Env.env, Pulse_Prover_Substs.t,
                 Pulse_Syntax_Base.vprop,
                 (unit, unit, unit, unit) continuation_elaborator)
                 FStar_Pervasives.dtuple4,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun ctxt ->
                   fun ctxt_typing ->
                     fun uvs ->
                       fun goals ->
                         fun goals_typing ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> Prims.magic ()))) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___
let (check_stapp_no_ctxt :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      ((Pulse_Typing_Env.env, Pulse_Syntax_Base.st_term,
         Pulse_Syntax_Base.comp_st,
         (unit, unit, unit) Pulse_Typing.st_typing) FStar_Pervasives.dtuple4,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Prims.magic ())))
        uu___1 uu___
let (extend_post_hint_opt_g :
  Pulse_Typing_Env.env ->
    unit Pulse_Checker_Common.post_hint_opt ->
      Pulse_Typing_Env.env -> unit Pulse_Checker_Common.post_hint_opt)
  =
  fun g ->
    fun post_hint ->
      fun g1 ->
        match post_hint with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some post_hint1 ->
            FStar_Pervasives_Native.Some post_hint1
let (add_frame :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.vprop ->
            ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
               (unit, unit, unit) Pulse_Typing.st_typing)
               FStar_Pervasives.dtuple3,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun g ->
               fun t ->
                 fun c ->
                   fun t_typing ->
                     fun frame ->
                       Obj.magic
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> Prims.magic ()))) uu___4 uu___3
              uu___2 uu___1 uu___
let (st_typing_subst :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp_st ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Prover_Substs.t ->
              ((unit, unit, unit) Pulse_Typing.st_typing
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun uvs ->
      fun t ->
        fun c ->
          fun d ->
            fun ss ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                         (Prims.of_int (163)) (Prims.of_int (8))
                         (Prims.of_int (163)) (Prims.of_int (40)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                         (Prims.of_int (164)) Prims.int_zero
                         (Prims.of_int (169)) (Prims.of_int (11)))))
                (Obj.magic
                   (Pulse_Prover_Substs.check_well_typedness g uvs ss))
                (fun b ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        if Prims.op_Negation b
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            (Pulse_Prover_Substs.st_typing_nt_substs g uvs
                               (Pulse_Typing_Env.mk_env
                                  (Pulse_Typing_Env.fstar_env g)) t c d
                               (Pulse_Prover_Substs.as_nt_substs ss))))
let (st_typing_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp_st ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Typing_Env.env ->
              ((unit, unit, unit) Pulse_Typing.st_typing, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun g' ->
                   fun t ->
                     fun c ->
                       fun uu___ ->
                         fun g1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> Prims.magic ()))) uu___5
                uu___4 uu___3 uu___2 uu___1 uu___
let (mk_bind' :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            Pulse_Syntax_Base.comp_st ->
              Pulse_Syntax_Base.nvar ->
                (unit, unit, unit) Pulse_Typing.st_typing ->
                  unit ->
                    (unit, unit, unit) Pulse_Typing.st_typing ->
                      unit Pulse_Checker_Common.post_hint_opt ->
                        unit ->
                          ((unit, unit, unit)
                             Pulse_Checker_Common.checker_result_t,
                            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___11 ->
    fun uu___10 ->
      fun uu___9 ->
        fun uu___8 ->
          fun uu___7 ->
            fun uu___6 ->
              fun uu___5 ->
                fun uu___4 ->
                  fun uu___3 ->
                    fun uu___2 ->
                      fun uu___1 ->
                        fun uu___ ->
                          (fun g ->
                             fun pre ->
                               fun e1 ->
                                 fun e2 ->
                                   fun c1 ->
                                     fun c2 ->
                                       fun px ->
                                         fun d_e1 ->
                                           fun d_c1res ->
                                             fun d_e2 ->
                                               fun post_hint ->
                                                 fun uu___ ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           Prims.magic ())))
                            uu___11 uu___10 uu___9 uu___8 uu___7 uu___6
                            uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (check_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Checker_Common.post_hint_opt ->
            Pulse_Checker_Common.check_t ->
              ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun check ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                         (Prims.of_int (209)) (Prims.of_int (47))
                         (Prims.of_int (209)) (Prims.of_int (53)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                         (Prims.of_int (207)) (Prims.of_int (46))
                         (Prims.of_int (258)) (Prims.of_int (47)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> t.Pulse_Syntax_Base.term1))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax_Base.Tm_Bind
                          { Pulse_Syntax_Base.binder = b;
                            Pulse_Syntax_Base.head1 = e1;
                            Pulse_Syntax_Base.body1 = e2;_}
                          ->
                          (match e1.Pulse_Syntax_Base.term1 with
                           | Pulse_Syntax_Base.Tm_STApp uu___1 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Prover.Common.fsti"
                                             (Prims.of_int (213))
                                             (Prims.of_int (33))
                                             (Prims.of_int (213))
                                             (Prims.of_int (57)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Prover.Common.fsti"
                                             (Prims.of_int (212))
                                             (Prims.of_int (17))
                                             (Prims.of_int (256))
                                             (Prims.of_int (21)))))
                                    (Obj.magic (check_stapp_no_ctxt g e1))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          match uu___2 with
                                          | FStar_Pervasives.Mkdtuple4
                                              (uvs1, e11, c1, d1) ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Prover.Common.fsti"
                                                            (Prims.of_int (214))
                                                            (Prims.of_int (14))
                                                            (Prims.of_int (214))
                                                            (Prims.of_int (16)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Prover.Common.fsti"
                                                            (Prims.of_int (214))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (256))
                                                            (Prims.of_int (21)))))
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 -> c1))
                                                   (fun uu___3 ->
                                                      (fun c10 ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (53)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                              (Obj.magic
                                                                 (prove g pre
                                                                    () uvs1
                                                                    (
                                                                    Pulse_Syntax_Base.comp_pre
                                                                    c1) ()))
                                                              (fun uu___3 ->
                                                                 (fun uu___3
                                                                    ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g1, ss1,
                                                                    remaining_pre,
                                                                    k) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ((b.Pulse_Syntax_Base.binder_ppname),
                                                                    x)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    b.Pulse_Syntax_Base.binder_ppname
                                                                    (op_Array_Access
                                                                    ss1
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun g2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    op_Star
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (op_Array_Access
                                                                    ss1
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c1)) px)
                                                                    remaining_pre))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    pre_e2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    (check g2
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px)
                                                                    pre_e2 ()
                                                                    (extend_post_hint_opt_g
                                                                    g
                                                                    post_hint
                                                                    g2)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e21, c2,
                                                                    d2) ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.stateful_comp
                                                                    c2)
                                                                    then
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    "Bind: c2 is not st")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    (st_typing_weakening
                                                                    g uvs1
                                                                    e11 c1 d1
                                                                    g1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    (st_typing_subst
                                                                    g1 uvs1
                                                                    e11 c1
                                                                    d11 ss1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    d1opt ->
                                                                    if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    d1opt
                                                                    then
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    "Bind: could not find a well-typed substitution")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    d1opt))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    d12 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    (add_frame
                                                                    g1
                                                                    (Pulse_Prover_Substs.subst_st_term
                                                                    e11 ss1)
                                                                    (Pulse_Prover_Substs.subst_comp
                                                                    c1 ss1)
                                                                    d12
                                                                    remaining_pre))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e12,
                                                                    c11, d13)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    e21 x))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    e2_closed
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    coerce_eq
                                                                    d13 ()))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun d14
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    coerce_eq
                                                                    d2 ()))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun d21
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    (mk_bind'
                                                                    g1
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c11) e12
                                                                    e2_closed
                                                                    c11 c2 px
                                                                    d14 ()
                                                                    d21
                                                                    post_hint
                                                                    ()))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (k
                                                                    post_hint
                                                                    r))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                   uu___3)))
                                                        uu___3))) uu___2))
                           | uu___1 ->
                               Obj.magic
                                 (Pulse_Typing_Env.fail g
                                    FStar_Pervasives_Native.None
                                    "Bind: e1 is not an stapp"))) uu___)
type ('ss1, 'ss2) ss_extends = unit
type ('preamble1, 'pst1, 'pst2) pst_extends = unit
type prover_t =
  preamble ->
    unit prover_state ->
      (unit prover_state, unit) FStar_Tactics_Effect.tac_repr
let (k_intro_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.binder ->
        Pulse_Syntax_Base.vprop ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.vprop ->
              ((unit, unit, unit, unit) continuation_elaborator, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun u ->
                   fun b ->
                     fun p ->
                       fun e ->
                         fun frame ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> Prims.magic ()))) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___
let (intro_exists :
  preamble ->
    unit prover_state ->
      Pulse_Syntax_Base.universe ->
        Pulse_Syntax_Base.binder ->
          Pulse_Syntax_Base.vprop ->
            Pulse_Syntax_Base.vprop Prims.list ->
              unit ->
                prover_t ->
                  (unit prover_state, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun preamble1 ->
    fun pst ->
      fun u ->
        fun b ->
          fun body ->
            fun unsolved' ->
              fun uu___ ->
                fun prover ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                             (Prims.of_int (290)) (Prims.of_int (10))
                             (Prims.of_int (290)) (Prims.of_int (22)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                             (Prims.of_int (290)) (Prims.of_int (25))
                             (Prims.of_int (459)) (Prims.of_int (6)))))
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> Pulse_Typing_Env.fresh pst.pg))
                    (fun uu___1 ->
                       (fun x ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Prover.Common.fsti"
                                        (Prims.of_int (291))
                                        (Prims.of_int (11))
                                        (Prims.of_int (291))
                                        (Prims.of_int (29)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Prover.Common.fsti"
                                        (Prims.of_int (291))
                                        (Prims.of_int (32))
                                        (Prims.of_int (459))
                                        (Prims.of_int (6)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     ((b.Pulse_Syntax_Base.binder_ppname), x)))
                               (fun uu___1 ->
                                  (fun px ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Prover.Common.fsti"
                                                   (Prims.of_int (293))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (296))
                                                   (Prims.of_int (74)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Prover.Common.fsti"
                                                   (Prims.of_int (298))
                                                   (Prims.of_int (37))
                                                   (Prims.of_int (459))
                                                   (Prims.of_int (6)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                {
                                                  g0 = (pst.pg);
                                                  ctxt =
                                                    (op_Star
                                                       (Pulse_Checker_VPropEquiv.list_as_vprop
                                                          pst.remaining_ctxt)
                                                       (op_Array_Access
                                                          pst.ss pst.solved));
                                                  ctxt_typing = ();
                                                  goals =
                                                    (op_Star
                                                       (op_Star pst.solved
                                                          (Pulse_Syntax_Naming.open_term_nv
                                                             body px))
                                                       (Pulse_Checker_VPropEquiv.list_as_vprop
                                                          unsolved'))
                                                }))
                                          (fun uu___1 ->
                                             (fun preamble_sub ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Prover.Common.fsti"
                                                              (Prims.of_int (300))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (308))
                                                              (Prims.of_int (20)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Prover.Common.fsti"
                                                              (Prims.of_int (309))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (459))
                                                              (Prims.of_int (6)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           {
                                                             pg = (pst.pg);
                                                             remaining_ctxt =
                                                               (Pulse_Checker_VPropEquiv.vprop_as_list
                                                                  preamble_sub.ctxt);
                                                             uvs = (pst.uvs);
                                                             ss = (pst.ss);
                                                             solved =
                                                               Pulse_Syntax_Base.tm_emp;
                                                             unsolved =
                                                               (FStar_List_Tot_Base.append
                                                                  (Pulse_Checker_VPropEquiv.vprop_as_list
                                                                    (op_Array_Access
                                                                    pst.ss
                                                                    pst.solved))
                                                                  (FStar_List_Tot_Base.append
                                                                    [
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    body px]
                                                                    unsolved'));
                                                             k =
                                                               (Prims.magic
                                                                  ());
                                                             goals_inv = ();
                                                             solved_inv = ()
                                                           }))
                                                     (fun uu___1 ->
                                                        (fun pst_sub ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (39)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (6)))))
                                                                (Obj.magic
                                                                   (prover
                                                                    preamble_sub
                                                                    pst_sub))
                                                                (fun uu___1
                                                                   ->
                                                                   (fun
                                                                    pst_sub_terminal
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    pst_sub_terminal_goals_inv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    pst_sub_terminal_goals_inv1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    pst_sub_terminal.k))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub_terminal
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (12)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Prims.magic
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub_terminal1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    k_sub_terminal1))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub_terminal2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    op_Array_Access
                                                                    pst_sub_terminal.ss
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    witness
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Prims.magic
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub_terminal3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (k_intro_exists
                                                                    pst_sub_terminal.pg
                                                                    u
                                                                    (Pulse_Prover_Substs.nt_subst_binder
                                                                    b
                                                                    (Pulse_Prover_Substs.as_nt_substs
                                                                    pst_sub_terminal.ss))
                                                                    (op_Array_Access
                                                                    pst_sub_terminal.ss
                                                                    body)
                                                                    witness
                                                                    (op_Star
                                                                    (op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub_terminal.remaining_ctxt)
                                                                    (op_Array_Access
                                                                    pst_sub_terminal.ss
                                                                    pst.solved))
                                                                    (op_Array_Access
                                                                    pst_sub_terminal.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))))
                                                                    (fun
                                                                    k_intro_exists1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    {
                                                                    pg =
                                                                    (pst_sub_terminal.pg);
                                                                    remaining_ctxt
                                                                    =
                                                                    (pst_sub_terminal.remaining_ctxt);
                                                                    uvs =
                                                                    (pst_sub_terminal.uvs);
                                                                    ss =
                                                                    (pst_sub_terminal.ss);
                                                                    solved =
                                                                    (preamble1.goals);
                                                                    unsolved
                                                                    = [];
                                                                    k =
                                                                    (Prims.magic
                                                                    ());
                                                                    goals_inv
                                                                    = ();
                                                                    solved_inv
                                                                    = ()
                                                                    }))))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                          uu___1))) uu___1)))
                                    uu___1))) uu___1)
let (try_match_pq :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.vprop ->
        unit ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              ((Pulse_Prover_Substs.t, unit) Prims.dtuple2
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun uvs ->
                   fun p ->
                     fun p_typing ->
                       fun q ->
                         fun q_typing ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> Prims.magic ()))) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___
let (compose_ss :
  Pulse_Prover_Substs.t -> Pulse_Prover_Substs.t -> Pulse_Prover_Substs.t) =
  fun ss1 -> fun ss2 -> Prims.magic ()
let (match_step :
  preamble ->
    unit prover_state ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop Prims.list ->
          Pulse_Syntax_Base.vprop ->
            Pulse_Syntax_Base.vprop Prims.list ->
              unit ->
                (unit prover_state FStar_Pervasives_Native.option, unit)
                  FStar_Tactics_Effect.tac_repr)
  =
  fun preamble1 ->
    fun pst ->
      fun p ->
        fun remaining_ctxt' ->
          fun q ->
            fun unsolved' ->
              fun uu___ ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                           (Prims.of_int (477)) (Prims.of_int (11))
                           (Prims.of_int (477)) (Prims.of_int (21)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                           (Prims.of_int (478)) (Prims.of_int (52))
                           (Prims.of_int (540)) (Prims.of_int (11)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 -> op_Array_Access pst.ss q))
                  (fun uu___1 ->
                     (fun q_ss ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Prover.Common.fsti"
                                      (Prims.of_int (480))
                                      (Prims.of_int (11))
                                      (Prims.of_int (480))
                                      (Prims.of_int (69)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Prover.Common.fsti"
                                      (Prims.of_int (481)) Prims.int_zero
                                      (Prims.of_int (540))
                                      (Prims.of_int (11)))))
                             (Obj.magic
                                (try_match_pq pst.pg pst.uvs p () q_ss ()))
                             (fun ropt ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     match ropt with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.Some
                                         (Prims.Mkdtuple2 (ss_q, veq)) ->
                                         FStar_Pervasives_Native.Some
                                           {
                                             pg = (pst.pg);
                                             remaining_ctxt = remaining_ctxt';
                                             uvs = (pst.uvs);
                                             ss = (compose_ss ss_q pst.ss);
                                             solved = (op_Star q pst.solved);
                                             unsolved = unsolved';
                                             k = (Prims.magic ());
                                             goals_inv = ();
                                             solved_inv = ()
                                           })))) uu___1)