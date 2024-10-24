open Prims
let rec (vprop_as_list :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term Prims.list) =
  fun vp ->
    match vp with
    | Pulse_Syntax_Base.Tm_Emp -> []
    | Pulse_Syntax_Base.Tm_Star (vp0, vp1) ->
        FStar_List_Tot_Base.op_At (vprop_as_list vp0) (vprop_as_list vp1)
    | uu___ -> [vp]
let rec (list_as_vprop :
  Pulse_Syntax_Base.term Prims.list -> Pulse_Syntax_Base.term) =
  fun vps ->
    match vps with
    | [] -> Pulse_Syntax_Base.Tm_Emp
    | hd::tl -> Pulse_Syntax_Base.Tm_Star (hd, (list_as_vprop tl))
type framing_failure =
  {
  unmatched_preconditions: Pulse_Syntax_Base.term Prims.list ;
  remaining_context: Pulse_Syntax_Base.term Prims.list }
let (__proj__Mkframing_failure__item__unmatched_preconditions :
  framing_failure -> Pulse_Syntax_Base.term Prims.list) =
  fun projectee ->
    match projectee with
    | { unmatched_preconditions; remaining_context;_} ->
        unmatched_preconditions
let (__proj__Mkframing_failure__item__remaining_context :
  framing_failure -> Pulse_Syntax_Base.term Prims.list) =
  fun projectee ->
    match projectee with
    | { unmatched_preconditions; remaining_context;_} -> remaining_context
let (canon_vprop : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term) =
  fun vp -> list_as_vprop (vprop_as_list vp)
let (equational : Pulse_Syntax_Base.term -> Prims.bool) =
  fun t ->
    match t with
    | Pulse_Syntax_Base.Tm_FStar (host_term, uu___) ->
        (match FStar_Reflection_Builtins.inspect_ln host_term with
         | FStar_Reflection_Data.Tv_Match (uu___1, uu___2, uu___3) -> true
         | uu___1 -> false)
    | uu___ -> false
let (check_one_vprop :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (unit FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun p ->
             fun q ->
               if Pulse_Syntax_Base.eq_tm p q
               then
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ -> FStar_Pervasives_Native.Some ())))
               else
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                            (Prims.of_int (129)) (Prims.of_int (6))
                            (Prims.of_int (131)) (Prims.of_int (44)))
                         (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                            (Prims.of_int (133)) (Prims.of_int (4))
                            (Prims.of_int (140)) (Prims.of_int (13)))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               match ((Pulse_Syntax_Pure.is_pure_app p),
                                       (Pulse_Syntax_Pure.is_pure_app q))
                               with
                               | (FStar_Pervasives_Native.Some
                                  (hd_p, uu___2, uu___3),
                                  FStar_Pervasives_Native.Some
                                  (hd_q, uu___4, uu___5)) ->
                                   Pulse_Syntax_Base.eq_tm hd_p hd_q
                               | (uu___2, uu___3) ->
                                   (equational p) || (equational q)))
                         (fun uu___1 ->
                            (fun check_extensional_equality ->
                               if check_extensional_equality
                               then
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Framing.fst"
                                            (Prims.of_int (135))
                                            (Prims.of_int (15))
                                            (Prims.of_int (135))
                                            (Prims.of_int (26)))
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Framing.fst"
                                            (Prims.of_int (135))
                                            (Prims.of_int (29))
                                            (Prims.of_int (139))
                                            (Prims.of_int (23)))
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___1 ->
                                               Pulse_Elaborate_Pure.elab_term
                                                 p))
                                         (fun uu___1 ->
                                            (fun v0 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Framing.fst"
                                                       (Prims.of_int (136))
                                                       (Prims.of_int (15))
                                                       (Prims.of_int (136))
                                                       (Prims.of_int (26)))
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Framing.fst"
                                                       (Prims.of_int (137))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (139))
                                                       (Prims.of_int (23)))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          Pulse_Elaborate_Pure.elab_term
                                                            q))
                                                    (fun uu___1 ->
                                                       (fun v1 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Framing.fst"
                                                                  (Prims.of_int (137))
                                                                  (Prims.of_int (12))
                                                                  (Prims.of_int (137))
                                                                  (Prims.of_int (44)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Framing.fst"
                                                                  (Prims.of_int (137))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (139))
                                                                  (Prims.of_int (23)))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Builtins.check_equiv
                                                                    (Pulse_Typing.elab_env
                                                                    g) v0 v1))
                                                               (fun uu___1 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    token,
                                                                    uu___3)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ()
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    uu___3)
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                         uu___1))) uu___1)))
                               else
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            FStar_Pervasives_Native.None))))
                              uu___1)))) uu___2 uu___1 uu___
type ('g, 'p, 'qs) split_one_vprop_res =
  (Pulse_Syntax_Base.term Prims.list, Pulse_Syntax_Base.term, unit,
    Pulse_Syntax_Base.term Prims.list) FStar_Pervasives.dtuple4
    FStar_Pervasives_Native.option
let rec (maybe_split_one_vprop :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term Prims.list ->
        ((unit, unit, unit) split_one_vprop_res, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun p ->
             fun qs ->
               match qs with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> FStar_Pervasives_Native.None)))
               | q::qs1 ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                              (Prims.of_int (155)) (Prims.of_int (18))
                              (Prims.of_int (155)) (Prims.of_int (39)))
                           (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                              (Prims.of_int (156)) (Prims.of_int (6))
                              (Prims.of_int (160)) (Prims.of_int (64)))
                           (Obj.magic (check_one_vprop g p q))
                           (fun uu___ ->
                              (fun d_opt ->
                                 if
                                   FStar_Pervasives_Native.uu___is_Some d_opt
                                 then
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___ ->
                                              FStar_Pervasives_Native.Some
                                                (FStar_Pervasives.Mkdtuple4
                                                   ([], q, (), qs1)))))
                                 else
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Framing.fst"
                                              (Prims.of_int (158))
                                              (Prims.of_int (17))
                                              (Prims.of_int (158))
                                              (Prims.of_int (45)))
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Framing.fst"
                                              (Prims.of_int (158))
                                              (Prims.of_int (11))
                                              (Prims.of_int (160))
                                              (Prims.of_int (64)))
                                           (Obj.magic
                                              (maybe_split_one_vprop g p qs1))
                                           (fun uu___1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   match uu___1 with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       FStar_Pervasives_Native.None
                                                   | FStar_Pervasives_Native.Some
                                                       (FStar_Pervasives.Mkdtuple4
                                                       (l, q', d, r)) ->
                                                       FStar_Pervasives_Native.Some
                                                         (FStar_Pervasives.Mkdtuple4
                                                            ((q :: l), q',
                                                              (), r)))))))
                                uu___)))) uu___2 uu___1 uu___
type ('g, 'req, 'ctxt) framing_success =
  (Pulse_Syntax_Base.term Prims.list, unit) Prims.dtuple2
type ('g, 'req, 'ctxt) try_frame_result =
  ((unit, unit, unit) framing_success, framing_failure)
    FStar_Pervasives.either
let (mk_framing_failure :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term Prims.list ->
      Pulse_Syntax_Base.term Prims.list ->
        Pulse_Syntax_Base.term Prims.list ->
          Pulse_Syntax_Base.term Prims.list ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit) try_frame_result ->
                (unit, unit, unit) try_frame_result)
  =
  fun g ->
    fun req ->
      fun req' ->
        fun ctxt ->
          fun ctxt' ->
            fun unmatched_pre ->
              fun res ->
                match res with
                | FStar_Pervasives.Inr failure ->
                    FStar_Pervasives.Inr
                      {
                        unmatched_preconditions = (unmatched_pre ::
                          (failure.unmatched_preconditions));
                        remaining_context = (failure.remaining_context)
                      }
                | FStar_Pervasives.Inl (Prims.Mkdtuple2 (frame, uu___)) ->
                    FStar_Pervasives.Inr
                      {
                        unmatched_preconditions = [unmatched_pre];
                        remaining_context = frame
                      }
let rec (try_split_vprop :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term Prims.list ->
      Pulse_Syntax_Base.term Prims.list ->
        (((Pulse_Syntax_Base.term Prims.list, unit) Prims.dtuple2,
           framing_failure) FStar_Pervasives.either,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun req ->
             fun ctxt ->
               match req with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ ->
                              FStar_Pervasives.Inl
                                (Prims.Mkdtuple2 (ctxt, ())))))
               | hd::tl ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                              (Prims.of_int (213)) (Prims.of_int (12))
                              (Prims.of_int (213)) (Prims.of_int (43)))
                           (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                              (Prims.of_int (213)) (Prims.of_int (6))
                              (Prims.of_int (236)) (Prims.of_int (30)))
                           (Obj.magic (maybe_split_one_vprop g hd ctxt))
                           (fun uu___ ->
                              (fun uu___ ->
                                 match uu___ with
                                 | FStar_Pervasives_Native.None ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (214))
                                             (Prims.of_int (38))
                                             (Prims.of_int (214))
                                             (Prims.of_int (65)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (214))
                                             (Prims.of_int (16))
                                             (Prims.of_int (214))
                                             (Prims.of_int (65)))
                                          (Obj.magic
                                             (try_split_vprop g tl ctxt))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  mk_framing_failure g tl req
                                                    ctxt ctxt hd uu___1)))
                                 | FStar_Pervasives_Native.Some
                                     (FStar_Pervasives.Mkdtuple4
                                     (l, q, d, r)) ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (220))
                                             (Prims.of_int (12))
                                             (Prims.of_int (220))
                                             (Prims.of_int (47)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (222))
                                             (Prims.of_int (8))
                                             (Prims.of_int (236))
                                             (Prims.of_int (30)))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 -> ()))
                                          (fun uu___1 ->
                                             (fun d1 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Framing.fst"
                                                        (Prims.of_int (222))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (222))
                                                        (Prims.of_int (42)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Framing.fst"
                                                        (Prims.of_int (222))
                                                        (Prims.of_int (8))
                                                        (Prims.of_int (236))
                                                        (Prims.of_int (30)))
                                                     (Obj.magic
                                                        (try_split_vprop g tl
                                                           (FStar_List_Tot_Base.op_At
                                                              l r)))
                                                     (fun uu___1 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             match uu___1
                                                             with
                                                             | FStar_Pervasives.Inr
                                                                 failure ->
                                                                 FStar_Pervasives.Inr
                                                                   failure
                                                             | FStar_Pervasives.Inl
                                                                 (Prims.Mkdtuple2
                                                                 (frame, d2))
                                                                 ->
                                                                 FStar_Pervasives.Inl
                                                                   (Prims.Mkdtuple2
                                                                    (frame,
                                                                    ()))))))
                                               uu___1))) uu___)))) uu___2
          uu___1 uu___
let (split_vprop :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.term ->
          (((Pulse_Syntax_Base.term, unit, unit) FStar_Pervasives.dtuple3,
             framing_failure) FStar_Pervasives.either,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun req ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
               (Prims.of_int (246)) (Prims.of_int (18)) (Prims.of_int (246))
               (Prims.of_int (36)))
            (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
               (Prims.of_int (246)) (Prims.of_int (39)) (Prims.of_int (274))
               (Prims.of_int (47)))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> vprop_as_list ctxt))
            (fun uu___ ->
               (fun ctxt_l ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                          (Prims.of_int (247)) (Prims.of_int (17))
                          (Prims.of_int (247)) (Prims.of_int (34)))
                       (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                          (Prims.of_int (248)) (Prims.of_int (5))
                          (Prims.of_int (274)) (Prims.of_int (47)))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ -> vprop_as_list req))
                       (fun uu___ ->
                          (fun req_l ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Framing.fst"
                                     (Prims.of_int (248)) (Prims.of_int (11))
                                     (Prims.of_int (248)) (Prims.of_int (41)))
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Framing.fst"
                                     (Prims.of_int (248)) (Prims.of_int (5))
                                     (Prims.of_int (274)) (Prims.of_int (47)))
                                  (Obj.magic (try_split_vprop g req_l ctxt_l))
                                  (fun uu___ ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 ->
                                          match uu___ with
                                          | FStar_Pervasives.Inr failure ->
                                              FStar_Pervasives.Inr failure
                                          | FStar_Pervasives.Inl
                                              (Prims.Mkdtuple2 (frame, veq))
                                              ->
                                              FStar_Pervasives.Inl
                                                (FStar_Pervasives.Mkdtuple3
                                                   ((list_as_vprop frame),
                                                     (), ())))))) uu___)))
                 uu___)
let rec (check_equiv_emp :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term -> unit FStar_Pervasives_Native.option)
  =
  fun g ->
    fun vp ->
      match vp with
      | Pulse_Syntax_Base.Tm_Emp -> FStar_Pervasives_Native.Some ()
      | Pulse_Syntax_Base.Tm_Star (vp1, vp2) ->
          (match ((check_equiv_emp g vp1), (check_equiv_emp g vp2)) with
           | (FStar_Pervasives_Native.Some d1, FStar_Pervasives_Native.Some
              d2) -> FStar_Pervasives_Native.Some ()
           | (uu___, uu___1) -> FStar_Pervasives_Native.None)
      | uu___ -> FStar_Pervasives_Native.None
let (check_vprop_equiv :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun vp1 ->
      fun vp2 ->
        fun vp1_typing ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
               (Prims.of_int (299)) (Prims.of_int (8)) (Prims.of_int (299))
               (Prims.of_int (40)))
            (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
               (Prims.of_int (299)) (Prims.of_int (2)) (Prims.of_int (325))
               (Prims.of_int (54))) (Obj.magic (split_vprop g vp1 () vp2))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | FStar_Pervasives.Inr failure ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Framing.fst"
                                 (Prims.of_int (301)) (Prims.of_int (11))
                                 (Prims.of_int (305)) (Prims.of_int (94)))
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Framing.fst"
                                 (Prims.of_int (301)) (Prims.of_int (4))
                                 (Prims.of_int (305)) (Prims.of_int (94)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Framing.fst"
                                       (Prims.of_int (305))
                                       (Prims.of_int (16))
                                       (Prims.of_int (305))
                                       (Prims.of_int (93)))
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Framing.fst"
                                       (Prims.of_int (301))
                                       (Prims.of_int (11))
                                       (Prims.of_int (305))
                                       (Prims.of_int (94)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (305))
                                             (Prims.of_int (36))
                                             (Prims.of_int (305))
                                             (Prims.of_int (92)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (305))
                                             (Prims.of_int (16))
                                             (Prims.of_int (305))
                                             (Prims.of_int (93)))
                                          (Obj.magic
                                             (FStar_Tactics_Util.map
                                                Pulse_Syntax_Printer.term_to_string
                                                failure.unmatched_preconditions))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  FStar_String.concat "\n"
                                                    uu___1))))
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Framing.fst"
                                                  (Prims.of_int (301))
                                                  (Prims.of_int (11))
                                                  (Prims.of_int (305))
                                                  (Prims.of_int (94)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Framing.fst"
                                                  (Prims.of_int (301))
                                                  (Prims.of_int (11))
                                                  (Prims.of_int (305))
                                                  (Prims.of_int (94)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Framing.fst"
                                                        (Prims.of_int (304))
                                                        (Prims.of_int (16))
                                                        (Prims.of_int (304))
                                                        (Prims.of_int (38)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Framing.fst"
                                                        (Prims.of_int (301))
                                                        (Prims.of_int (11))
                                                        (Prims.of_int (305))
                                                        (Prims.of_int (94)))
                                                     (Obj.magic
                                                        (Pulse_Syntax_Printer.term_to_string
                                                           vp2))
                                                     (fun uu___2 ->
                                                        (fun uu___2 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Framing.fst"
                                                                   (Prims.of_int (301))
                                                                   (Prims.of_int (11))
                                                                   (Prims.of_int (305))
                                                                   (Prims.of_int (94)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Framing.fst"
                                                                   (Prims.of_int (301))
                                                                   (Prims.of_int (11))
                                                                   (Prims.of_int (305))
                                                                   (Prims.of_int (94)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Framing.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (38)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    vp1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_vprop_equiv: "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " and "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " are not equivalent; missing preconditions:\n"))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                (fun uu___3
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                          uu___2)))
                                               (fun uu___2 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___3 ->
                                                       uu___2 uu___1))))
                                         uu___1)))
                              (fun uu___1 ->
                                 FStar_Tactics_Derived.fail uu___1)))
                  | FStar_Pervasives.Inl (FStar_Pervasives.Mkdtuple3
                      (frame, uu___1, d)) ->
                      Obj.magic
                        (Obj.repr
                           (match check_equiv_emp g frame with
                            | FStar_Pervasives_Native.Some d_frame_equiv_emp
                                ->
                                Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> ()))
                            | FStar_Pervasives_Native.None ->
                                Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Framing.fst"
                                        (Prims.of_int (322))
                                        (Prims.of_int (13))
                                        (Prims.of_int (325))
                                        (Prims.of_int (54)))
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Framing.fst"
                                        (Prims.of_int (322))
                                        (Prims.of_int (6))
                                        (Prims.of_int (325))
                                        (Prims.of_int (54)))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Framing.fst"
                                              (Prims.of_int (325))
                                              (Prims.of_int (29))
                                              (Prims.of_int (325))
                                              (Prims.of_int (53)))
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Framing.fst"
                                              (Prims.of_int (322))
                                              (Prims.of_int (13))
                                              (Prims.of_int (325))
                                              (Prims.of_int (54)))
                                           (Obj.magic
                                              (Pulse_Syntax_Printer.term_to_string
                                                 frame))
                                           (fun uu___2 ->
                                              (fun uu___2 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Framing.fst"
                                                         (Prims.of_int (322))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (325))
                                                         (Prims.of_int (54)))
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Framing.fst"
                                                         (Prims.of_int (322))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (325))
                                                         (Prims.of_int (54)))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Framing.fst"
                                                               (Prims.of_int (324))
                                                               (Prims.of_int (29))
                                                               (Prims.of_int (324))
                                                               (Prims.of_int (51)))
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Framing.fst"
                                                               (Prims.of_int (322))
                                                               (Prims.of_int (13))
                                                               (Prims.of_int (325))
                                                               (Prims.of_int (54)))
                                                            (Obj.magic
                                                               (Pulse_Syntax_Printer.term_to_string
                                                                  vp2))
                                                            (fun uu___3 ->
                                                               (fun uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Framing.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (54)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Framing.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (54)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Framing.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    vp1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_vprop_equiv: "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    " and "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " are not equivalent, frame: "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                 uu___3)))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              uu___3 uu___2))))
                                                uu___2)))
                                     (fun uu___2 ->
                                        FStar_Tactics_Derived.fail uu___2)))))
                 uu___)
let (try_frame_pre :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              (((Pulse_Syntax_Base.comp_st,
                  (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2,
                 framing_failure) FStar_Pervasives.either,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun c ->
            fun t_typing ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                   (Prims.of_int (343)) (Prims.of_int (12))
                   (Prims.of_int (343)) (Prims.of_int (29)))
                (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                   (Prims.of_int (344)) (Prims.of_int (4))
                   (Prims.of_int (362)) (Prims.of_int (29)))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Pulse_Syntax_Base.st_comp_of_comp c))
                (fun uu___ ->
                   (fun s ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                              (Prims.of_int (344)) (Prims.of_int (10))
                              (Prims.of_int (344)) (Prims.of_int (44)))
                           (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                              (Prims.of_int (344)) (Prims.of_int (4))
                              (Prims.of_int (362)) (Prims.of_int (29)))
                           (Obj.magic
                              (split_vprop g pre () s.Pulse_Syntax_Base.pre))
                           (fun uu___ ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   match uu___ with
                                   | FStar_Pervasives.Inr failure ->
                                       FStar_Pervasives.Inr failure
                                   | FStar_Pervasives.Inl
                                       (FStar_Pervasives.Mkdtuple3
                                       (frame, frame_typing, ve)) ->
                                       (match Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                g
                                                (Pulse_Syntax_Base.st_comp_of_comp
                                                   (Pulse_Typing.add_frame c
                                                      frame))
                                                (Pulse_Typing_Metatheory.comp_typing_inversion
                                                   g
                                                   (Pulse_Typing.add_frame c
                                                      frame)
                                                   (Pulse_Typing_Metatheory.st_typing_correctness
                                                      g t
                                                      (Pulse_Typing.add_frame
                                                         c frame)
                                                      (Pulse_Typing.T_Frame
                                                         (g, t, c, frame, (),
                                                           t_typing))))
                                        with
                                        | FStar_Pervasives.Mkdtuple4
                                            (res_typing, pre_typing1, x,
                                             post_typing)
                                            ->
                                            FStar_Pervasives.Inl
                                              (Prims.Mkdtuple2
                                                 ((Pulse_Syntax_Base.with_st_comp
                                                     (Pulse_Typing.add_frame
                                                        c frame)
                                                     {
                                                       Pulse_Syntax_Base.u =
                                                         ((Pulse_Syntax_Base.st_comp_of_comp
                                                             (Pulse_Typing.add_frame
                                                                c frame)).Pulse_Syntax_Base.u);
                                                       Pulse_Syntax_Base.res
                                                         =
                                                         ((Pulse_Syntax_Base.st_comp_of_comp
                                                             (Pulse_Typing.add_frame
                                                                c frame)).Pulse_Syntax_Base.res);
                                                       Pulse_Syntax_Base.pre
                                                         = pre;
                                                       Pulse_Syntax_Base.post
                                                         =
                                                         ((Pulse_Syntax_Base.st_comp_of_comp
                                                             (Pulse_Typing.add_frame
                                                                c frame)).Pulse_Syntax_Base.post)
                                                     }),
                                                   (Pulse_Typing.T_Equiv
                                                      (g, t,
                                                        (Pulse_Typing.add_frame
                                                           c frame),
                                                        (Pulse_Syntax_Base.with_st_comp
                                                           (Pulse_Typing.add_frame
                                                              c frame)
                                                           {
                                                             Pulse_Syntax_Base.u
                                                               =
                                                               ((Pulse_Syntax_Base.st_comp_of_comp
                                                                   (Pulse_Typing.add_frame
                                                                    c frame)).Pulse_Syntax_Base.u);
                                                             Pulse_Syntax_Base.res
                                                               =
                                                               ((Pulse_Syntax_Base.st_comp_of_comp
                                                                   (Pulse_Typing.add_frame
                                                                    c frame)).Pulse_Syntax_Base.res);
                                                             Pulse_Syntax_Base.pre
                                                               = pre;
                                                             Pulse_Syntax_Base.post
                                                               =
                                                               ((Pulse_Syntax_Base.st_comp_of_comp
                                                                   (Pulse_Typing.add_frame
                                                                    c frame)).Pulse_Syntax_Base.post)
                                                           }),
                                                        (Pulse_Typing.T_Frame
                                                           (g, t, c, frame,
                                                             (), t_typing)),
                                                        (Pulse_Typing.ST_VPropEquiv
                                                           (g,
                                                             (Pulse_Typing.add_frame
                                                                c frame),
                                                             (Pulse_Syntax_Base.with_st_comp
                                                                (Pulse_Typing.add_frame
                                                                   c frame)
                                                                {
                                                                  Pulse_Syntax_Base.u
                                                                    =
                                                                    (
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c frame)).Pulse_Syntax_Base.u);
                                                                  Pulse_Syntax_Base.res
                                                                    =
                                                                    (
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c frame)).Pulse_Syntax_Base.res);
                                                                  Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                  Pulse_Syntax_Base.post
                                                                    =
                                                                    (
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c frame)).Pulse_Syntax_Base.post)
                                                                }), x, (),
                                                             (), (), (), ())))))))))))
                     uu___)
let (frame_empty :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Syntax_Base.st_term ->
                Pulse_Syntax_Base.comp_st ->
                  (unit, unit, unit) Pulse_Typing.st_typing ->
                    ((Pulse_Syntax_Base.comp_st,
                       (unit, unit, unit) Pulse_Typing.st_typing)
                       Prims.dtuple2,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
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
                         fun pre_typing ->
                           fun u ->
                             fun ty ->
                               fun ut ->
                                 fun t ->
                                   fun c0 ->
                                     fun d ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___ ->
                                               match Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                       g
                                                       (Pulse_Syntax_Base.st_comp_of_comp
                                                          (Pulse_Typing.add_frame
                                                             c0 pre))
                                                       (Pulse_Typing_Metatheory.comp_typing_inversion
                                                          g
                                                          (Pulse_Typing.add_frame
                                                             c0 pre)
                                                          (Pulse_Typing_Metatheory.st_typing_correctness
                                                             g t
                                                             (Pulse_Typing.add_frame
                                                                c0 pre)
                                                             (Pulse_Typing.T_Frame
                                                                (g, t, c0,
                                                                  pre, (), d))))
                                               with
                                               | FStar_Pervasives.Mkdtuple4
                                                   (res_typing, pre_typing1,
                                                    x, post_typing)
                                                   ->
                                                   Prims.Mkdtuple2
                                                     ((Pulse_Syntax_Base.with_st_comp
                                                         (Pulse_Typing.add_frame
                                                            c0 pre)
                                                         {
                                                           Pulse_Syntax_Base.u
                                                             =
                                                             ((Pulse_Syntax_Base.st_comp_of_comp
                                                                 (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.u);
                                                           Pulse_Syntax_Base.res
                                                             =
                                                             ((Pulse_Syntax_Base.st_comp_of_comp
                                                                 (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.res);
                                                           Pulse_Syntax_Base.pre
                                                             = pre;
                                                           Pulse_Syntax_Base.post
                                                             =
                                                             ((Pulse_Syntax_Base.st_comp_of_comp
                                                                 (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.post)
                                                         }),
                                                       (Pulse_Typing.T_Equiv
                                                          (g, t,
                                                            (Pulse_Typing.add_frame
                                                               c0 pre),
                                                            (Pulse_Syntax_Base.with_st_comp
                                                               (Pulse_Typing.add_frame
                                                                  c0 pre)
                                                               {
                                                                 Pulse_Syntax_Base.u
                                                                   =
                                                                   ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.u);
                                                                 Pulse_Syntax_Base.res
                                                                   =
                                                                   ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.res);
                                                                 Pulse_Syntax_Base.pre
                                                                   = pre;
                                                                 Pulse_Syntax_Base.post
                                                                   =
                                                                   ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.post)
                                                               }),
                                                            (Pulse_Typing.T_Frame
                                                               (g, t, c0,
                                                                 pre, (), d)),
                                                            (Pulse_Typing.ST_VPropEquiv
                                                               (g,
                                                                 (Pulse_Typing.add_frame
                                                                    c0 pre),
                                                                 (Pulse_Syntax_Base.with_st_comp
                                                                    (
                                                                    Pulse_Typing.add_frame
                                                                    c0 pre)
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.res
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.res);
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.post)
                                                                    }), x,
                                                                 (), (), (),
                                                                 (), ()))))))))
                      uu___8 uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1
                      uu___