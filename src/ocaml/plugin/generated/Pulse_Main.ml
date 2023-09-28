open Prims
let (debug_main :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun s ->
           if
             Pulse_RuntimeUtils.debug_at_level (Pulse_Typing_Env.fstar_env g)
               "pulse.main"
           then
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (20)) (Prims.of_int (15))
                              (Prims.of_int (20)) (Prims.of_int (21)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (20)) (Prims.of_int (7))
                              (Prims.of_int (20)) (Prims.of_int (21)))))
                     (Obj.magic (s ()))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic (FStar_Tactics_V2_Builtins.print uu___))
                          uu___)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
let (main' :
  Prims.string ->
    Pulse_Syntax_Base.decl ->
      Pulse_Syntax_Base.term ->
        FStar_Reflection_Typing.fstar_top_env ->
          (unit FStar_Reflection_Typing.dsl_tac_result_t, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun nm ->
             fun d ->
               fun pre ->
                 fun g ->
                   match Pulse_Soundness_Common.check_top_level_environment g
                   with
                   | FStar_Pervasives_Native.None ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_V2_Derived.fail
                               "pulse main: top-level environment does not include stt at the expected types"))
                   | FStar_Pervasives_Native.Some g1 ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.Main.fst"
                                        (Prims.of_int (28))
                                        (Prims.of_int (6))
                                        (Prims.of_int (29))
                                        (Prims.of_int (88)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.Main.fst"
                                        (Prims.of_int (29))
                                        (Prims.of_int (89))
                                        (Prims.of_int (74))
                                        (Prims.of_int (11)))))
                               (if
                                  Pulse_RuntimeUtils.debug_at_level
                                    (Pulse_Typing_Env.fstar_env g1) "Pulse"
                                then
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (29))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (29))
                                                   (Prims.of_int (88)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (29))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (29))
                                                   (Prims.of_int (88)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Main.fst"
                                                         (Prims.of_int (29))
                                                         (Prims.of_int (67))
                                                         (Prims.of_int (29))
                                                         (Prims.of_int (87)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (Pulse_Syntax_Printer.decl_to_string
                                                      d))
                                                (fun uu___ ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___1 ->
                                                        Prims.strcat
                                                          "About to check pulse decl:\n"
                                                          (Prims.strcat uu___
                                                             "\n")))))
                                          (fun uu___ ->
                                             (fun uu___ ->
                                                Obj.magic
                                                  (FStar_Tactics_V2_Builtins.print
                                                     uu___)) uu___)))
                                else
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ()))))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (77)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (29))
                                                   (Prims.of_int (89))
                                                   (Prims.of_int (74))
                                                   (Prims.of_int (11)))))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.check_tot_term
                                                g1 pre))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | FStar_Pervasives.Mkdtuple3
                                                    (pre1, ty, pre_typing) ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Main.fst"
                                                                  (Prims.of_int (31))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (32))
                                                                  (Prims.of_int (80)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Main.fst"
                                                                  (Prims.of_int (32))
                                                                  (Prims.of_int (81))
                                                                  (Prims.of_int (74))
                                                                  (Prims.of_int (11)))))
                                                         (if
                                                            Prims.op_Negation
                                                              (Pulse_Syntax_Base.eq_tm
                                                                 ty
                                                                 Pulse_Syntax_Base.tm_vprop)
                                                          then
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    (pre1.Pulse_Syntax_Base.range1))
                                                                    "pulse main: cannot typecheck pre at type vprop"))
                                                          else
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    ()))))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (61)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (11)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    pre_typing1
                                                                    ->
                                                                    match d
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.FnDecl
                                                                    {
                                                                    Pulse_Syntax_Base.id
                                                                    = id;
                                                                    Pulse_Syntax_Base.isrec
                                                                    = isrec;
                                                                    Pulse_Syntax_Base.body5
                                                                    = body;_}
                                                                    ->
                                                                    (match 
                                                                    body.Pulse_Syntax_Base.term1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Abs
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    nm))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    nm_orig
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    if isrec
                                                                    then
                                                                    Prims.strcat
                                                                    "__recaux_"
                                                                    nm
                                                                    else nm))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun nm1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    body.Pulse_Syntax_Base.range2))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun rng
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Abs.check_abs
                                                                    g1 body
                                                                    Pulse_Checker.check))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    c,
                                                                    t_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    g1
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    body1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "\ncheck call returned in main with:\n"
                                                                    (Prims.strcat
                                                                    uu___6
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (debug_main
                                                                    g1
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Printer.print_st_typing
                                                                    g1 body1
                                                                    c
                                                                    t_typing))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    body1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "\nchecker call returned in main with:\n"
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "\nderivation="))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___8
                                                                    uu___7))))
                                                                    uu___7))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Elaborate_Pure.elab_comp
                                                                    c))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    refl_t ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_RuntimeUtils.embed_st_term_for_extraction
                                                                    body1
                                                                    (FStar_Pervasives_Native.Some
                                                                    rng)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    refl_e ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ("pulse",
                                                                    refl_e)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun blob
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (102)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (102)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.ext_getv
                                                                    "pulse:elab_derivation"))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7 <>
                                                                    ""))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    if uu___7
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Reflection_Typing.mk_checked_let
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g1) nm1
                                                                    (Pulse_Elaborate_Core.elab_st_typing
                                                                    g1 body1
                                                                    c
                                                                    t_typing)
                                                                    refl_t)
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Reflection_Util.mk_opaque_let
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g1) nm1
                                                                    () refl_t))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    main_decl
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match main_decl
                                                                    with
                                                                    | 
                                                                    (chk, se,
                                                                    uu___8)
                                                                    ->
                                                                    (chk, se,
                                                                    (FStar_Pervasives_Native.Some
                                                                    blob))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    main_decl1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (38)))))
                                                                    (if isrec
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Recursion.tie_knot
                                                                    g1 rng
                                                                    body1 c
                                                                    nm1
                                                                    nm_orig))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    []))))
                                                                    (fun
                                                                    recursive_decls
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    main_decl1
                                                                    ::
                                                                    recursive_decls))))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4))
                                                                    | 
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (body.Pulse_Syntax_Base.range2))
                                                                    "main: FnDecl body not a Tm_Abs")))
                                                                    uu___3)))
                                                              uu___2)))
                                               uu___1))) uu___)))) uu___3
            uu___2 uu___1 uu___
let (join_smt_goals : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (80))
               (Prims.of_int (2)) (Prims.of_int (81)) (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (81))
               (Prims.of_int (36)) (Prims.of_int (102)) (Prims.of_int (4)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (80))
                     (Prims.of_int (5)) (Prims.of_int (80))
                     (Prims.of_int (48)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (80))
                     (Prims.of_int (2)) (Prims.of_int (81))
                     (Prims.of_int (35)))))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (80)) (Prims.of_int (23))
                           (Prims.of_int (80)) (Prims.of_int (35)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (80)) (Prims.of_int (5))
                           (Prims.of_int (80)) (Prims.of_int (48)))))
                  (Obj.magic (FStar_Tactics_V2_Builtins.top_env ()))
                  (fun uu___1 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___2 ->
                          Pulse_RuntimeUtils.debug_at_level uu___1
                            "pulse.join"))))
            (fun uu___1 ->
               (fun uu___1 ->
                  if uu___1
                  then
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_V2_Builtins.dump
                            "PULSE: Goals before join"))
                  else
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> ())))) uu___1)))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (84)) (Prims.of_int (18))
                          (Prims.of_int (84)) (Prims.of_int (30)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (85)) (Prims.of_int (2))
                          (Prims.of_int (102)) (Prims.of_int (4)))))
                 (Obj.magic (FStar_Tactics_V2_Derived.smt_goals ()))
                 (fun uu___2 ->
                    (fun smt_goals ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (85)) (Prims.of_int (2))
                                     (Prims.of_int (85)) (Prims.of_int (34)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (86)) (Prims.of_int (2))
                                     (Prims.of_int (102)) (Prims.of_int (4)))))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (85))
                                           (Prims.of_int (12))
                                           (Prims.of_int (85))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (85))
                                           (Prims.of_int (2))
                                           (Prims.of_int (85))
                                           (Prims.of_int (34)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (85))
                                                 (Prims.of_int (13))
                                                 (Prims.of_int (85))
                                                 (Prims.of_int (21)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (85))
                                                 (Prims.of_int (12))
                                                 (Prims.of_int (85))
                                                 (Prims.of_int (34)))))
                                        (Obj.magic
                                           (FStar_Tactics_V2_Derived.goals ()))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                FStar_List_Tot_Base.op_At
                                                  uu___2 smt_goals))))
                                  (fun uu___2 ->
                                     (fun uu___2 ->
                                        Obj.magic
                                          (FStar_Tactics_V2_Builtins.set_goals
                                             uu___2)) uu___2)))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (86))
                                                (Prims.of_int (2))
                                                (Prims.of_int (86))
                                                (Prims.of_int (18)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (86))
                                                (Prims.of_int (19))
                                                (Prims.of_int (102))
                                                (Prims.of_int (4)))))
                                       (Obj.magic
                                          (FStar_Tactics_V2_Builtins.set_smt_goals
                                             []))
                                       (fun uu___3 ->
                                          (fun uu___3 ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (87))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (87))
                                                           (Prims.of_int (36)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (88))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (102))
                                                           (Prims.of_int (4)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Main.fst"
                                                                 (Prims.of_int (87))
                                                                 (Prims.of_int (26))
                                                                 (Prims.of_int (87))
                                                                 (Prims.of_int (36)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Main.fst"
                                                                 (Prims.of_int (87))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (87))
                                                                 (Prims.of_int (36)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_V2_Derived.goals
                                                              ()))
                                                        (fun uu___4 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___5 ->
                                                                FStar_List_Tot_Base.length
                                                                  uu___4))))
                                                  (fun uu___4 ->
                                                     (fun n ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (22)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (4)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (22)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (22)))))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.repeat
                                                                    FStar_Tactics_V2_Builtins.join))
                                                                   (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ()))))
                                                             (fun uu___4 ->
                                                                (fun uu___4
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (4)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.goals
                                                                    ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.uu___is_Nil
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.op_Negation
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    if uu___5
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_SMT.get_rlimit
                                                                    ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6 +
                                                                    ((n -
                                                                    Prims.int_one)
                                                                    *
                                                                    (Prims.of_int (2)))))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    rlimit ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_SMT.set_rlimit
                                                                    rlimit))
                                                                    uu___6)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ()))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (4)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.top_env
                                                                    ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    uu___6
                                                                    "pulse.join"))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    if uu___6
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Builtins.dump
                                                                    "PULSE: Goals after join"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ()))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ()))))
                                                                    uu___5)))
                                                                  uu___4)))
                                                       uu___4))) uu___3)))
                                 uu___2))) uu___2))) uu___1)
let (main :
  Prims.string ->
    Pulse_Syntax_Base.decl ->
      Pulse_Syntax_Base.term -> FStar_Reflection_Typing.dsl_tac_t)
  =
  fun nm ->
    fun t ->
      fun pre ->
        fun g ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (109))
                     (Prims.of_int (2)) (Prims.of_int (112))
                     (Prims.of_int (24)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (112))
                     (Prims.of_int (25)) (Prims.of_int (121))
                     (Prims.of_int (5)))))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (109)) (Prims.of_int (5))
                           (Prims.of_int (109)) (Prims.of_int (46)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (109)) (Prims.of_int (2))
                           (Prims.of_int (112)) (Prims.of_int (24)))))
                  (Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Main.fst"
                                 (Prims.of_int (109)) (Prims.of_int (5))
                                 (Prims.of_int (109)) (Prims.of_int (34)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Main.fst"
                                 (Prims.of_int (109)) (Prims.of_int (5))
                                 (Prims.of_int (109)) (Prims.of_int (46)))))
                        (Obj.magic
                           (FStar_Tactics_V2_Builtins.ext_getv
                              "pulse:guard_policy"))
                        (fun uu___ ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 -> uu___ = "SMTSync"))))
                  (fun uu___ ->
                     (fun uu___ ->
                        if uu___
                        then
                          Obj.magic
                            (FStar_Tactics_V2_Builtins.set_guard_policy
                               FStar_Tactics_Types.SMTSync)
                        else
                          Obj.magic
                            (FStar_Tactics_V2_Builtins.set_guard_policy
                               FStar_Tactics_Types.SMT)) uu___)))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (114)) (Prims.of_int (12))
                                (Prims.of_int (114)) (Prims.of_int (28)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (116)) (Prims.of_int (2))
                                (Prims.of_int (121)) (Prims.of_int (5)))))
                       (Obj.magic (main' nm t pre g))
                       (fun uu___1 ->
                          (fun res ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (116))
                                           (Prims.of_int (2))
                                           (Prims.of_int (120))
                                           (Prims.of_int (20)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (114))
                                           (Prims.of_int (6))
                                           (Prims.of_int (114))
                                           (Prims.of_int (9)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (116))
                                                 (Prims.of_int (5))
                                                 (Prims.of_int (116))
                                                 (Prims.of_int (32)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (116))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (120))
                                                 (Prims.of_int (20)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Main.fst"
                                                       (Prims.of_int (116))
                                                       (Prims.of_int (5))
                                                       (Prims.of_int (116))
                                                       (Prims.of_int (26)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Main.fst"
                                                       (Prims.of_int (116))
                                                       (Prims.of_int (5))
                                                       (Prims.of_int (116))
                                                       (Prims.of_int (32)))))
                                              (Obj.magic
                                                 (FStar_Tactics_V2_Builtins.ext_getv
                                                    "pulse:join"))
                                              (fun uu___1 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      uu___1 = "1"))))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              if uu___1
                                              then
                                                Obj.magic
                                                  (Obj.repr
                                                     (join_smt_goals ()))
                                              else
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 -> ()))))
                                             uu___1)))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> res)))) uu___1))) uu___)
let (check_pulse :
  Prims.string Prims.list ->
    (Prims.string * Prims.string) Prims.list ->
      Prims.string ->
        Prims.string ->
          Prims.int ->
            Prims.int -> Prims.string -> FStar_Reflection_Typing.dsl_tac_t)
  =
  fun namespaces ->
    fun module_abbrevs ->
      fun content ->
        fun file_name ->
          fun line ->
            fun col ->
              fun nm ->
                fun env ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Main.fst"
                             (Prims.of_int (131)) (Prims.of_int (12))
                             (Prims.of_int (131)) (Prims.of_int (97)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Main.fst"
                             (Prims.of_int (131)) (Prims.of_int (6))
                             (Prims.of_int (147)) (Prims.of_int (36)))))
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          Pulse_ASTBuilder.parse_pulse env namespaces
                            module_abbrevs content file_name line col))
                    (fun uu___ ->
                       (fun uu___ ->
                          match uu___ with
                          | FStar_Pervasives.Inl decl ->
                              Obj.magic
                                (Obj.repr
                                   (main nm decl Pulse_Syntax_Base.tm_emp env))
                          | FStar_Pervasives.Inr
                              (FStar_Pervasives_Native.None) ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_V2_Derived.fail
                                      "Pulse parser failed"))
                          | FStar_Pervasives.Inr
                              (FStar_Pervasives_Native.Some (msg, range)) ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (140))
                                               (Prims.of_int (10))
                                               (Prims.of_int (144))
                                               (Prims.of_int (21)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (146))
                                               (Prims.of_int (8))
                                               (Prims.of_int (147))
                                               (Prims.of_int (36)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Main.fst"
                                                     (Prims.of_int (141))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (141))
                                                     (Prims.of_int (74)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Issue.fsti"
                                                     (Prims.of_int (49))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (49))
                                                     (Prims.of_int (65)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (141))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (141))
                                                           (Prims.of_int (74)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (141))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (141))
                                                           (Prims.of_int (74)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Main.fst"
                                                                 (Prims.of_int (141))
                                                                 (Prims.of_int (44))
                                                                 (Prims.of_int (141))
                                                                 (Prims.of_int (69)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Printf.fst"
                                                                 (Prims.of_int (121))
                                                                 (Prims.of_int (8))
                                                                 (Prims.of_int (123))
                                                                 (Prims.of_int (44)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_V2_Builtins.range_to_string
                                                              range))
                                                        (fun uu___1 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                fun x ->
                                                                  Prims.strcat
                                                                    (
                                                                    Prims.strcat
                                                                    ""
                                                                    (Prims.strcat
                                                                    uu___1
                                                                    ": "))
                                                                    (
                                                                    Prims.strcat
                                                                    x "")))))
                                                  (fun uu___1 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___2 ->
                                                          uu___1 msg))))
                                            (fun uu___1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    FStar_Issue.mk_issue_doc
                                                      "Error"
                                                      [FStar_Pprint.arbitrary_string
                                                         uu___1]
                                                      (FStar_Pervasives_Native.Some
                                                         range)
                                                      FStar_Pervasives_Native.None
                                                      []))))
                                      (fun uu___1 ->
                                         (fun i ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (146))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (146))
                                                          (Prims.of_int (24)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (147))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (147))
                                                          (Prims.of_int (36)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_V2_Builtins.log_issues
                                                       [i]))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_V2_Derived.fail
                                                      "Pulse parser failed")))
                                           uu___1)))) uu___)
let _ =
  FStar_Tactics_Native.register_tactic "Pulse.Main.check_pulse"
    (Prims.of_int (9))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_V2_InterpFuns.mk_tactic_interpretation_8
             "Pulse.Main.check_pulse (plugin)"
             (FStar_Tactics_Native.from_tactic_8 check_pulse)
             (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string)
             (FStar_Syntax_Embeddings.e_list
                (FStar_Syntax_Embeddings.e_tuple2
                   FStar_Syntax_Embeddings.e_string
                   FStar_Syntax_Embeddings.e_string))
             FStar_Syntax_Embeddings.e_string
             FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_int
             FStar_Syntax_Embeddings.e_int FStar_Syntax_Embeddings.e_string
             FStar_Reflection_V2_Embeddings.e_env
             (FStar_Syntax_Embeddings.e_list
                (FStar_Syntax_Embeddings.e_tuple3
                   FStar_Syntax_Embeddings.e_bool
                   FStar_Reflection_V2_Embeddings.e_sigelt
                   (FStar_Syntax_Embeddings.e_option
                      (FStar_Syntax_Embeddings.e_tuple2
                         FStar_Syntax_Embeddings.e_string
                         FStar_Reflection_V2_Embeddings.e_term)))) psc ncb
             args)