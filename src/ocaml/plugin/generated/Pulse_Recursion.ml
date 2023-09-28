open Prims
let (tie_knot :
  Pulse_Typing_Env.env ->
    FStar_Range.range ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp ->
          Prims.string ->
            Prims.string ->
              (unit FStar_Reflection_Typing.sigelt_for Prims.list, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun rng ->
      fun body ->
        fun c ->
          fun nm ->
            fun nm_orig ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Recursion.fst"
                         (Prims.of_int (20)) (Prims.of_int (4))
                         (Prims.of_int (26)) (Prims.of_int (43)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Recursion.fst"
                         (Prims.of_int (27)) (Prims.of_int (4))
                         (Prims.of_int (37)) (Prims.of_int (61)))))
                (match c with
                 | Pulse_Syntax_Base.C_Tot t ->
                     Obj.magic
                       (Obj.repr
                          (match t.Pulse_Syntax_Base.t with
                           | Pulse_Syntax_Base.Tm_FStar t1 ->
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ -> t1))
                           | uu___ ->
                               Obj.repr
                                 (Pulse_Typing_Env.fail g
                                    (FStar_Pervasives_Native.Some rng)
                                    "not a Tm_Fstar?")))
                 | uu___ ->
                     Obj.magic
                       (Obj.repr
                          (Pulse_Typing_Env.fail g
                             (FStar_Pervasives_Native.Some rng)
                             "not a C_Tot?")))
                (fun uu___ ->
                   (fun f_ty ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Recursion.fst"
                                    (Prims.of_int (29)) (Prims.of_int (14))
                                    (Prims.of_int (29)) (Prims.of_int (36)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Recursion.fst"
                                    (Prims.of_int (27)) (Prims.of_int (4))
                                    (Prims.of_int (37)) (Prims.of_int (61)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ ->
                                 FStar_Reflection_V2_Derived.collect_arr_ln_bs
                                   f_ty))
                           (fun uu___ ->
                              (fun uu___ ->
                                 match uu___ with
                                 | (bs, c1) ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Recursion.fst"
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (34)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Recursion.fst"
                                                   (Prims.of_int (32))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (37))
                                                   (Prims.of_int (61)))))
                                          (if Prims.uu___is_Nil bs
                                           then
                                             Obj.magic
                                               (Obj.repr
                                                  (Pulse_Typing_Env.fail g
                                                     (FStar_Pervasives_Native.Some
                                                        rng) "no binders"))
                                           else
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 -> ()))))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Recursion.fst"
                                                              (Prims.of_int (32))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (33))
                                                              (Prims.of_int (41)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Recursion.fst"
                                                              (Prims.of_int (33))
                                                              (Prims.of_int (42))
                                                              (Prims.of_int (37))
                                                              (Prims.of_int (61)))))
                                                     (if
                                                        Prims.uu___is_Nil
                                                          (FStar_List_Tot_Base.init
                                                             bs)
                                                      then
                                                        Obj.magic
                                                          (Obj.repr
                                                             (Pulse_Typing_Env.fail
                                                                g
                                                                (FStar_Pervasives_Native.Some
                                                                   rng)
                                                                "only one binder??"))
                                                      else
                                                        Obj.magic
                                                          (Obj.repr
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   -> ()))))
                                                     (fun uu___2 ->
                                                        (fun uu___2 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (68)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (61)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    FStar_Reflection_V2_Derived.mk_arr_ln
                                                                    (FStar_List_Tot_Base.init
                                                                    bs) c1))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun ty ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (3))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (FStar_Reflection_Typing.mk_unchecked_let
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)
                                                                    nm_orig
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "magic"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    FStar_Reflection_V2_Data.C_Unit)),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))
                                                                    ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    [uu___3]))))
                                                                    uu___3)))
                                                          uu___2))) uu___1)))
                                uu___))) uu___)