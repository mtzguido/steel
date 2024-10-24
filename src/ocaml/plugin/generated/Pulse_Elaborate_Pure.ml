open Prims
let op_let_Bang :
  'a 'b .
    'a FStar_Pervasives_Native.option ->
      ('a -> 'b FStar_Pervasives_Native.option) ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun g ->
      match f with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some x -> g x
let (elab_qual :
  Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
    FStar_Reflection_Data.aqualv)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> FStar_Reflection_Data.Q_Explicit
    | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Implicit) ->
        FStar_Reflection_Data.Q_Implicit
let rec (elab_term : Pulse_Syntax_Base.term -> FStar_Reflection_Types.term) =
  fun top ->
    match top with
    | Pulse_Syntax_Base.Tm_VProp ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                Pulse_Reflection_Util.vprop_lid))
    | Pulse_Syntax_Base.Tm_Emp ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv Pulse_Reflection_Util.emp_lid))
    | Pulse_Syntax_Base.Tm_Pure p ->
        let p1 = elab_term p in
        let head =
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_FVar
               (FStar_Reflection_Builtins.pack_fv
                  Pulse_Reflection_Util.pure_lid)) in
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_App
             (head, (p1, FStar_Reflection_Data.Q_Explicit)))
    | Pulse_Syntax_Base.Tm_Star (l, r) ->
        let l1 = elab_term l in
        let r1 = elab_term r in Pulse_Reflection_Util.mk_star l1 r1
    | Pulse_Syntax_Base.Tm_ExistsSL (u, t, body, uu___) ->
        let t1 = elab_term t in
        let b = elab_term body in
        if Pulse_Syntax_Base.uu___is_Tm_ExistsSL top
        then
          Pulse_Reflection_Util.mk_exists u t1
            (Pulse_Reflection_Util.mk_abs t1 FStar_Reflection_Data.Q_Explicit
               b)
        else
          Pulse_Reflection_Util.mk_forall u t1
            (Pulse_Reflection_Util.mk_abs t1 FStar_Reflection_Data.Q_Explicit
               b)
    | Pulse_Syntax_Base.Tm_ForallSL (u, t, body) ->
        let t1 = elab_term t in
        let b = elab_term body in
        if Pulse_Syntax_Base.uu___is_Tm_ExistsSL top
        then
          Pulse_Reflection_Util.mk_exists u t1
            (Pulse_Reflection_Util.mk_abs t1 FStar_Reflection_Data.Q_Explicit
               b)
        else
          Pulse_Reflection_Util.mk_forall u t1
            (Pulse_Reflection_Util.mk_abs t1 FStar_Reflection_Data.Q_Explicit
               b)
    | Pulse_Syntax_Base.Tm_Inames ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                Pulse_Reflection_Util.inames_lid))
    | Pulse_Syntax_Base.Tm_EmpInames -> Pulse_Reflection_Util.emp_inames_tm
    | Pulse_Syntax_Base.Tm_Unknown ->
        FStar_Reflection_Builtins.pack_ln FStar_Reflection_Data.Tv_Unknown
    | Pulse_Syntax_Base.Tm_FStar (t, uu___) -> t
let (elab_st_comp :
  Pulse_Syntax_Base.st_comp ->
    (FStar_Reflection_Types.universe * FStar_Reflection_Types.term *
      FStar_Reflection_Types.term * FStar_Reflection_Types.term))
  =
  fun c ->
    let res = elab_term c.Pulse_Syntax_Base.res in
    let pre = elab_term c.Pulse_Syntax_Base.pre in
    let post = elab_term c.Pulse_Syntax_Base.post in
    ((c.Pulse_Syntax_Base.u), res, pre, post)
let (elab_comp : Pulse_Syntax_Base.comp -> FStar_Reflection_Types.term) =
  fun c ->
    match c with
    | Pulse_Syntax_Base.C_Tot t -> elab_term t
    | Pulse_Syntax_Base.C_ST c1 ->
        let uu___ = elab_st_comp c1 in
        (match uu___ with
         | (u, res, pre, post) ->
             Pulse_Reflection_Util.mk_stt_comp u res pre
               (Pulse_Reflection_Util.mk_abs res
                  FStar_Reflection_Data.Q_Explicit post))
    | Pulse_Syntax_Base.C_STAtomic (inames, c1) ->
        let inames1 = elab_term inames in
        let uu___ = elab_st_comp c1 in
        (match uu___ with
         | (u, res, pre, post) ->
             Pulse_Reflection_Util.mk_stt_atomic_comp u res inames1 pre
               (Pulse_Reflection_Util.mk_abs res
                  FStar_Reflection_Data.Q_Explicit post))
    | Pulse_Syntax_Base.C_STGhost (inames, c1) ->
        let inames1 = elab_term inames in
        let uu___ = elab_st_comp c1 in
        (match uu___ with
         | (u, res, pre, post) ->
             Pulse_Reflection_Util.mk_stt_ghost_comp u res inames1 pre
               (Pulse_Reflection_Util.mk_abs res
                  FStar_Reflection_Data.Q_Explicit post))
let (elab_stt_equiv :
  FStar_Reflection_Types.env ->
    Pulse_Syntax_Base.comp ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          (unit, unit, unit) FStar_Reflection_Typing.equiv ->
            (unit, unit, unit) FStar_Reflection_Typing.equiv ->
              (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun c ->
      fun pre ->
        fun post ->
          fun eq_pre ->
            fun eq_post ->
              Pulse_Reflection_Util.mk_stt_comp_equiv g
                (Pulse_Syntax_Base.comp_u c)
                (elab_term (Pulse_Syntax_Base.comp_res c)) pre post
                (elab_term (Pulse_Syntax_Base.comp_pre c))
                (Pulse_Reflection_Util.mk_abs
                   (elab_term (Pulse_Syntax_Base.comp_res c))
                   FStar_Reflection_Data.Q_Explicit
                   (elab_term (Pulse_Syntax_Base.comp_post c))) eq_pre
                eq_post
let (elab_statomic_equiv :
  FStar_Reflection_Types.env ->
    Pulse_Syntax_Base.comp ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          (unit, unit, unit) FStar_Reflection_Typing.equiv ->
            (unit, unit, unit) FStar_Reflection_Typing.equiv ->
              (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun c ->
      fun pre ->
        fun post ->
          fun eq_pre ->
            fun eq_post ->
              let uu___ = c in
              match uu___ with
              | Pulse_Syntax_Base.C_STAtomic (inames, uu___1) ->
                  Pulse_Reflection_Util.mk_stt_atomic_comp_equiv g
                    (Pulse_Syntax_Base.comp_u c)
                    (elab_term (Pulse_Syntax_Base.comp_res c))
                    (elab_term inames) pre post
                    (elab_term (Pulse_Syntax_Base.comp_pre c))
                    (Pulse_Reflection_Util.mk_abs
                       (elab_term (Pulse_Syntax_Base.comp_res c))
                       FStar_Reflection_Data.Q_Explicit
                       (elab_term (Pulse_Syntax_Base.comp_post c))) eq_pre
                    eq_post
let (elab_stghost_equiv :
  FStar_Reflection_Types.env ->
    Pulse_Syntax_Base.comp ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          (unit, unit, unit) FStar_Reflection_Typing.equiv ->
            (unit, unit, unit) FStar_Reflection_Typing.equiv ->
              (unit, unit, unit) FStar_Reflection_Typing.equiv)
  =
  fun g ->
    fun c ->
      fun pre ->
        fun post ->
          fun eq_pre ->
            fun eq_post ->
              let uu___ = c in
              match uu___ with
              | Pulse_Syntax_Base.C_STGhost (inames, uu___1) ->
                  Pulse_Reflection_Util.mk_stt_ghost_comp_equiv g
                    (Pulse_Syntax_Base.comp_u c)
                    (elab_term (Pulse_Syntax_Base.comp_res c))
                    (elab_term inames) pre post
                    (elab_term (Pulse_Syntax_Base.comp_pre c))
                    (Pulse_Reflection_Util.mk_abs
                       (elab_term (Pulse_Syntax_Base.comp_res c))
                       FStar_Reflection_Data.Q_Explicit
                       (elab_term (Pulse_Syntax_Base.comp_post c))) eq_pre
                    eq_post