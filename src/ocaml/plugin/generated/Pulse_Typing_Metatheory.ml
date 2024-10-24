open Prims
type ('g, 'c) comp_typing_u = (unit, unit, unit) Pulse_Typing.comp_typing
let (admit_st_comp_typing :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_comp -> (unit, unit) Pulse_Typing.st_comp_typing)
  =
  fun g ->
    fun st -> Pulse_Typing.STC (g, st, (Pulse_Typing.fresh g), (), (), ())
let (admit_comp_typing :
  Pulse_Typing.env -> Pulse_Syntax_Base.comp_st -> (unit, unit) comp_typing_u)
  =
  fun g ->
    fun c ->
      match c with
      | Pulse_Syntax_Base.C_ST st ->
          Pulse_Typing.CT_ST (g, st, (admit_st_comp_typing g st))
      | Pulse_Syntax_Base.C_STAtomic (inames, st) ->
          Pulse_Typing.CT_STAtomic
            (g, inames, st, (), (admit_st_comp_typing g st))
      | Pulse_Syntax_Base.C_STGhost (inames, st) ->
          Pulse_Typing.CT_STGhost
            (g, inames, st, (), (admit_st_comp_typing g st))
let (st_typing_correctness :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (unit, unit) comp_typing_u)
  = fun g -> fun t -> fun c -> fun uu___ -> admit_comp_typing g c
let (add_frame_well_typed :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit) comp_typing_u ->
        Pulse_Syntax_Base.term -> unit -> (unit, unit) comp_typing_u)
  =
  fun g ->
    fun c ->
      fun ct ->
        fun f -> fun ft -> admit_comp_typing g (Pulse_Typing.add_frame c f)
let (comp_typing_inversion :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit) comp_typing_u -> (unit, unit) Pulse_Typing.st_comp_typing)
  =
  fun g ->
    fun c ->
      fun ct ->
        match ct with
        | Pulse_Typing.CT_ST (uu___, uu___1, st) -> st
        | Pulse_Typing.CT_STAtomic (uu___, uu___1, uu___2, uu___3, st) -> st
        | Pulse_Typing.CT_STGhost (uu___, uu___1, uu___2, uu___3, st) -> st
type ('x, 'g, 'vars) fresh_wrt = unit
let (st_comp_typing_inversion_cofinite :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_comp ->
      (unit, unit) Pulse_Typing.st_comp_typing -> (unit * unit * unit))
  = fun g -> fun st -> fun ct -> ((), (), ())
let (st_comp_typing_inversion :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_comp ->
      (unit, unit) Pulse_Typing.st_comp_typing ->
        (unit, unit, Pulse_Syntax_Base.var, unit) FStar_Pervasives.dtuple4)
  =
  fun g ->
    fun st ->
      fun ct ->
        let uu___ = ct in
        match uu___ with
        | Pulse_Typing.STC (g1, st1, x, ty, pre, post) ->
            FStar_Pervasives.Mkdtuple4 ((), (), x, ())
let (tm_exists_inversion :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          unit -> Pulse_Syntax_Base.var -> (unit * unit))
  = fun g -> fun u -> fun ty -> fun p -> fun uu___ -> fun x -> ((), ())
