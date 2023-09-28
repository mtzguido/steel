module Pulse.Recursion

module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing

open FStar.Tactics.V2
open Pulse.Syntax
open Pulse.Typing

val tie_knot (g : env)  (rng : R.range)
             (body : st_term) (c : comp)
             (nm : string) (nm_orig : string)
: Tac (list (RT.sigelt_for (fstar_env g)))
