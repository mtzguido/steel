module Pulse.Lib.Pervasives
include Pulse.Main
include Pulse.Lib.Core
include Pulse.Lib.Array
include Pulse.Lib.Reference
include Steel.FractionalPermission
include FStar.Ghost

(* Pulse will currently not recognize calls to anything other than
top-level names, so this allows to force it. *)
val perform
  (#a #pre #post : _)
  (f : unit -> stt a pre post)
  : unit -> stt a pre post
let perform f () = f ()

(* TEMPORARY! REMOVE! *)
let inames_ext (is1 is2 : inames)
  : Lemma (requires forall i. Set.mem i is1 <==> Set.mem i is2)
          (ensures is1 == is2)
          [SMTPat (is1 == is2)]
  = Set.lemma_equal_intro is1 is2

let l1 (is1 : inames)
  : Lemma (join_inames is1 emp_inames == is1) [SMTPat (join_inames is1 emp_inames)]
  = Set.lemma_equal_intro (join_inames is1 emp_inames) is1
