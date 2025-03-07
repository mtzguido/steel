module HaclExample
open Steel.ST.GenElim
open Steel.ST.C.Types
open Steel.C.Typenat
open Steel.C.Typestring
open Steel.ST.C.Types.Struct.Aux
open Steel.ST.C.Types.UserStruct // hides Struct

module U64 = FStar.UInt64

(** In this file we demonstrate how Steel could be used to manipulate the following data type used in Hacl*:
      https://github.com/project-everest/hacl-star/blob/master/code/poly1305/Hacl.Impl.Poly1305.fsti#L18
    This Low* definition amounts to the struct definition
      struct poly1305_ctx { uint64_t limbs[5]; uint64_t precomp[20]; };
    and, with our new model of structs and arrays and pointer-to-field, can be expresesd directly in Steel.

    See PointStruct.fst for more detailed explanations of the various definitions needed below.
*)

noextract inline_for_extraction let five = normalize (nat_t_of_nat 5)
noextract inline_for_extraction let twenty = normalize (nat_t_of_nat 20)
noextract inline_for_extraction let comp_name = normalize (mk_string_t "HaclExample2.comp")

noeq
type comp_t = {
  limbs: base_array_t (scalar_t U64.t)  five 5sz;
  precomp: base_array_t (scalar_t U64.t)  twenty 20sz;
}

noextract
inline_for_extraction
[@@ norm_field_attr]
let comp_struct_def : struct_def comp_t =
  let fields = FStar.Set.add "limbs" (FStar.Set.singleton "precomp") in
  let fd_type (n: field_t fields) : Tot Type0 = match n with "limbs" -> base_array_t (scalar_t U64.t)  five 5sz | "precomp" -> base_array_t (scalar_t U64.t) twenty 20sz in
  let field_desc : field_description_gen_t (field_t fields) = {
    fd_nonempty = nonempty_set_nonempty_type "limbs" fields;
    fd_type = fd_type;
    fd_typedef = (fun (n: field_t fields) -> match n returns typedef (fd_type n) with "limbs" -> base_array0 five (scalar U64.t) 5sz | "precomp" -> base_array0 twenty (scalar U64.t) 20sz);
  }
  in {
    fields = fields;
    field_desc = field_desc;
    mk = (fun f -> Mkcomp_t (f "limbs") (f "precomp"));
    get = (fun x f -> match f with "limbs" -> x.limbs | "precomp" -> x.precomp);
    get_mk = (fun _ _ -> ());
    extensionality = (fun s1 s2 phi -> phi "limbs"; phi "precomp");
  }

noextract inline_for_extraction
let comp = struct_typedef comp_struct_def

(** To demonstrate how our model could be used, we write a simple
    function that takes pointers to the limbs and precomp fields and
    passes them to helper functions (which in this case simply set on
    element of the corresponding array to zero) *)

let do_something_with_limbs
  (#v: Ghost.erased (Seq.seq (scalar_t U64.t)))
  (a: array (scalar U64.t))
: ST (Ghost.erased (Seq.seq (scalar_t U64.t)))
    (array_pts_to a v)
    (fun v' -> array_pts_to a v')
    (requires
      array_length a == 5 /\
      fractionable_seq (scalar U64.t) v /\
      full_seq (scalar U64.t) v
    )
    (ensures (fun v' ->
      fractionable_seq (scalar U64.t) v' /\
      full_seq (scalar U64.t) v'
    ))
= let p = array_cell a 2sz in
  write p 0uL;
  unarray_cell _ _ _;
  drop (has_array_cell _ _ _); 
  return _

let do_something_with_precomp
  (#v: Ghost.erased (Seq.seq (scalar_t U64.t)))
  (a: array (scalar U64.t))
: ST (ptr (scalar U64.t))
    (array_pts_to a v)
    (fun _ -> exists_ (fun (v': Ghost.erased (Seq.seq (scalar_t U64.t))) ->
      array_pts_to a v' `star`
      pure (full_seq (scalar U64.t) v' /\ fractionable_seq (scalar U64.t) v')
    ))
    (requires
      array_length a == 20 /\
      fractionable_seq (scalar U64.t) v /\
      full_seq (scalar U64.t) v
    )
    (ensures fun _ -> True)
= 
  let ar = array_split a 10sz in
  let _ = gen_elim () in
  let vr = vpattern (array_pts_to ar) in
  vpattern_rewrite (array_pts_to ar) (Ghost.hide (mk_fraction_seq (scalar U64.t) (Ghost.reveal vr) full_perm));
  array_memcpy ar (array_split_l a 10sz) 10sz;
  let _ = array_join a _ ar 10sz in
  let p = array_cell a 19sz in
  write p 0uL;
  unarray_cell _ _ _;
  drop (has_array_cell _ _ _);
  let _ = vpattern_replace (array_pts_to a) in
  noop ();
  return (null _)

let test_alloc_free
  ()
: STT unit
    emp
    (fun _ -> emp)
=
  let a = array_alloc (scalar bool) 42sz in
  let _ = gen_elim () in
  if array_is_null a
  then begin
    rewrite (array_pts_to_or_null _ _) emp;
    rewrite (freeable_or_null_array _) emp;
    noop ()
  end else begin
    let s = vpattern_replace (array_pts_to_or_null _) in
    rewrite (array_pts_to_or_null _ _) (array_pts_to a s);
    rewrite (freeable_or_null_array _) (freeable_array a);
    array_free a
  end

#push-options "--z3rlimit 16"
#restart-solver

let test
  (#v: Ghost.erased (typeof comp))
  (p: ref comp)
: ST (Ghost.erased (typeof comp))
    (p `pts_to` v)
    (fun v' -> p `pts_to` v')
    (full comp v /\ fractionable comp v)
    (fun v' -> full comp v' /\
      fractionable comp v')
= let q = p `struct_field` "limbs" in
  let a = array_of_base q in
  let r = p `struct_field` "precomp" in
  let _ = vpattern_replace_erased (pts_to p) in // FIXME: WHY WHY WHY?
  let b = array_of_base r in
  let _ = do_something_with_limbs a in
  let _ = do_something_with_precomp b in
  let _ = gen_elim () in
  let _ = unarray_of_base q a in
  let _ = unarray_of_base r b in
  let _ = unstruct_field p "precomp" r in
  let _ = unstruct_field p "limbs" q in
  drop (has_struct_field p "limbs" q);
  drop (has_struct_field p "precomp" r);
  noop ();
  return _

#pop-options
