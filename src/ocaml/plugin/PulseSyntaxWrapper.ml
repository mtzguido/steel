open Prims
open FStar_Ident
open Pulse_Syntax
module S = FStar_Syntax_Syntax
type universe = Pulse_Syntax.universe

let u_zero : universe = U_zero
let u_succ (u:universe) : universe = U_succ u
let u_var (s:string) : universe = U_var s
let u_max (u0:universe) (u1:universe) : universe = U_max (u0, u1)
let u_unknown : universe = U_unknown

type bv = Pulse_Syntax.bv
let mk_bv (i:index) (name:string) (r:range) : bv =
 { bv_index = i; bv_ppname=name; bv_range=r }

type nm = Pulse_Syntax.nm
let mk_nm (i:index) (name:string) (r:range) : nm =
 { nm_index = i; nm_ppname=name; nm_range= r}

type fv = Pulse_Syntax.fv
let mk_fv (nm:lident) (r:range) : fv =
 { fv_name = FStar_Ident.path_of_lid nm;
   fv_range = r }

type term = Pulse_Syntax.term
type binder = Pulse_Syntax.binder
type comp = Pulse_Syntax.comp
type vprop = term

let mk_binder (x:ident) (t:term) : binder =
  { binder_ty = t;
    binder_ppname=FStar_Ident.string_of_id x }


let tm_bvar (bv:bv) : term = Tm_BVar bv
let tm_var (x:nm) : term = Tm_Var x
let tm_fvar (x:fv) : term = Tm_FVar x
let tm_uinst (l:fv) (us:universe list) : term = Tm_UInst (l, us)
let tm_emp : term = Tm_Emp
let tm_pure (p:term) : term = Tm_Pure p
let tm_star (p0:term) (p1:term) : term = Tm_Star (p0, p1)
let tm_exists (b:binder) (body:vprop) : term = Tm_ExistsSL (U_unknown, b.binder_ty, body, false)
let map_aqual (q:S.aqual) =
  match q with
  | Some { S.aqual_implicit = true } -> Some Implicit
  | _ -> None
let tm_arrow (b:binder) (q:S.aqual) (body:comp) : term =
  Tm_Arrow(b, map_aqual q, body)
let tm_expr (t:S.term) : term = Tm_FStar t
let tm_unknown : term = Tm_Unknown


let mk_st_comp (pre:term) (ret:binder) (post:term) : st_comp =
  { u = U_unknown;
    res = ret.binder_ty;
    pre = pre;
    post = (* close_binder *) post
  }

let mk_comp (pre:term) (ret:binder) (post:term) : comp =
   C_ST (mk_st_comp pre ret post)

let ghost_comp (inames:term) (pre:term) (ret:binder) (post:term) : comp =
   C_STGhost (inames, mk_st_comp pre ret post)

let atomic_comp (inames:term) (pre:term) (ret:binder) (post:term) : comp =
   C_STAtomic (inames, mk_st_comp pre ret post)

type st_term = Pulse_Syntax.st_term
let tm_return (t:term) : st_term = Tm_Return(STT, false, t)

let tm_abs (bs:binder list) (annot:comp) (body:st_term) : st_term =
   let pre, post =
     match annot with
     | C_ST st 
     | C_STAtomic (_, st)
     | C_STGhost (_, st)  -> Some st.pre, Some st.post
     | _ -> None, None
   in
   let rec aux bs = 
     match bs with
     | [] -> failwith "Empty binders in tm_abs"
     | [ last ] ->
       Tm_Abs (last, None, pre, body, post)
     | hd::tl -> 
       Tm_Abs (hd, None, None, aux tl, None)
   in
   aux bs

let tm_st_app (head:term) (q:S.aqual) (arg:term) : st_term =
  Tm_STApp(head, map_aqual q, arg)
    
let tm_bind (x:(ident * term) option ) (e1:st_term) (e2:st_term) : st_term =
  Tm_Bind(e1, e2)    
  
let tm_let_mut (x:ident) (t:term) (v:term) (k:st_term) : st_term =
   Tm_WithLocal (v, k)
   
let tm_while (head:st_term) (invariant: (ident * vprop)) (body:st_term) : st_term =
   Tm_While (snd invariant, head, body)
   
let tm_if (head:term) (returns_annot:vprop option) (then_:st_term) (else_:st_term) : st_term =
   Tm_If (head, then_, else_, returns_annot)

module Pulse_Syntax_Naming = Pulse_Syntax (* for now *)
let close_term t v = Pulse_Syntax_Naming.close_term t v
let close_st_term t v = Pulse_Syntax_Naming.close_st_term t v
let close_comp t v = Pulse_Syntax_Naming.close_comp t v
