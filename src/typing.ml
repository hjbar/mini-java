(* Import *)

open Ast
open Typing_utils
open Typing_algo

(* Typing expr *)

let type_expr (expr : pexpr) : expr = match expr.pexpr_desc with _ -> assert false

(* Typing stmt *)

let rec type_stmt (classes : classes) (env : typing_env) (s : pstmt) : stmt =
  let loc = s.pstmt_loc in

  match s.pstmt_desc with
  | PSexpr e -> Sexpr (type_expr e)
  | PSvar (typ, var, None) when not @@ Hashtbl.mem env var.id ->
    Hashtbl.replace env var.id ();

    let typ = get_typ classes typ in
    Svar (make_var var.id typ ~-1, make_expr Enull typ)
  | PSvar (typ, var, Some e) when not @@ Hashtbl.mem env var.id ->
    Hashtbl.replace env var.id ();

    let typ = get_typ classes typ in
    let e = type_expr e in
    check_type ~loc typ e.expr_type;

    Svar (make_var var.id typ ~-1, make_expr e.expr_desc e.expr_type)
  | PSvar (_, var, _) -> error ~loc "The variable %s is already defined" var.id
  | PSif (e, s1, s2) ->
    let typed_e = type_expr e in
    check_type ~loc:e.pexpr_loc Tboolean typed_e.expr_type;

    let typed_s1 = type_stmt classes env s1 in
    let typed_s2 = type_stmt classes env s2 in

    Sif (typed_e, typed_s1, typed_s2)
  | PSreturn e_opt -> Sreturn (Option.map type_expr e_opt)
  | PSblock block -> Sblock (List.map (type_stmt classes env) block)
  | PSfor (s1, e, s2, s3) ->
    let typed_s1 = type_stmt classes env s1 in

    let typed_e = type_expr e in
    check_type ~loc:e.pexpr_loc Tboolean typed_e.expr_type;

    let typed_s2 = type_stmt classes env s2 in
    let typed_s3 = type_stmt classes env s3 in

    Sfor (typed_s1, typed_e, typed_s2, typed_s3)

(* Typing decl *)

let type_decl (classes : classes) (decls : pdecl list) : decl list =
  let loop (classes : classes) (acc : decl list) : pdecl -> decl list = function
    | PDattribute _ -> acc
    | PDconstructor (name, params, block) ->
      let vars = pparams_to_vars classes params in
      let block = type_stmt classes (Hashtbl.create 16) block in
      Dconstructor (vars, block) :: acc
    | PDmethod (typ_opt, name, params, block) ->
      let m =
        make_method name.id (get_typ_opt classes typ_opt) (pparams_to_vars classes params) ~-1
      in
      let block = type_stmt classes (Hashtbl.create 16) block in
      Dmethod (m, block) :: acc
  in
  List.fold_left (loop classes) [] decls

(* Main *)

let file ?debug:(b = false) (p : pfile) : tfile =
  (* TODO : extends todo in update_class *)
  debug := b;

  let classes : (string, class_) Hashtbl.t = Hashtbl.create 16 in
  init_classes classes p;

  List.iter (fun (id, _parent, decls) -> update_class classes (Hashtbl.find classes id.id) decls) p;
  List.map (fun (id, _parent, decls) -> (Hashtbl.find classes id.id, type_decl classes decls)) p
