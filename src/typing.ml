open Ast

let debug = ref false

let dummy_loc = (Lexing.dummy_pos, Lexing.dummy_pos)

exception Error of Ast.location * string

(* use the following function to signal typing errors, e.g.
      error ~loc "unbound variable %s" id
*)
let error ?(loc = dummy_loc) f =
  Format.kasprintf (fun s -> raise (Error (loc, s))) ("@[" ^^ f ^^ "@]")

let pexprTyp_to_typ (classes : (string, class_) Hashtbl.t) :
  Ast.pexpr_typ option -> Ast.typ = function
  | None -> Tvoid
  | Some PTboolean -> Tboolean
  | Some PTint -> Tint
  | Some (PTident s) -> Tclass (Hashtbl.find classes s.id)

let pparams_to_vars (classes : (string, class_) Hashtbl.t)
  (params : (pexpr_typ * ident) list) : Ast.var list =
  List.map
    begin
      fun (typ, name) ->
        { var_name = name.id
        ; var_type = pexprTyp_to_typ classes (Some typ)
        ; var_ofs = -1
        }
    end
    params

let type_expr (expr : Ast.pexpr) : Ast.expr =
  match expr.pexpr_desc with _ -> assert false

let rec type_stmt (env : (ident, unit) Hashtbl.t) (s : Ast.pstmt) : Ast.stmt =
  let loc = s.pstmt_loc in

  match s.pstmt_desc with
  | PSexpr e -> Sexpr (type_expr e)
  | PSvar (typ, var, None) -> .
  | PSvar (typ, var, Some e) -> .
  | PSif (e, s1, s2) ->
    let e' = type_expr e in
    if e'.expr_type <> Tboolean then
      error ~loc:e.pexpr_loc "Condition has not type Bool";

    let s1' = type_stmt env s1 in
    let s2' = type_stmt env s2 in

    Sif (e', s1', s2')
  | PSreturn e_opt -> Sreturn (Option.map type_expr e_opt)
  | PSblock block -> Sblock (List.map (type_stmt env) block)
  | PSfor (s1, e, s2, s3) ->
    let s1' = type_stmt env s1 in

    let e' = type_expr e in
    if e'.expr_type <> Tboolean then
      error ~loc:e.pexpr_loc "Condition has not type Bool";

    let s2' = type_stmt env s2 in
    let s3' = type_stmt env s3 in

    Sfor (s1', e', s2', s3')

let type_decl classes acc : Ast.pdecl -> Ast.decl list = function
  | PDattribute _ -> acc
  | PDconstructor (name, params, block) ->
    let env = Hashtbl.create 16 in
    let vars = pparams_to_vars classes params in
    Dconstructor (vars, type_stmt env block) :: acc
  | PDmethod (typ_opt, name, params, block) ->
    let m =
      { meth_name = name.id
      ; meth_type = pexprTyp_to_typ classes typ_opt
      ; meth_params = pparams_to_vars classes params
      ; meth_ofs = -1
      }
    in
    let env = Hashtbl.create 16 in
    Dmethod (m, type_stmt env block) :: acc

let file ?debug:(b = false) (p : Ast.pfile) : Ast.tfile =
  debug := b;

  let classes : (string, class_) Hashtbl.t = Hashtbl.create 16 in

  List.iter
    begin
      fun (id, _, _) ->
        Hashtbl.replace classes id.id
          { class_name = id.id
          ; class_extends = None
          ; class_methods = Hashtbl.create 16
          ; class_attributes = Hashtbl.create 16
          }
    end
    p;

  (* TODO: vérifier que y'a pas deux classes avec le même nom *)
  List.iter
    begin
      fun (id, _parent, decls) ->
        let c = Hashtbl.find classes id.id in
        (* TODO : extends *)

        List.iter
          begin
            fun decl ->
              match decl with
              | PDattribute (typ, name) ->
                Hashtbl.replace c.class_attributes name.id
                  { attr_name = name.id
                  ; attr_type = pexprTyp_to_typ classes (Some typ)
                  ; attr_ofs = -1
                  }
              | PDconstructor (name, params, block) ->
                Hashtbl.replace c.class_methods name.id
                  { meth_name = name.id
                  ; meth_type = pexprTyp_to_typ classes (Some (PTident name))
                  ; meth_params = pparams_to_vars classes params
                  ; meth_ofs = -1
                  }
              | PDmethod (typ_opt, name, params, blck) ->
                Hashtbl.replace c.class_methods name.id
                  { meth_name = name.id
                  ; meth_type = pexprTyp_to_typ classes typ_opt
                  ; meth_params = pparams_to_vars classes params
                  ; meth_ofs = -1
                  }
          end
          decls
    end
    p;

  List.map
    begin
      fun (id, _parent, decls) ->
        (Hashtbl.find classes id.id, List.fold_left (type_decl classes) [] decls)
    end
    p
