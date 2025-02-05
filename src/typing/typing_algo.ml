(* IMPORT *)

open Ast
open Typing_utils

(* Init classes for typing  *)

let init_classes (classes : classes) (p : pfile) =
  List.iter
    begin
      fun (id, _, _) ->
        let name, loc = (id.id, id.loc) in

        if name = "Object" || name = "String" then
          error ~loc "This name %s for class is already used for build-in classes" name;
        if Hashtbl.mem classes id.id then error ~loc "The class %s is already defined" name;

        Hashtbl.replace classes id.id (init_class id.id)
    end
    p

(* Update class with decls *)

let update_class (classes : classes) (c : class_) (decls : pdecl list) : unit =
  (* TODO : extends *)
  List.iter
    begin
      function
      | PDattribute (typ, id) ->
        let name, loc = (id.id, id.loc) in
        let typ = get_typ ~loc classes typ in

        if Hashtbl.mem c.class_attributes name then
          error ~loc "The attribute %s is already defined" name;

        Hashtbl.replace c.class_attributes name @@ make_attribute name typ ~-1
      | PDconstructor (id, params, block) ->
        let name, loc = (id.id, id.loc) in

        if Hashtbl.mem c.class_methods name then error ~loc "The method %s is already defined" name;
        if c.class_name <> name then
          error ~loc "The name constructor %s must have the same that the class %s" name
            c.class_name;

        Hashtbl.replace c.class_methods name
        @@ make_method name (get_typ classes (PTident id)) (pparams_to_vars classes params) ~-1
      | PDmethod (typ_opt, id, params, blck) ->
        let name, loc = (id.id, id.loc) in

        if Hashtbl.mem c.class_methods name then
          error ~loc "The constructor %s is already defined" name;

        Hashtbl.replace c.class_methods name
        @@ make_method name (get_typ_opt classes typ_opt) (pparams_to_vars classes params) ~-1
    end
    decls

let update_classes (classes : classes) (p : pfile) : unit =
  List.iter (fun (id, _parent, decls) -> update_class classes (Hashtbl.find classes id.id) decls) p

(* Init vars and env for typing method & constr *)

let env_from_params (classes : classes) (params : pparam list) : var list * typing_env =
  let env = Hashtbl.create 16 in

  let vars =
    List.map
      begin
        fun (typ, id) ->
          let name, loc = (id.id, id.loc) in

          if Hashtbl.mem env name then error ~loc "The parameter %s is already defined" name;

          let var = make_var name (get_typ classes typ) ~-1 in
          Hashtbl.replace env var.var_name var.var_type;
          var
      end
      params
  in

  (vars, env)

(* Verify if the method is correct *)

let get_method (name : string) (loc : location) (args : pexpr list) (cls : class_) : method_ =
  if not @@ has_method name cls then error ~loc "%s is not a correct method" name;

  let meth = Hashtbl.find cls.class_methods name in

  if List.(length meth.meth_params <> length args) then error ~loc "incorrect number of arguments";

  meth

(* Verify we have a return ot not *)

let rec have_return : pstmt_desc -> bool = function
  | PSreturn _ -> true
  | PSexpr _ | PSvar _ -> false
  | PSfor (_, e, _, _) when is_expr_false e -> false
  | PSif (_, s1, s2) -> have_return s1.pstmt_desc && have_return s2.pstmt_desc
  | PSblock block -> List.exists (fun s -> have_return s.pstmt_desc) block
  | PSfor (s1, _, s2, s3) ->
    have_return s1.pstmt_desc || have_return s2.pstmt_desc || have_return s3.pstmt_desc

let have_not_return (s : pstmt_desc) : bool = not @@ have_return s

let verify_have_return (loc : location) (s : pstmt_desc) : unit =
  if have_not_return s then error ~loc "This method must have a return"

let verify_have_not_return (loc : location) (s : pstmt_desc) : unit =
  if have_return s then error ~loc "This method must not have a return"

(* Type the args of a call *)

let type_call_args type_expr env args params =
  (* TODO : utiliser le sous-typage *)
  List.map2
    begin
      fun e v ->
        let typed_e = type_expr env e in
        check_type ~loc:e.pexpr_loc v.var_type typed_e.expr_type;
        typed_e
    end
    args params
