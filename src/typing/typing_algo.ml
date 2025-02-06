(* IMPORT *)

open Ast
open Typing_utils

(* Init classes for typing  *)

let init_classes (classes : classes) (p : pfile) =
  (* We expected that Object and String are already in classes *)
  List.iter
    begin
      fun (id, _, _) ->
        let name, loc = (id.id, id.loc) in

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
  let vars, env =
    List.fold_left
      begin
        fun (vars, env) (typ, id) ->
          let name, loc = (id.id, id.loc) in

          if Env.mem name env then error ~loc "The parameter %s is already defined" name;

          let var = make_var name (get_typ classes typ) ~-1 in
          let env = Env.add var.var_name var.var_type env in

          (var :: vars, env)
      end
      ([], Env.empty) params
  in
  (List.rev vars, env)

(* Verify if the method is correct *)

let get_method (name : string) (loc : location) (args : pexpr list) (cls : class_) : method_ =
  if not @@ has_method name cls then error ~loc "%s is not a correct method" name;

  let meth = Hashtbl.find cls.class_methods name in

  if List.compare_lengths meth.meth_params args <> 0 then error ~loc "incorrect number of arguments";

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

let verify_have_return (loc : location) (name : string) (s : pstmt_desc) : unit =
  if have_not_return s then error ~loc "The method %s must have a return" name

let verify_have_not_return (loc : location) (name : string) (s : pstmt_desc) : unit =
  if have_return s then error ~loc "The method %s must not have a return" name

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

(* Type the binop Add *)

let type_add ~loc e1 e2 =
  if e1.expr_type =* Tint && e2.expr_type =* Tint then make_expr (Ebinop (Badd, e1, e2)) Tint
  else if e1.expr_type =* type_string && e2.expr_type =* type_string then
    make_expr (Ebinop (Badd_s, e1, e2)) type_string
  else if e1.expr_type =* Tint && e2.expr_type =* type_string then
    make_expr (Ebinop (Badd_s, make_expr (Eunop (Ustring_of_int, e1)) type_string, e2)) type_string
  else if e1.expr_type =* type_string && e2.expr_type =* Tint then
    make_expr (Ebinop (Badd_s, e1, make_expr (Eunop (Ustring_of_int, e2)) type_string)) type_string
  else error ~loc "Invalid_argument for +"
