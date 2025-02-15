(* IMPORT *)

open Ast
open Typing_utils

(* Init classes for typing  *)

let print_class c =
  Printf.printf "Class %s " c.class_name;
  Printf.printf "Extends %s\n" c.class_extends.class_name

let print_classes (classes : classes) = Hashtbl.iter (fun name c -> print_class !c) classes

let has_cycles (classes : (string, class_ ref) Hashtbl.t) =
  let visited = Hashtbl.create 16 in

  let rec visit (c : class_) =
    (* Printf.printf "Visiting %s\n" c.class_name; *)
    if Hashtbl.mem visited c.class_name then raise (Error (dummy_loc, "Cycle detected"));

    Hashtbl.add visited c.class_name ();

    Printf.printf "extends %s\n" c.class_extends.class_name;

    if c.class_name <> "Object" then visit c.class_extends;

    Hashtbl.remove visited c.class_name
  in

  Hashtbl.iter (fun _ c -> visit !c) classes

let init_heriarchy (classes : classes) (p : pfile) =
  List.iter
    begin
      fun (id, parent, _) ->
        let name, loc = (id.id, id.loc) in
        begin
          match parent with
          | None -> ()
          | Some par ->
            let par_name = par.id in
            if not @@ Hashtbl.mem classes par_name then
              error ~loc "The class %s is not defined" par_name;
            let par = Hashtbl.find classes par_name in
            let c = Hashtbl.find classes name in
            !c.class_extends <- !par
        end
    end
    (List.rev p)

let init_classes (classes : classes) (p : pfile) =
  (* We expected that Object and String are already in classes *)
  List.iter
    begin
      fun (id, par, _) ->
        let name, loc = (id.id, id.loc) in

        if Hashtbl.mem classes id.id then error ~loc "The class %s is already defined" name;

        Hashtbl.replace classes id.id (ref @@ init_class id.id)
    end
    (List.rev p);
  init_heriarchy classes p;
  has_cycles classes

(* Update class with decls *)

let update_class (classes : classes) (c : class_) (decls : pdecl list) : unit =
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
  List.iter (fun (id, _parent, decls) -> update_class classes !(Hashtbl.find classes id.id) decls) p

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
  check_has_method ~loc name cls;

  let meth = Hashtbl.find cls.class_methods name in

  if List.compare_lengths meth.meth_params args <> 0 then error ~loc "incorrect number of arguments";

  meth

(* Verify we have a return ot not *)

let rec have_return : pstmt_desc -> bool = function
  | PSreturn _ -> true
  | PSexpr _ | PSvar _ | PSfor _ -> false
  | PSif (_, s1, s2) -> have_return s1.pstmt_desc && have_return s2.pstmt_desc
  | PSblock block -> List.exists (fun s -> have_return s.pstmt_desc) block

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

(* Verify that args have exactly one arg and return it *)

let get_argument ~loc id = function
  | [ e ] -> e
  | _ -> error ~loc "%s function need exactly one argument" id
