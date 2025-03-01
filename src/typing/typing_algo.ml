(* IMPORT *)

open Ast
open Typing_utils

(* Init classes for typing  *)

let has_no_cycles (classes : (string, class_) Hashtbl.t) =
  let rec visit (visited : (string, unit) Hashtbl.t) (c : class_) =
    match Hashtbl.mem visited c.class_name with
    | true -> error "Cycle detected"
    | false ->
      Hashtbl.replace visited c.class_name ();
      if c.class_name <> "Object" then visit visited c.class_extends
  in

  Hashtbl.iter (fun _ c -> visit (Hashtbl.create 16) c) classes

let init_heriarchy (classes : classes) =
  List.iter
    begin
      fun (id, parent, _) ->
        let name, loc = (id.id, id.loc) in

        match parent with
        | None -> ()
        | Some par ->
          let par_name = par.id in

          if not @@ Hashtbl.mem classes par_name then
            error ~loc "The class %s is not defined" par_name;
          if par_name = "String" then error ~loc "The class String cannot be extended";

          let par = Hashtbl.find classes par_name in
          let c = Hashtbl.find classes name in

          c.class_extends <- par
    end

let init_classes (classes : classes) (p : pfile) =
  (* We expected that Object and String are already in classes *)
  List.iter
    begin
      fun (id, par, _) ->
        let name, loc = (id.id, id.loc) in
        if Hashtbl.mem classes id.id then error ~loc "The class %s is already defined" name;

        Hashtbl.replace classes id.id (init_class id.id)
    end
    p;

  init_heriarchy classes p;
  has_no_cycles classes

(* Verify if the method is correct *)

let rec check_has_method_opt ~loc (id : string) (c : class_) : method_ option =
  if c.class_name = "Object" then None
  else
    match has_method id c with
    | false -> check_has_method_opt ~loc id c.class_extends
    | true -> Hashtbl.find c.class_methods id |> Option.some

let rec check_has_method ~loc (id : string) (c : class_) : method_ =
  match check_has_method_opt ~loc id c with
  | None -> error ~loc "The method %s is not defined" id
  | Some m -> m

let get_method (name : string) (loc : location) (args : pexpr list) (cls : class_) : method_ =
  let meth = check_has_method ~loc name cls in
  if List.compare_lengths meth.meth_params args <> 0 then error ~loc "incorrect number of arguments";
  meth

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

        if Hashtbl.mem c.class_methods name then
          error ~loc "The constructor %s is already defined" name;
        if c.class_name <> name then
          error ~loc "The name constructor %s must have the same that the class %s" name
            c.class_name;

        Hashtbl.replace c.class_methods name
        @@ make_method name (get_typ classes (PTident id)) (pparams_to_vars classes params) ~-1
      | PDmethod (typ_opt, id, params, blck) ->
        let name, loc = (id.id, id.loc) in

        if Hashtbl.mem c.class_methods name then error ~loc "The method %s is already defined" name;
        let m_type = get_typ_opt classes typ_opt in

        let () =
          match check_has_method_opt ~loc name c with
          | None -> ()
          | Some m' ->
            if m'.meth_type <> m_type then error ~loc "The method %s has a different type" name
        in

        Hashtbl.replace c.class_methods name
        @@ make_method name m_type (pparams_to_vars classes params) ~-1
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
          let env = Env.add var.var_name var env in

          (var :: vars, env)
      end
      ([], Env.empty) params
  in
  (List.rev vars, env)

(*Verify if the class has the attributes*)

let rec get_attribute ?(loc = dummy_loc) (id : string) (c : class_) : attribute =
  if c.class_name = "Object" then error ~loc "The attribute %s is not defined" id;

  match has_attribute id c with
  | false -> get_attribute ~loc id c.class_extends
  | true -> Hashtbl.find c.class_attributes id

let check_has_attribute ~loc (id : string) (c : class_) : unit = get_attribute ~loc id c |> ignore

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
  List.map2
    begin
      fun e v ->
        let typed_e = type_expr env e in
        check_subtype ~loc:e.pexpr_loc typed_e.expr_type v.var_type;
        typed_e
    end
    args params

(* Verify that args have exactly one arg and return it *)

let get_argument ~loc id = function
  | [ e ] -> e
  | _ -> error ~loc "%s function need exactly one argument" id
