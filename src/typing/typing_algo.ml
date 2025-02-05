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
