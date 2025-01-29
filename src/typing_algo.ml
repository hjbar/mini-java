(* IMPORT *)

open Ast
open Typing_utils

(* Init classes for typing  *)

let init_classes (classes : classes) (p : pfile) =
  let f (id, _, _) =
    if Hashtbl.mem classes id.id then error ~loc:id.loc "The class %s is already defined" id.id;
    Hashtbl.replace classes id.id (init_class id.id)
  in
  List.iter f p

(* Update class with decls *)

let update_class (classes : classes) (c : class_) (decls : pdecl list) =
  (* TODO : extends *)
  List.iter
    begin
      function
      | PDattribute (typ, name) ->
        Hashtbl.replace c.class_attributes name.id
        @@ make_attribute name.id (get_typ classes typ) ~-1
      | PDconstructor (name, params, block) ->
        Hashtbl.replace c.class_methods name.id
        @@ make_method name.id (get_typ classes (PTident name)) (pparams_to_vars classes params) ~-1
      | PDmethod (typ_opt, name, params, blck) ->
        Hashtbl.replace c.class_methods name.id
        @@ make_method name.id (get_typ_opt classes typ_opt) (pparams_to_vars classes params) ~-1
    end
    decls
