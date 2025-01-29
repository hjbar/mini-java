(* Import *)

open Ast

(* Debug *)

let debug = ref false

(* Errors *)

let dummy_loc = (Lexing.dummy_pos, Lexing.dummy_pos)

exception Error of location * string

let error ?(loc = dummy_loc) f =
  Format.kasprintf (fun s -> raise (Error (loc, s))) ("@[" ^^ f ^^ "@]")

(* Types *)

type classes = (string, class_) Hashtbl.t

type typing_env = (string, unit) Hashtbl.t

let typ_to_string = function
  | Tvoid -> "void"
  | Tnull -> "null"
  | Tboolean -> "bool"
  | Tint -> "int"
  | Tclass c -> c.class_name

let check_type ?(loc = dummy_loc) (typ1 : typ) (typ2 : typ) =
  if typ1 <> typ2 then
    error ~loc "Type %s expected, but got %s" (typ_to_string typ1) (typ_to_string typ2)

(* Making some records *)

let init_class class_name : class_ =
  { class_name
  ; class_extends = None
  ; class_methods = Hashtbl.create 16
  ; class_attributes = Hashtbl.create 16
  }

let make_class class_name class_extends class_methods class_attributes : class_ =
  { class_name; class_extends; class_methods; class_attributes }

let make_attribute attr_name attr_type attr_ofs : attribute = { attr_name; attr_type; attr_ofs }

let make_method meth_name meth_type meth_params meth_ofs : method_ =
  { meth_name; meth_type; meth_params; meth_ofs }

let make_var var_name var_type var_ofs : var = { var_name; var_type; var_ofs }

let make_expr expr_desc expr_type : expr = { expr_desc; expr_type }

(* Conversion of types *)

let get_typ (classes : classes) : pexpr_typ -> typ = function
  | PTboolean -> Tboolean
  | PTint -> Tint
  | PTident s -> Tclass (Hashtbl.find classes s.id)

let get_typ_opt (classes : classes) : pexpr_typ option -> typ = function
  | None -> Tvoid
  | Some typ -> get_typ classes typ

(* Conversion of constructions *)

let pparams_to_vars (classes : classes) (params : pparam list) : var list =
  List.map (fun (typ, name) -> make_var name.id (get_typ classes typ) ~-1) params
