(* Import *)

open Ast

(* Debug *)

let debug = ref false

(* Errors *)

let dummy_loc = (Lexing.dummy_pos, Lexing.dummy_pos)

exception Error of location * string

let error ?(loc = dummy_loc) f =
  Format.kasprintf (fun s -> raise (Error (loc, s))) ("@[" ^^ f ^^ "@]")

(* Env *)

type classes = (string, class_) Hashtbl.t

module Env = Map.Make (String)

type typing_env = typ Env.t

(*
type typing_env = (string, typ) Hashtbl.t
*)

(* Build-in classes *)

let rec class_Object =
  { class_name = "Object"
  ; class_extends = class_Object
  ; class_methods = Hashtbl.create 16
  ; class_attributes = Hashtbl.create 16
  }

let class_String =
  { class_name = "String"
  ; class_extends = class_Object
  ; class_methods = Hashtbl.create 16
  ; class_attributes = Hashtbl.create 16
  }

let init_classes_env () : classes =
  let classes = Hashtbl.create 16 in

  Hashtbl.replace classes class_Object.class_name class_Object;
  Hashtbl.replace classes class_String.class_name class_String;

  classes

(* Build-in functons *)

let is_system_out c =
  match c.pexpr_desc with
  | PEdot (pexpr, id_out) when id_out.id = "out" -> begin
    match pexpr.pexpr_desc with PEident id_sys when id_sys.id = "System" -> true | _ -> false
  end
  | _ -> false

(* Types *)

let typ_to_string = function
  | Tvoid -> "void"
  | Tnull -> "null"
  | Tboolean -> "bool"
  | Tint -> "int"
  | Tclass c -> c.class_name

let is_class_type : typ -> bool = function Tclass _ -> true | _ -> false

let ( =* ) (typ1 : typ) (typ2 : typ) : bool =
  match (typ1, typ2) with
  | Tclass c1, Tclass c2 -> c1.class_name = c2.class_name
  | Tvoid, Tvoid | Tnull, Tnull | Tint, Tint | Tboolean, Tboolean -> true
  | _ -> false

let ( <>* ) (typ1 : typ) (typ2 : typ) : bool = not (typ1 =* typ2)

let check_type ?(loc = dummy_loc) (typ1 : typ) (typ2 : typ) =
  if typ1 <>* typ2 then
    error ~loc "Type %s expected, but got %s" (typ_to_string typ1) (typ_to_string typ2)

(* Making some records *)

let init_class class_name : class_ =
  { class_name
  ; class_extends = class_Object
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

(* Function on class *)

let get_class_type : typ -> class_ = function Tclass cls -> cls | _ -> assert false

let has_attribute (id : string) (c : class_) : bool = Hashtbl.mem c.class_attributes id

let get_attribute (id : string) (c : class_) : attribute = Hashtbl.find c.class_attributes id

let has_method (id : string) (c : class_) : bool = Hashtbl.mem c.class_methods id

let exist_class (classes : classes) (c : class_) : bool = Hashtbl.mem classes c.class_name

(* Function on  expr *)

let is_expr_false (e : pexpr) : bool =
  match e.pexpr_desc with PEconstant (Cbool false) -> true | _ -> false

(* Conversion of types *)

let get_typ ?(loc : location = dummy_loc) (classes : classes) : pexpr_typ -> typ = function
  | PTboolean -> Tboolean
  | PTint -> Tint
  | PTident s -> begin
    match Hashtbl.find_opt classes s.id with
    | None -> error ~loc "The class %s don't exist" s.id
    | Some cls -> Tclass cls
  end

let get_typ_opt (classes : classes) : pexpr_typ option -> typ = function
  | None -> Tvoid
  | Some typ -> get_typ classes typ

let cst_to_typ : constant -> typ = function
  | Cbool _ -> Tboolean
  | Cint _ -> Tint
  | Cstring _ -> Tclass class_String

(* Conversion of constructions *)

let pparams_to_vars (classes : classes) (params : pparam list) : var list =
  List.map (fun (typ, name) -> make_var name.id (get_typ classes typ) ~-1) params
