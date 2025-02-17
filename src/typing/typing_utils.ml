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

let type_object = Tclass class_Object

let type_string = Tclass class_String

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

let rec ( <=* ) (typ1 : typ) (typ2 : typ) : bool =
  Printf.printf "Comparing %s and %s\n" (typ_to_string typ1) (typ_to_string typ2);
  match (typ1, typ2) with
  | Tnull, _ -> true
  | Tint, Tint | Tboolean, Tboolean -> true
  | Tclass _, Tclass { class_name = "Object" } -> true
  | Tclass c1, Tclass c2 ->
    if c1.class_name = c2.class_name then true
    else if c1.class_name = "Object" then false
    else Tclass c1.class_extends <=* typ2
  | _ -> false

let ( <=>* ) (typ1 : typ) (typ2 : typ) : bool = typ1 <=* typ2 || typ2 <=* typ1

(* Env *)

(* Check functions *)

let check_type ?(loc = dummy_loc) (typ1 : typ) (typ2 : typ) =
  if typ1 <>* typ2 then
    error ~loc "Type %s expected, but got %s" (typ_to_string typ1) (typ_to_string typ2)

let check_subtype ?(loc = dummy_loc) (typ1 : typ) (typ2 : typ) =
  if not (typ1 <=* typ2) then
    error ~loc "Type %s is not a subtype of %s" (typ_to_string typ1) (typ_to_string typ2)

let check_equiv_type ?(loc = dummy_loc) (typ1 : typ) (typ2 : typ) =
  if not (typ1 <=>* typ2) then
    error ~loc "Type %s is not equivalent to %s" (typ_to_string typ1) (typ_to_string typ2)

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

let has_method (id : string) (c : class_) : bool = Hashtbl.mem c.class_methods id

let exist_class (classes : classes) (c : class_) : bool = Hashtbl.mem classes c.class_name

(* Check functions *)

let check_is_class ~loc (t : typ) =
  if not @@ is_class_type t then error ~loc "We expected an expression of type Class here"

let check_is_class_or_null ~loc (t : typ) =
  if not (is_class_type t || t =* Tnull) then
    error ~loc "We have type %s, but Class or Null expected" (typ_to_string t)

let check_exist_class ~loc (classes : classes) (c : class_) : unit =
  if not @@ exist_class classes c then error ~loc "Class %s not exist" c.class_name

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
  | Cstring _ -> type_string

(* Conversion of constructions *)

let pparams_to_vars (classes : classes) (params : pparam list) : var list =
  List.map (fun (typ, name) -> make_var name.id (get_typ classes typ) ~-1) params
