(* Import *)

open X86_64
open Ast

(* Debug *)

let debug = ref false

let debug_text case text =
  if !debug then
    comment ""
    ++ comment (" Début " ^ case ^ " :")
    ++ comment "" ++ text ++ comment ""
    ++ comment (" Fin " ^ case ^ " :")
    ++ comment ""
  else text

(* Label *)

let label_print_function = "M_print_string"

let label_malloc_function = "M_malloc"

let label_print_data = ".D_print_string"

let label_main = "M_Main_main"

let get_label_meth cls meth = Format.sprintf "M_%s_%s" cls.class_name meth.meth_name |> label

let get_name_constr cls = Format.sprintf "M_%s_%s" cls.class_name cls.class_name

let get_label_class cls = Format.sprintf "C_%s" cls.class_name |> label

let get_ilab_class cls = Format.sprintf "C_%s" cls.class_name |> ilab

(* Data Queue *)

type data_queue = (string * constant) Queue.t

(* Type *)

let class_String = Typing_utils.class_String

let is_type_void = function Tvoid -> true | _ -> false

let make_expr = Typing_utils.make_expr

let make_var = Typing_utils.make_var

(* Return *)

let rec have_return = function
  | Sreturn _ -> true
  | Sif (_, s1, s2) -> have_return s1 && have_return s2
  | Sblock block -> List.exists have_return block
  | _ -> false

(* Attributes *)

let get_nb_attribute cls =
  let rec loop cls cpt =
    if cls.class_name = "Object" then cpt
    else loop cls.class_extends (cpt + Hashtbl.length cls.class_attributes)
  in
  loop cls 0

(* Get descriptors *)

let get_descriptors (descriptors : (string, data) Hashtbl.t) : data =
  Hashtbl.fold (fun _ v acc -> acc ++ v) descriptors nop
