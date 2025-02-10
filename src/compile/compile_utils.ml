(* Import *)

open X86_64
open Ast

(* Debug *)

let debug = ref false

(* Label *)

let label_print_function = "M_print_string"

let label_print_data = ".D_print_string"

let label_main = "M_Main_main"

let get_label_meth cls meth = Format.sprintf "M_%s_%s" cls.class_name meth.meth_name |> label

let get_label_cons cls cons = Format.sprintf "C_%s_%s" cls.class_name cons.meth_name |> label

(* Data Queue *)

type data_queue = (string * constant) Queue.t

let init_data_queue () : data_queue =
  let q = Queue.create () in
  Queue.push (label_print_data, Cstring "%s") q;
  q

(* Type *)

let is_type_void = function Tvoid -> true | _ -> false
