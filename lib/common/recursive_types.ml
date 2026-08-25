(* Central registry of recursive type definitions.
   User-defined types (from `data` decls)
   added at parse time via [register]. *)
open Common_types
type binder_source =
    | Param of int    (* the i-th type parameter *)
    | Self            (* the recursive type itself *)
    | Fixed of Type.t  (* a concrete base type, e.g. Int, Bool *)

type constructor_def = {
    ctor_name: string;
    binder_sources: binder_source list;
}

type rec_type_def = {
    type_name: string;
    param_count: int;
    constructors: constructor_def list;
}

let inl_constructor = "Inl"
let inr_constructor = "Inr"
let nil_constructor = "Nil"
let cons_constructor = "Cons"

(* Built-in recursive types *)
let builtin_rec_types = [
    { type_name = sum_type_name; param_count = 2;
      constructors = [
          { ctor_name = inl_constructor; binder_sources = [Param 0] };
          { ctor_name = inr_constructor; binder_sources = [Param 1] };
      ] };
    { type_name = list_type_name; param_count = 1;
      constructors = [
          { ctor_name = nil_constructor; binder_sources = [] };
          { ctor_name = cons_constructor; binder_sources = [Param 0; Self] };
      ] };
]

(* Mutable registry, starting with built-ins, extended by data decls *)
let registry : rec_type_def list ref = ref builtin_rec_types

(* Keyword table for lexer, maps source names to constructor names.
   Rebuilt whenever registry changes. *)
let keyword_table : (string, string) Hashtbl.t = Hashtbl.create 32

let rebuild_keyword_table () =
    Hashtbl.clear keyword_table;
    List.iter (fun def ->
        List.iter (fun c ->
            (* SJF TODO: Would be good to get rid of this and have all constructors uppercase *)
            let lc = String.lowercase_ascii c.ctor_name in
            Hashtbl.replace keyword_table lc c.ctor_name;
            (* Also register original case if different *)
            if lc <> c.ctor_name then
                Hashtbl.replace keyword_table c.ctor_name c.ctor_name
        ) def.constructors
    ) !registry

let () = rebuild_keyword_table ()

(* Reset to built-ins only. Call between parsing different files. *)
let reset () =
    registry := builtin_rec_types;
    rebuild_keyword_table ()

(* Look up source name in keyword table.
   Returns Some ctor_name if known constructor keyword. *)
let find_constructor_keyword src =
    Hashtbl.find_opt keyword_table src

(* Reserved names that cannot be used as user-defined data type or constructor names *)
let reserved_names = ["Int"; "Bool"; "String"; "Atom"; "Unit"]

(* Register a new user-defined type. Raises Errors.Parse_error on conflicts. *)
let register def pos_list =
    (* Check type name isn't a reserved built-in type name *)
    let () =
        if List.mem def.type_name reserved_names then
            raise (Errors.Parse_error
                (Format.sprintf "'%s' is a reserved type name and cannot be redefined"
                    def.type_name,
                 pos_list))
    in
    (* Check constructor names don't conflict with reserved names *)
    let () =
        List.iter (fun c ->
            if List.mem c.ctor_name reserved_names then
                raise (Errors.Parse_error
                    (Format.sprintf "Constructor name '%s' conflicts with a reserved type name"
                        c.ctor_name,
                     pos_list))
        ) def.constructors
    in
    (* Check type name doesn't conflict with existing types *)
    let () =
        if List.exists (fun d -> d.type_name = def.type_name) !registry then
            raise (Errors.Parse_error
                (Format.sprintf "Data type name '%s' is already defined" def.type_name,
                 pos_list))
    in
    (* Check constructor names don't conflict with existing constructors *)
    let () =
        List.iter (fun c ->
            match List.find_opt (fun d ->
                List.exists (fun ec -> ec.ctor_name = c.ctor_name) d.constructors
            ) !registry with
            | Some owner ->
                raise (Errors.Parse_error
                    (Format.sprintf "Constructor name '%s' is already defined for type '%s'"
                        c.ctor_name owner.type_name,
                     pos_list))
            | None -> ()
        ) def.constructors
    in
    (* Check constructor names don't conflict with existing type names *)
    let all_existing_types = List.map (fun d -> d.type_name) !registry in
    let () =
        List.iter (fun c ->
            if List.mem c.ctor_name all_existing_types then
                raise (Errors.Parse_error
                    (Format.sprintf "Constructor name '%s' conflicts with an existing type name"
                        c.ctor_name,
                     pos_list))
        ) def.constructors
    in
    (* Check type name doesn't conflict with existing constructor names *)
    let () =
        match List.find_opt (fun d ->
            List.exists (fun c -> c.ctor_name = def.type_name) d.constructors
        ) !registry with
        | Some owner ->
            raise (Errors.Parse_error
                (Format.sprintf
                    "Data type name '%s' conflicts with a constructor of the same name in type '%s'"
                    def.type_name owner.type_name,
                 pos_list))
        | None -> ()
    in
    registry := def :: !registry;
    rebuild_keyword_table ()

(* Get all (source_name, ctor_name) pairs for building lexer keyword tables. *)
let constructor_keywords () =
    List.concat_map (fun def ->
        List.concat_map (fun c ->
            let lc = String.lowercase_ascii c.ctor_name in
            if lc <> c.ctor_name then
                [(lc, c.ctor_name); (c.ctor_name, c.ctor_name)]
            else
                [(lc, c.ctor_name)]
        ) def.constructors
    ) !registry

(* Get all type names for building lexer/parser tables. *)
let type_names () =
    List.map (fun def -> def.type_name) !registry

(* Look up recursive type definition by type name. *)
let find_type name =
    List.find_opt (fun d -> d.type_name = name) !registry

(* Look up rec type def and constructor def for constructor name. *)
let find_constructor ctor_name =
    List.find_map (fun def ->
        List.find_opt (fun c -> c.ctor_name = ctor_name) def.constructors
        |> Option.map (fun c -> (def, c))
    ) !registry

(* Instantiate binder types for a constructor, given type parameters
   and self type. *)
let instantiate_binder_types params self_ty binder_sources =
    List.map (function
        | Param i -> List.nth params i
        | Self -> self_ty
        | Fixed ty -> ty
    ) binder_sources

(* Get all (constructor_name, binder_types) pairs for recursive type,
   given type parameters, self type, and converter for Fixed types. *)
let constructor_types def params self_ty =
    List.map (fun ctor ->
        (ctor.ctor_name,
         instantiate_binder_types params self_ty ctor.binder_sources)
    ) def.constructors

(* Whether constructor has any Self binder sources.
   Important as used by gen_constraints to decide whether to apply make_returnable. *)
let has_self_source ctor =
    List.exists (function Self -> true | Param _ | Fixed _ -> false) ctor.binder_sources
