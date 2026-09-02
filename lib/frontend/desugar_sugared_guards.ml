(*
    free(x) |-> M ---> empty(x) |-> free(x)
 *)
open Common

let visitor =
    object(self)
        inherit [_] Sugar_ast.map as super

        method! visit_guard env guard_with_pos =
            let open Sugar_ast in
            let open Source_code in
            let guard_node = WithPos.node guard_with_pos in
            match guard_node with
                | GFree e ->
                    let var = "_gf" in
                    let e = self#visit_expr env e in
                    let new_guard_node = Empty (var, (WithPos.make (Seq (WithPos.make (Free (WithPos.make (Var var))), e)))) in
                    { guard_with_pos with node = new_guard_node }
                | _ -> super#visit_guard env guard_with_pos
        
        method visit_t _env x = x
    end

let desugar =
    visitor#visit_program ()
