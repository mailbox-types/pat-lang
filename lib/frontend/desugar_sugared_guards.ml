(*
    free(x) |-> M ---> empty(x) |-> free(x)
    fail(M)[A]    ---> guard M : 0 { fail[A] }
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

        method! visit_expr env expr_with_pos =
            let open Sugar_ast in
            let open Source_code in
            let expr_node = WithPos.node expr_with_pos in
            match expr_node with
            | SugarFail (e, ty) ->
              let new_target = self#visit_expr env e in
              let new_guard = Guard {
                target = new_target;
                pattern = Type.Pattern.Zero;
                guards = [WithPos.make ~pos:(WithPos.pos new_target) (Fail ty)];
                iname = None
              } in
              let new_expr_node = Annotate (WithPos.make ~pos:(WithPos.pos new_target) new_guard, ty) in
              { expr_with_pos with node = new_expr_node }
            | _ -> super#visit_expr env expr_with_pos
        
        method visit_t _env x = x
    end

let desugar =
    visitor#visit_program ()
