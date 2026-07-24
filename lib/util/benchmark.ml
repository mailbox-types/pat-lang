(* Utility functions used for benchmarking. *)

let time f =
  let start = Unix.gettimeofday () in
  let fxy = f () in
  let ms = (Unix.gettimeofday () -. start) *. 1000.0 in 
  (ms, fxy)

let rec repeat n acc_ms f =
  if n <= 0 then (
    acc_ms
  )
  else (
    let (ms, _) = time f in
    (* Print.printf "Run #%d complete in %.2fms.\n" n ms; *)
    (* flush stdout; *)
    repeat (n - 1) (acc_ms +. ms) f
  )

let benchmark n f = 
  (* Printf.printf "Starting benchmark with %d run(s)..\n" n; *)
  flush stdout;
  let total_ms = repeat n 0.0 f in
  Printf.printf "%.2f" (total_ms /. (float_of_int n))
