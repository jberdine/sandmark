let num_domains = try int_of_string Sys.argv.(1) with _ -> 1
let n_times = try int_of_string Sys.argv.(2) with _ -> 2
let board_size = try int_of_string Sys.argv.(3) with _ -> 1024

module T = Domainslib.Task

(* setup board buffers; rg contains initial state *)
let rg =
  ref (Array.init board_size (fun _ -> Array.init board_size (fun _ -> Random.int 2)))
let rg' =
  ref (Array.init board_size (fun _ -> Array.make board_size 0))

let get g x y =
  try g.(x).(y)
  with _ -> 0
  [@@inline]

let neighbourhood g x y =
  (get g (x-1) (y-1)) +
  (get g (x-1) (y  )) +
  (get g (x-1) (y+1)) +
  (get g (x  ) (y-1)) +
  (get g (x  ) (y+1)) +
  (get g (x+1) (y-1)) +
  (get g (x+1) (y  )) +
  (get g (x+1) (y+1))
  [@@inline]

let next_cell g x y =
  let n = neighbourhood g x y in
  match g.(x).(y), n with
  | 1, 0 | 1, 1                      -> 0  (* lonely *)
  | 1, 4 | 1, 5 | 1, 6 | 1, 7 | 1, 8 -> 0  (* overcrowded *)
  | 1, 2 | 1, 3                      -> 1  (* lives *)
  | 0, 3                             -> 1  (* get birth *)
  | _ (* 0, (0|1|2|4|5|6|7|8) *)     -> 0  (* barren *)

let print g =
  let buf = Bytes.create board_size in
  for x = 0 to board_size - 1 do
    for y = 0 to board_size - 1 do
      if g.(x).(y) = 0
      then Bytes.set buf y '.'
      else Bytes.set buf y 'o'
    done;
    print_endline (Bytes.unsafe_to_string buf)
  done;
  print_endline ""

let next pool =
  let g = !rg in
  let new_g = !rg' in
  T.run pool (fun _ ->
  T.parallel_for ~start:0 ~finish:(board_size - 1)
    ~body:(fun x ->
      for y = 0 to board_size - 1 do
        new_g.(x).(y) <- next_cell g x y
      done) pool);
  rg := new_g;
  rg' := g


let rec repeat pool n =
  match n with
  | 0-> ()
  | _-> next pool; repeat pool (n-1)

let ()=
  let pool = T.setup_pool ~num_domains:(num_domains - 1) () in
  (* print !rg; *)
  repeat pool n_times;
  (* print !rg; *)
  T.teardown_pool pool

