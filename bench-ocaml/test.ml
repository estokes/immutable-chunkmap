open Core

let random_array size = Array.init size (fun _ -> Random.int Int.max_value)

let bench_add v =
  let st = Time.now () in
  let m =
    Array.fold v ~init:(Map.empty (module Int)) ~f:(fun m k ->
      Map.set m ~key:k ~data:k)
  in
  let en = Time.now () in
  (m, Time.diff en st)

let bench_add_sorted v =
  let st = Time.now () in
  Array.sort ~cmp:Int.compare v;
  let m =
    Array.fold v ~init:(Map.empty (module Int)) ~f:(fun m k ->
      Map.set m ~key:k ~data:k)
  in
  let en = Time.now () in
  (m, Time.diff en st)

let bench_find m v =
  let st = Time.now () in
  for i = 0 to Array.length v - 1 do
    let k = Array.unsafe_get v i in
    assert (Option.value_exn (Map.find m k) = k)
  done;
  let en = Time.now () in
  Time.diff en st

let bench_remove m v =
  let st = Time.now () in
  let m =
    Array.fold v ~init:m ~f:(fun m k ->
      Map.remove m k)
  in
  if Map.length m <> 0 then failwith "remove is broken";
  let en = Time.now () in
  Time.diff en st

let () =
  let size =
    if Array.length Sys.argv = 2 then Int.of_string Sys.argv.(1)
    else begin
      printf "usage: test <size>\n%!";
      exit 0
    end
  in
  let v = random_array size in
  let (m, add) = bench_add v in
  let (_, adds) = bench_add_sorted (random_array size) in
  let find = bench_find m v in
  let rm = bench_remove m v in
  let str t = sprintf "%gns" (Time.Span.to_ns t /. float size) in
  printf "add: %s, adds: %s, find: %s, remove: %s\n%!"
    (str add) (str adds) (str find) (str rm)
