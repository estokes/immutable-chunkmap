open Core

let random_string () =
  let size = 32 in
  let s = Bytes.create size in
  for i = 0 to size - 1 do
    let c = Option.value_exn (Char.of_int (Random.int 254)) in
    Bytes.set s i c;
  done;
  s

let random_str_array size = Array.init size (fun _ -> random_string ())
let random_int_array size = Array.init size (fun _ -> Random.int Int.max_value)

let bench_add cmp v =
  let st = Time.now () in
  let m =
    Array.fold v ~init:(Map.empty cmp) ~f:(fun m k ->
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
    if Array.length Sys.argv = 4 then Int.of_string Sys.argv.(3)
    else begin
      printf "usage: test <unused> <kind> <size>\n%!";
      exit 0
    end
  in
  let str t = sprintf "%g" (Time.Span.to_ns t /. float size) in
  match Sys.argv.(2) with
    "ptr" -> begin
      let v = random_int_array size in
      let vs = random_int_array size in
      Array.sort ~compare:Int.compare vs;
      let (m, add) = bench_add (module Int) v in
      let (_, adds) = bench_add (module Int) vs in
      let find = bench_find m v in
      let rm = bench_remove m v in
      printf "%d,%s,%s,%s,%s,%s,%s\n%!"
        size (str add) (str adds) "0." (str find) "0" (str rm)
    end
  | "str" -> begin
      let v = random_str_array size in
      let vs = random_str_array size in
      let (m, add) = bench_add (module Bytes) v in
      let (_, adds) = bench_add (module Bytes) vs in
      let find = bench_find m v in
      let rm = bench_remove m v in
      printf "%d,%s,%s,%s,%s,%s,%s\n%!"
        size (str add) (str adds) "0." (str find) "0" (str rm)
    end
  | _ -> failwith "invalid kind. Allowed kinds: [ptr, str]"
