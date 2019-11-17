open Core

let min_iter = 1_000_000

let random_string () =
  let size = 32 in
  let s = Bytes.create size in
  for i = 0 to size - 1 do
    let c = Option.value_exn (Char.of_int (Random.int 254)) in
    Bytes.set s i c;
  done;
  Bytes.to_string s

let random_array size mk k =
  let s = Hash_set.create ~size k () in
  while Hash_set.length s < size do
    Hash_set.add s (mk ())
  done;
  Hash_set.to_array s

let bench_add cmp k v =
  let kv = Option.value_exn (Array.zip k v) in
  let st = Time.now () in
  let m =
    Array.fold kv ~init:(Map.empty cmp)
      ~f:(fun m (k, v) -> Map.set m ~key:k ~data:v)
  in
  let en = Time.now () in
  (m, Time.diff en st)

let bench_find m k =
  let st = Time.now () in
  let i = ref 0 in
  let len = Array.length k in
  while !i < min_iter do
    assert (Option.is_some (Map.find m (Array.unsafe_get k (!i mod len))));
    inc i
  done;
  let en = Time.now () in
  Time.diff en st

let bench_remove m k =
  let st = Time.now () in
  let m = Array.fold k ~init:m ~f:(fun m k -> Map.remove m k) in
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
  let str t sz = sprintf "%g" (Time.Span.to_ns t /. float sz) in
  match Sys.argv.(2) with
    "ptr" -> begin
      let mk () = Random.int Int.max_value in
      let k = random_array size mk (module Int) in
      let ks = random_array size mk (module Int) in
      let v = random_array size mk (module Int) in
      Array.sort ~compare:Int.compare ks;
      let (m, add) = bench_add (module Int) k v in
      let (_, adds) = bench_add (module Int) ks v in
      let find = bench_find m k in
      let rm = bench_remove m k in
      printf "%d,%s,%s,%s,%s,%s,%s\n%!"
        size (str add size) (str adds size) "0."
        (str find (Int.max min_iter size)) "0" (str rm size)
    end
  | "str" -> begin
      let k = random_array size random_string (module String) in
      let ks = random_array size random_string (module String) in
      let v = random_array size random_string (module String) in
      Array.sort ~compare:String.compare ks;
      let (m, add) = bench_add (module String) k v in
      let (_, adds) = bench_add (module String) ks v in
      let find = bench_find m k in
      let rm = bench_remove m k in
      printf "%d,%s,%s,%s,%s,%s,%s\n%!"
        size (str add size) (str adds size) "0."
        (str find (Int.max min_iter size)) "0" (str rm size)
    end
  | _ -> failwith "invalid kind. Allowed kinds: [ptr, str]"
