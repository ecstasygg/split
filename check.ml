module S = Split.Split

let numbers =
  let xs = Array.make 4097 S.Zero_nat in
  for i = 1 to 4096 do xs.(i) <- S.Suc xs.(i - 1) done;
  xs

let nat n = numbers.(n)

let integer n =
  let rec count acc = function
    | S.Zero_nat -> acc
    | S.Suc n -> count (acc + 1) n
  in
  count 0 n

let require ok message = if not ok then failwith message
let read s k offset = integer (S.read_byte s (nat k) (nat offset))
let step capacity s a = S.checked (nat 8) (nat 4096) (nat capacity) s a

let selftest () =
  let state = ref S.boot in
  let reference = Array.init 8 (fun k -> Array.init 4096 (fun b -> ((k mod 4) * 17 + b) mod 256)) in
  let random = Random.State.make [|2026; 4; 8|] in
  for i = 0 to 1023 do
    let k = Random.State.int random 8 in
    let offset = if i mod 127 = 0 then 4095 else Random.State.int random 128 in
    let byte = Random.State.int random 256 in
    let action = S.Write (nat k, nat offset, nat byte) in
    state := Option.get (step 12 !state action);
    reference.(k).(offset) <- byte;
    for j = 0 to 7 do
      require (read !state j offset = reference.(j).(offset)) "private memory refinement"
    done
  done;
  require (integer (S.frontier !state) = 12) "one copy per written page";
  List.iter (fun action -> require (step 12 !state action = None) "invalid action accepted")
    [S.Write (nat 8, nat 0, nat 1); S.Write (nat 0, nat 4096, nat 1);
     S.Write (nat 0, nat 0, nat 256); S.Read (nat 8, nat 0)];
  require (step 4 S.boot (S.Write (nat 0, nat 0, nat 1)) = None) "exhaustion accepted";
  require (Option.is_some (step 12 !state (S.Write (nat 0, nat 0, nat 1)))) "private write rejected";
  print_endline "checked 1024 model writes with boundary and exhaustion cases"

type document = { fields : string array; values : string array }

type guest = {
  pid : int;
  input : in_channel;
  output : out_channel;
  serial : out_channel;
  original : document;
  mutable state : unit S.pager_ext;
  mutable frames : int array;
  mutable available : S.nat list;
  mutable tracing : bool;
}

let names = [|"draft"; "review"; "original"|]

let index xs name =
  let rec find i =
    if i = Array.length xs then invalid_arg ("unknown name " ^ name)
    else if xs.(i) = name then i else find (i + 1)
  in
  find 0

let text value =
  if String.length value > 255 then invalid_arg "a field can contain at most 255 bytes";
  String.iter (fun c -> if Char.code c < 32 || Char.code c > 126 then
    invalid_arg "fields must contain printable ASCII text") value

let load path =
  let input = open_in path in
  let entries = Fun.protect ~finally:(fun () -> close_in input) (fun () ->
    let rec collect acc =
      match input_line input with
      | exception End_of_file -> List.rev acc
      | line when String.trim line = "" -> collect acc
      | line ->
          let at = match String.index_opt line '=' with
            | Some at -> at
            | None -> invalid_arg "expected a key followed by an equals sign and a value"
          in
          let name = String.trim (String.sub line 0 at) in
          let value = String.trim (String.sub line (at + 1) (String.length line - at - 1)) in
          require (name <> "" && not (String.contains name ' ')) "keys must be single words";
          require (not (List.mem_assoc name acc)) ("duplicate field " ^ name);
          text value;
          collect ((name, value) :: acc)
    in
    collect []) in
  require (List.length entries = 4) "a document requires exactly four fields";
  {fields = Array.of_list (List.map fst entries); values = Array.of_list (List.map snd entries)}

let close g =
  (try Unix.kill g.pid Sys.sigterm with Unix.Unix_error (Unix.ESRCH, _, _) -> ());
  ignore (Unix.waitpid [] g.pid);
  close_in_noerr g.input;
  close_out_noerr g.output;
  close_out_noerr g.serial

let event g line =
  match String.split_on_char ' ' line with
  | ["SPLIT"; operation; c] when operation = "STOP" || operation = "RUN" ->
      let c = int_of_string c in
      require (c >= 0 && c < 2) "invalid worker lifecycle";
      if g.tracing then Printf.printf "%s %s TCB\n"
        (if operation = "STOP" then "Suspend" else "Resume ") (String.capitalize_ascii names.(c))
  | ["SPLIT"; "RELEASE"; k; f; old; source; cleared] ->
      let k, f = int_of_string k, int_of_string f in
      require (k >= 0 && k < 8 && integer (S.ptable g.state (nat k)) = f)
        "released frame mismatch";
      require (int_of_string cleared = 4096) "incomplete frame scrub";
      let state, available = match S.reclaim (nat 4) (nat 8) g.state g.available (nat k) with
        | Some result -> result
        | None -> failwith "model rejected frame reclamation"
      in
      g.state <- state; g.available <- available;
      if g.tracing then begin
        Printf.printf "Unmap   VA 0x%08x  PA 0x%08x\n" (0x40000000 + k mod 4 * 4096) (int_of_string old);
        Printf.printf "Restore VA 0x%08x -> PA 0x%08x  Rights R--\n"
          (0x40000000 + k mod 4 * 4096) (int_of_string source);
        Printf.printf "Scrub   PA 0x%08x  Readback 4096 zero bytes\n" (int_of_string old);
        Printf.printf "Release Frame %d -> Reclaimed pool\n" f
      end
  | ["SPLIT"; "FAULT"; k; address; ip; fsr; source; target] ->
      let k, address, ip, fsr, source, target = int_of_string k, int_of_string address,
        int_of_string ip, int_of_string fsr, int_of_string source, int_of_string target in
      require (k >= 0 && k < 8 && ip > 0 && ip land 3 = 0 && fsr land 64 <> 0)
        "invalid write fault metadata";
      require (address land (lnot 4095) = 0x40000000 + k mod 4 * 4096)
        "fault address does not match its slot";
      require (source <> target && source land 4095 = 0 && target land 4095 = 0)
        "invalid physical copy frames";
      if g.tracing then begin
        Printf.printf "VMFault %-6s VA 0x%08x  IP 0x%08x  FSR 0x%08x\n"
          (String.capitalize_ascii names.(k / 4)) address ip fsr;
        Printf.printf "Copy    PA 0x%08x -> PA 0x%08x  Bytes 4096\n" source target;
        Printf.printf "Remap   VA 0x%08x -> PA 0x%08x  Rights RW-\n" (address land (lnot 4095)) target;
        Printf.printf "Retry   IP 0x%08x\n" ip
      end
  | ["SPLIT"; "COPY"; k; source; fresh] ->
      let k, source, fresh = int_of_string k, int_of_string source, int_of_string fresh in
      require (k >= 0 && k < 8 && fresh < 12) "invalid page copy";
      require (not (S.writable g.state (nat k))) "duplicate page copy";
      require (integer (S.ptable g.state (nat k)) = source) "copy source mismatch";
      let recycled = g.available <> [] in
      let state, available = match S.reserve (nat 4) (nat 8) (nat 12) g.state g.available (nat k) with
        | Some result -> result
        | None -> failwith "model rejected frame allocation"
      in
      require (integer (S.ptable state (nat k)) = fresh) "allocation mismatch";
      g.state <- state; g.available <- available;
      if g.tracing && recycled then Printf.printf "Acquire Frame %d <- Reclaimed pool\n" fresh
  | "SPLIT" :: "TABLE" :: frames ->
      require (List.length frames = 8) "invalid page table";
      g.frames <- Array.of_list (List.map int_of_string frames);
      Array.iteri (fun k f -> require (integer (S.ptable g.state (nat k)) = f)
        "page table differs from model") g.frames
  | ["SPLIT"; operation; k; offset; byte] when operation = "R" || operation = "W" ->
      let k, offset, byte = int_of_string k, int_of_string offset, int_of_string byte in
      require (k >= 0 && k < 8 && offset >= 0 && offset < 4096 && byte >= 0 && byte < 256)
        "invalid memory observation";
      if operation = "W" then begin
        require (S.writable g.state (nat k)) "write reached a shared page";
        g.state <- Option.get (step 12 g.state (S.Write (nat k, nat offset, nat byte)))
      end;
      require (read g.state k offset = byte) "guest memory differs from model";
      if g.tracing && operation = "W" && (offset = 0 || byte = 0) then
        Printf.printf "Store   %-6s VA 0x%08x  Byte 0x%02x\n"
          (String.capitalize_ascii names.(k / 4)) (0x40000000 + k mod 4 * 4096 + offset) byte
  | _ -> ()

let receive g expected =
  let handler = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> failwith "guest did not respond")) in
  ignore (Unix.alarm 10);
  Fun.protect ~finally:(fun () -> ignore (Unix.alarm 0); Sys.set_signal Sys.sigalrm handler) (fun () ->
    let rec collect acc =
      let raw = input_line g.input in
      let line = if String.ends_with ~suffix:"\r" raw then String.sub raw 0 (String.length raw - 1) else raw in
      output_string g.serial (line ^ "\n");
      event g line;
      if String.starts_with ~prefix:"@error " line then failwith (String.sub line 7 (String.length line - 7));
      if line = expected then List.rev acc
      else collect (if String.starts_with ~prefix:"@" line then line :: acc else acc)
    in
    collect [])

let request g line =
  output_string g.output (line ^ "\n");
  flush g.output;
  receive g "@done"

let launch image original =
  let child_input, writer = Unix.pipe () in
  let reader, child_output = Unix.pipe () in
  Unix.set_close_on_exec reader;
  Unix.set_close_on_exec writer;
  let args = [|"qemu-system-aarch64"; "-machine"; "virt,virtualization=on";
    "-cpu"; "cortex-a53"; "-m"; "2G"; "-nographic"; "-monitor"; "none";
    "-serial"; "stdio"; "-device"; "loader,file=" ^ image ^ ",addr=0x70000000,cpu-num=0"|] in
  let pid = Unix.create_process args.(0) args child_input child_output child_output in
  Unix.close child_input;
  Unix.close child_output;
  let contents f offset =
    let f, offset = integer f, integer offset in
    nat (if f < 4 && offset < String.length original.values.(f) then Char.code original.values.(f).[offset] else 0)
  in
  let g = {pid; input = Unix.in_channel_of_descr reader; output = Unix.out_channel_of_descr writer;
    serial = open_out "build/live.log"; original; state = S.initial (nat 4) contents;
    frames = Array.init 8 (fun k -> k mod 4); available = []; tracing = false} in
  try
    ignore (receive g "@ready");
    Array.iteri (fun p value -> ignore (request g (Printf.sprintf "B %d %s" p value))) original.values;
    ignore (request g "S");
    g
  with exn -> close g; raise exn

let query g target =
  let values = Array.make 4 "" and seen = Array.make 4 false in
  List.iter (fun line ->
    require (String.length line >= 8) "incomplete document response";
    let p = Char.code line.[7] - Char.code '0' in
    require (p >= 0 && p < 4 && not seen.(p)) "invalid document response";
    values.(p) <- if String.length line > 8 then String.sub line 9 (String.length line - 9) else "";
    seen.(p) <- true) (request g (Printf.sprintf "Q %d" target));
  require (Array.for_all Fun.id seen) "incomplete document";
  if target = 2 then require (values = g.original.values) "original document changed";
  values

let edit g target field value =
  if target = 2 then invalid_arg "the original is read-only";
  text value;
  ignore (request g (Printf.sprintf "E %d %d %s" target field value))

let save path document =
  let output = open_out path in
  Fun.protect ~finally:(fun () -> close_out output) (fun () ->
    Array.iteri (fun i value -> Printf.fprintf output "%s = %s\n" document.fields.(i) value) document.values)

let memory g =
  ignore (request g "M");
  print_endline "Original: 4 read-only source pages";
  Printf.printf "%-12s %14s %14s\n" "Snapshot" "Private pages" "Shared pages";
  for c = 0 to 1 do
    let private_pages = ref 0 in
    for p = 0 to 3 do if g.frames.(c * 4 + p) >= 4 then incr private_pages done;
    Printf.printf "%-12s %14d %14d\n" (String.capitalize_ascii names.(c)) !private_pages (4 - !private_pages)
  done;
  let copies = integer (S.frontier g.state) - 4 - List.length g.available in
  Printf.printf "Copy pool: %d used, %d reserved pages available\n" copies (8 - copies)

let discard g target =
  if target = 2 then invalid_arg "the original is read-only";
  ignore (request g (Printf.sprintf "D %d" target));
  require (query g target = g.original.values) "discard did not restore original"

let pool g =
  let remaining = ref g.available and count = ref 0 and samples = ref 0 in
  List.iter (fun line -> match String.split_on_char ' ' line with
    | ["@free"; f; pa; cleared] ->
        let f = int_of_string f in
        require (int_of_string cleared = 4096) "returned frame contains data";
        (match !remaining with
        | head :: tail when integer head = f -> remaining := tail
        | _ -> failwith "returned pool differs from model");
        incr count;
        Printf.printf "Frame %d  PA 0x%08x  Unmapped from clients  4096 zero bytes\n" f (int_of_string pa)
    | ["@zero"; f; offset; byte] ->
        let f, offset, byte = int_of_string f, int_of_string offset, int_of_string byte in
        require (List.exists (fun n -> integer n = f) g.available && offset = !samples mod 32 && byte = 0)
          "returned frame sample mismatch";
        incr samples;
        if offset mod 16 = 0 then Printf.printf "  %04x  " offset;
        Printf.printf "%02x " byte;
        if offset mod 16 = 15 then print_newline ()
    | _ -> failwith "invalid pool response") (request g "F");
  require (!remaining = [] && !samples = !count * 32) "incomplete pool response";
  if !count = 0 then print_endline "Reclaimed pool empty"

let mappings g =
  print_endline "Snapshot  Virtual address  Physical address  Rights";
  List.iter (fun line -> match String.split_on_char ' ' line with
    | ["@map"; k; address; physical; writable] ->
        let k = int_of_string k in
        require ((g.frames.(k) >= 4) = (writable = "1")) "mapping rights mismatch";
        Printf.printf "%-8s  0x%08x       0x%08x        %s\n"
          (String.capitalize_ascii names.(k / 4)) (int_of_string address)
          (int_of_string physical) (if writable = "1" then "RW-" else "R--")
    | _ -> failwith "invalid mapping response") (request g "P")

let peek g target field =
  let address = ref 0 and physical = ref 0 and seen = Array.make 64 false in
  let bytes = Array.make 64 0 in
  List.iter (fun line -> match String.split_on_char ' ' line with
    | ["@addr"; va; pa] -> address := int_of_string va; physical := int_of_string pa
    | ["@byte"; offset; byte] ->
        let offset, byte = int_of_string offset, int_of_string byte in
        require (offset >= 0 && offset < 64 && byte >= 0 && byte < 256) "invalid byte response";
        let expected = if target < 2 then read g.state (target * 4 + field) offset
          else if offset < String.length g.original.values.(field) then Char.code g.original.values.(field).[offset] else 0 in
        require (byte = expected) "memory dump differs from model";
        seen.(offset) <- true; bytes.(offset) <- byte
    | _ -> failwith "invalid memory response") (request g (Printf.sprintf "H %d %d" target field));
  require (Array.for_all Fun.id seen) "incomplete memory response";
  Printf.printf "%s %s  VA 0x%08x  PA 0x%08x\n" (String.capitalize_ascii names.(target))
    (String.capitalize_ascii g.original.fields.(field)) !address !physical;
  for row = 0 to 3 do
    Printf.printf "%08x  " (!address + row * 16);
    for i = 0 to 15 do Printf.printf "%02x " bytes.(row * 16 + i) done;
    print_string " ";
    for i = 0 to 15 do
      let byte = bytes.(row * 16 + i) in
      print_char (if byte >= 32 && byte < 127 then Char.chr byte else '.')
    done;
    print_newline ()
  done

let edit_value line =
  let size = String.length line in
  let rec spaces i = if i < size && line.[i] = ' ' then spaces (i + 1) else i in
  let rec words i remaining =
    if remaining = 0 then String.sub line i (size - i)
    else match String.index_from_opt line (spaces i) ' ' with
      | None -> ""
      | Some at -> words (spaces at) (remaining - 1)
  in
  words 0 3

let work image path =
  let original = load path in
  let g = launch image original in
  Fun.protect ~finally:(fun () -> close g) (fun () ->
    print_endline "Split Configuration Snapshots";
    print_endline "seL4 guest running on AArch64";
    print_endline ("Opened " ^ path ^ ". Draft and Review share the original pages.");
    print_endline "Commands: show, edit, discard, diff, maps, peek, pool, trace, memory, save, quit";
    let running = ref true in
    while !running do
      print_string "$ "; flush stdout;
      match input_line stdin with
      | exception End_of_file -> running := false
      | line ->
          try
            match String.split_on_char ' ' (String.trim line) |> List.filter ((<>) "") with
            | [] -> ()
            | ["quit"] -> running := false
            | ["clear"] -> print_string "\027[2J\027[H"
            | ["trace"; "on"] -> g.tracing <- true; print_endline "Live VM trace enabled"
            | ["trace"; "off"] -> g.tracing <- false; print_endline "Live VM trace disabled"
            | ["maps"] -> mappings g
            | ["pool"] -> pool g
            | ["discard"; name] ->
                discard g (index names name);
                print_endline ("Discarded " ^ String.capitalize_ascii name ^ " edits. Original mappings restored.")
            | ["peek"; name; field] -> peek g (index names name) (index original.fields field)
            | ["show"; name] ->
                let values = query g (index names name) in
                print_endline (String.capitalize_ascii name ^ " configuration");
                Array.iteri (fun i value -> Printf.printf "%-8s %s\n" (String.capitalize_ascii original.fields.(i)) value) values
            | "edit" :: name :: field :: _ ->
                let target = index names name and page = index original.fields field in
                let owned = target < 2 && S.writable g.state (nat (target * 4 + page)) in
                edit g (index names name) (index original.fields field) (edit_value line);
                Printf.printf "Updated %s in %s. %s\n" (String.capitalize_ascii field)
                  (String.capitalize_ascii name)
                  (if owned then "Reused its private page." else "Copied one shared page.")
            | ["diff"; name] ->
                let values = query g (index names name) and baseline = query g 2 in
                print_endline ("Changes in " ^ String.capitalize_ascii name);
                let changed = ref false in
                Array.iteri (fun i value -> if value <> baseline.(i) then begin
                  changed := true;
                  Printf.printf "%s\n  Original  %s\n  %-8s  %s\n" (String.capitalize_ascii original.fields.(i))
                    baseline.(i) (String.capitalize_ascii name) value
                end) values;
                if not !changed then print_endline "No changes"
            | ["memory"] -> memory g
            | ["save"; name; filename] ->
                save filename {original with values = query g (index names name)};
                print_endline ("Saved " ^ filename)
            | _ -> print_endline "Use show NAME, edit NAME FIELD TEXT, diff NAME, memory, save NAME FILE, or quit"
          with Invalid_argument message | Sys_error message -> print_endline (String.capitalize_ascii message)
    done)

let exercise () =
  let original = load "document" in
  let g = launch "build/loader.img" original in
  Fun.protect ~finally:(fun () -> close g) (fun () ->
    let physicals () =
      Array.of_list (List.map (fun line -> match String.split_on_char ' ' line with
        | ["@map"; _; _; address; rights] -> int_of_string address, rights
        | _ -> failwith "invalid mapping record") (request g "P"))
    in
    let initial_frames = physicals () in
    require (Array.length initial_frames = 8) "mapping count";
    for p = 0 to 3 do
      require (initial_frames.(p) = initial_frames.(p + 4) && snd initial_frames.(p) = "0")
        "initial physical sharing"
    done;
    require (query g 0 = original.values && query g 1 = original.values && query g 2 = original.values) "initial document";
    edit g 0 3 "x";
    require ((query g 0).(3) = "x") "document edit";
    let copied_frames = physicals () in
    require (fst copied_frames.(3) <> fst initial_frames.(3) && snd copied_frames.(3) = "1"
      && copied_frames.(7) = initial_frames.(7)) "physical copy isolation";
    peek g 0 3;
    peek g 1 3;
    peek g 2 3;
    require (query g 1 = original.values && query g 2 = original.values) "snapshot isolation";
    require (integer (S.frontier g.state) = 5) "first write copy";
    edit g 0 3 "";
    require ((query g 0).(3) = "") "empty field";
    require (integer (S.frontier g.state) = 5) "repeated edit allocated";
    require ((physicals ()).(3) = copied_frames.(3)) "private physical frame changed";
    edit g 0 3 (String.make 255 'x');
    require (String.length (query g 0).(3) = 255) "maximum field";
    let rejected = try edit g 0 0 (String.make 256 'x'); false with Invalid_argument _ -> true in
    require rejected "oversized field accepted";
    let before = query g 0 in
    let rejected = try ignore (request g ("E 0 0 " ^ String.make 256 'x')); false
      with Failure message -> message = "field too long" in
    require (rejected && query g 0 = before) "guest edit bounds";
    for c = 0 to 1 do
      for p = 0 to 3 do edit g c p (Printf.sprintf "snapshot %d field %d" c p) done
    done;
    require (integer (S.frontier g.state) = 12) "copy pool accounting";
    let final_frames = physicals () in
    for k = 0 to 7 do
      for j = k + 1 to 7 do
        require (fst final_frames.(k) <> fst final_frames.(j)) "private physical alias"
      done
    done;
    edit g 1 0 "updated after pool exhausted";
    require ((query g 1).(0) = "updated after pool exhausted") "private edit after exhaustion";
    require (query g 2 = original.values) "original changed";
    let values = query g 0 in
    save "build/export.txt" {original with values};
    require ((load "build/export.txt").values = values) "saved document differs";
    let rejected = try edit g 2 0 "changed"; false with Invalid_argument _ -> true in
    require rejected "original edit accepted";
    let survivor = query g 1 in
    discard g 0;
    require (List.length g.available = 4 && query g 1 = survivor) "discard isolation";
    let reset_frames = physicals () in
    for p = 0 to 3 do require (reset_frames.(p) = initial_frames.(p)) "discard mapping restore" done;
    pool g;
    for cycle = 0 to 15 do
      for p = 0 to 3 do edit g 0 p (Printf.sprintf "cycle %d field %d" cycle p) done;
      require (g.available = [] && integer (S.frontier g.state) = 12) "recycling grew pool";
      require (query g 1 = survivor && query g 2 = original.values) "recycling changed survivor";
      discard g 0
    done;
    discard g 1;
    require (List.length g.available = 8) "complete pool return";
    let recycled = fst final_frames.(7) in
    edit g 0 0 "draft now owns review frame";
    require (fst (physicals ()).(0) = recycled) "cross snapshot physical reuse";
    edit g 1 3 "review writes its old virtual address";
    require (fst (physicals ()).(7) <> recycled && (query g 0).(0) = "draft now owns review frame")
      "stale client mapping survived discard";
    discard g 0;
    discard g 1;
    pool g;
    require (query g 2 = original.values && List.length g.available = 8) "reclamation final state");
  let g = launch "build/unsafe.img" original in
  let detected = Fun.protect ~finally:(fun () -> close g) (fun () ->
    try edit g 0 3 "changed"; false with Failure message -> message = "write reached a shared page") in
  require detected "writable alias was not detected";
  print_endline "exercised edits, exports, full pool recycling and stale mapping isolation"

let () =
  Sys.catch_break true;
  try
    match Array.to_list Sys.argv with
    | [_; "--model"] -> selftest ()
    | [_; "--test"] -> exercise ()
    | [_] | [_; "work"] -> work "build/loader.img" "document"
    | [_; "work"; path] -> work "build/loader.img" path
    | _ -> invalid_arg "usage: check work DOCUMENT"
  with
  | Sys.Break -> print_newline ()
  | Failure message | Invalid_argument message | Sys_error message ->
      prerr_endline message; exit 1
  | exn -> prerr_endline (Printexc.to_string exn); exit 1
