
(* ---- Minimal HTTP/1.x server using Lwt_unix ----------------------------- *)

let http_ok body =
  Printf.sprintf
    "HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: %d\r\nAccess-Control-Allow-Origin: *\r\nConnection: close\r\n\r\n%s"
    (String.length body) body


let http_not_found =
  let body = {|{"error": "not found"}|} in
  Printf.sprintf
    "HTTP/1.1 404 Not Found\r\nContent-Type: application/json\r\nContent-Length: %d\r\nConnection: close\r\n\r\n%s"
    (String.length body) body

(* Extract the first line (request line) from a raw HTTP request. *)
let first_line s =
  match String.index_opt s '\r' with
  | Some i -> String.sub s 0 i
  | None ->
    (match String.index_opt s '\n' with
     | Some i -> String.sub s 0 i
     | None -> s)

(* Return true for GET requests targeting / or /bicom. *)
let is_get_bicom line =
  match String.split_on_char ' ' line with
  | [meth; path; _version] -> meth = "GET" && (path = "/" || path = "/bicom")
  | _ -> false

let handle_client json fd =
  let open Lwt.Infix in
  let buf = Bytes.create 4096 in
  Lwt.finalize
    (fun () ->
      Lwt_unix.read fd buf 0 4096 >>= fun n ->
      let req  = Bytes.sub_string buf 0 n in
      let line = first_line req in
      let response = if is_get_bicom line then http_ok json else http_not_found in
      let rbytes = Bytes.of_string response in
      Lwt_unix.write fd rbytes 0 (Bytes.length rbytes) >>= fun _ ->
      Lwt.return ())
    (fun () -> Lwt_unix.close fd)


let is_closed_socket_error = function
  | Unix.Unix_error (Unix.EBADF, _, _)
  | Unix.Unix_error (Unix.EINVAL, _, _)
  | Unix.Unix_error (Unix.ENOTSOCK, _, _) -> true
  | _ -> false

let run_accept_loop server_fd on_client banner =
  let open Lwt.Infix in
  let stopping = ref false in
  let request_stop _ =
    if not !stopping then begin
      stopping := true;
      Printf.printf "Shutting down server...\n%!";
      Lwt.async (fun () ->
        Lwt.catch
          (fun () -> Lwt_unix.close server_fd)
          (fun _ -> Lwt.return_unit))
    end
  in
  let sigint = Lwt_unix.on_signal Sys.sigint request_stop in
  let sigterm = Lwt_unix.on_signal Sys.sigterm request_stop in
  let rec loop () =
    Lwt.catch
      (fun () ->
         Lwt_unix.accept server_fd >>= fun (client_fd, _) ->
         Lwt.async (fun () -> on_client client_fd);
         loop ())
      (fun e ->
         if !stopping && is_closed_socket_error e then Lwt.return_unit
         else Lwt.fail e)
  in
  Printf.printf "%s\n%!" banner;
  Lwt.finalize
    loop
    (fun () ->
      Lwt_unix.disable_signal_handler sigint;
      Lwt_unix.disable_signal_handler sigterm;
      if !stopping then Lwt.return_unit
      else Lwt.catch
        (fun () -> Lwt_unix.close server_fd)
        (fun _ -> Lwt.return_unit))



let start_server json port =
  let open Lwt.Infix in
  let addr = Unix.ADDR_INET (Unix.inet_addr_loopback, port) in
  let server_fd = Lwt_unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Lwt_unix.setsockopt server_fd Unix.SO_REUSEADDR true;
  Lwt_unix.bind server_fd addr >>= fun () ->
  Lwt_unix.listen server_fd 128;
  run_accept_loop server_fd (handle_client json)
    (Printf.sprintf "Alignment server running on http://localhost:%d/bicom" port)


(* ---- Generic dispatch server (for the interactive session) -------------- *)

(* Split a request target "/path?a=1&b=2" into its path and raw query. *)
let split_target t =
  match String.index_opt t '?' with
  | Some i -> (String.sub t 0 i, String.sub t (i + 1) (String.length t - i - 1))
  | None -> (t, "")

(* Percent-decode a query component ("%20"->" ", "+"->" "). *)
let url_decode s =
  let n = String.length s in
  let buf = Buffer.create n in
  let i = ref 0 in
  while !i < n do
    (match s.[!i] with
     | '+' -> Buffer.add_char buf ' '; incr i
     | '%' when !i + 3 <= n ->
       (try
          Buffer.add_char buf (Char.chr (int_of_string ("0x" ^ String.sub s (!i + 1) 2)));
          i := !i + 3
        with _ -> Buffer.add_char buf '%'; incr i)
     | c -> Buffer.add_char buf c; incr i)
  done;
  Buffer.contents buf

(* Parse "a=1&b=2" into [("a","1"); ("b","2")], percent-decoding keys and values
   (so e.g. a relational invariant with spaces can be passed as a value). *)
let query_params q =
  if q = "" then []
  else
    String.split_on_char '&' q
    |> List.filter_map (fun kv ->
         if kv = "" then None
         else match String.index_opt kv '=' with
           | Some i -> Some (url_decode (String.sub kv 0 i),
                             url_decode (String.sub kv (i + 1) (String.length kv - i - 1)))
           | None -> Some (url_decode kv, ""))

(* Extract (method, path, query) from a raw request; the body is not needed
   since the interactive API takes its arguments in the query string. *)
let parse_request raw =
  let line = first_line raw in
  let meth, target =
    match String.split_on_char ' ' line with
    | m :: t :: _ -> (m, t)
    | [m] -> (m, "/")
    | [] -> ("GET", "/")
  in
  let path, query = split_target target in
  (meth, path, query)

let reason_phrase = function
  | 200 -> "OK"        | 400 -> "Bad Request"
  | 404 -> "Not Found" | 409 -> "Conflict"
  | 500 -> "Internal Server Error" | _ -> "OK"

let http_response status content_type body =
  Printf.sprintf
    "HTTP/1.1 %d %s\r\nContent-Type: %s\r\nContent-Length: %d\r\nAccess-Control-Allow-Origin: *\r\nConnection: close\r\n\r\n%s"
    status (reason_phrase status) content_type (String.length body) body

(* A [handler] maps a parsed request to a (status, content-type, body) triple. *)
let handle_dispatch
    (handler : meth:string -> path:string -> query:string -> int * string * string)
    fd =
  let open Lwt.Infix in
  let buf = Bytes.create 65536 in
  Lwt.finalize
    (fun () ->
      Lwt_unix.read fd buf 0 65536 >>= fun n ->
      let raw = Bytes.sub_string buf 0 n in
      let (meth, path, query) = parse_request raw in
      let (status, ctype, body) =
        try handler ~meth ~path ~query
        with e -> (500, "text/plain; charset=utf-8", Printexc.to_string e)
      in
      let response = http_response status ctype body in
      let rbytes = Bytes.of_string response in
      Lwt_unix.write fd rbytes 0 (Bytes.length rbytes) >>= fun _ ->
      Lwt.return ())
    (fun () -> Lwt_unix.close fd)

let start_dispatch_server handler port =
  let open Lwt.Infix in
  let addr = Unix.ADDR_INET (Unix.inet_addr_loopback, port) in
  let server_fd = Lwt_unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Lwt_unix.setsockopt server_fd Unix.SO_REUSEADDR true;
  Lwt_unix.bind server_fd addr >>= fun () ->
  Lwt_unix.listen server_fd 128;
  run_accept_loop server_fd (handle_dispatch handler)
    (Printf.sprintf
       "Interactive alignment server on http://localhost:%d/ (try /, /bicom, /suggest)"
       port)
