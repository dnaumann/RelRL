
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



let start_server json port =
  let open Lwt.Infix in
  let addr = Unix.ADDR_INET (Unix.inet_addr_loopback, port) in
  let server_fd = Lwt_unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Lwt_unix.setsockopt server_fd Unix.SO_REUSEADDR true;
  Lwt_unix.bind server_fd addr >>= fun () ->
  Lwt_unix.listen server_fd 128;
  Printf.printf "Alignment server running on http://localhost:%d/bicom\n%!" port;
  let rec loop () =
    Lwt_unix.accept server_fd >>= fun (client_fd, _) ->
    Lwt.async (fun () -> handle_client json client_fd);
    loop ()
  in
  loop ()
