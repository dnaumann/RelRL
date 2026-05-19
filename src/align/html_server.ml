
open Http_server

(* ---- HTML renderer ------------------------------------------------------ *)

let html_escape s =
  let buf = Buffer.create (String.length s) in
  String.iter (function
    | '<' -> Buffer.add_string buf "&lt;"
    | '>' -> Buffer.add_string buf "&gt;"
    | '&' -> Buffer.add_string buf "&amp;"
    | c   -> Buffer.add_char buf c) s;
  Buffer.contents buf

let build_html lmod lmeth rmod rmeth bicom_str =
  let lines = String.split_on_char '\n' bicom_str in
  let buf = Buffer.create 4096 in
  let p fmt = Printf.bprintf buf fmt in
  p "<!DOCTYPE html>\n";
  p "<html lang=\"en\">\n";
  p "<head>\n";
  p "  <meta charset=\"utf-8\">\n";
  p "  <title>Alignment: %s.%s | %s.%s</title>\n" lmod lmeth rmod rmeth;
  p "  <style>\n";
  p "    body{font-family:monospace;background:#1e1e1e;color:#d4d4d4;margin:2em}\n";
  p "    h1{color:#9cdcfe;font-size:1.1em;margin-bottom:1em}\n";
  p "    .code{display:table;border-collapse:collapse}\n";
  p "    .line{display:table-row}\n";
  p "    .ln{display:table-cell;text-align:right;padding:0 1em 0 0;color:#858585;";
  p "user-select:none;border-right:1px solid #3c3c3c;min-width:3em}\n";
  p "    .src{display:table-cell;padding:0 0 0 1em;white-space:pre}\n";
  p "  </style>\n";
  p "</head>\n";
  p "<body>\n";
  p "  <h1>Alignment: %s.%s &nbsp;|&nbsp; %s.%s</h1>\n" lmod lmeth rmod rmeth;
  p "  <div class=\"code\">\n";
  List.iteri (fun i line ->
    p "    <div class=\"line\">";
    p "<span class=\"ln\">%d</span>" (i + 1);
    p "<span class=\"src\">%s</span>" (html_escape line);
    p "</div>\n"
  ) lines;
  p "  </div>\n";
  p "</body>\n</html>\n";
  Buffer.contents buf

let emit_html lmod lmeth rmod rmeth bicom_str output_file =
  let html = build_html lmod lmeth rmod rmeth bicom_str in
  let oc = open_out output_file in
  output_string oc html;
  close_out oc;
  Printf.printf "HTML written to %s\n%!" output_file


let http_ok_html body =
  Printf.sprintf
    "HTTP/1.1 200 OK\r\nContent-Type: text/html; charset=utf-8\r\nContent-Length: %d\r\nAccess-Control-Allow-Origin: *\r\nConnection: close\r\n\r\n%s"
    (String.length body) body


let handle_html_client html fd =
  let open Lwt.Infix in
  let buf = Bytes.create 4096 in
  Lwt.finalize
    (fun () ->
      Lwt_unix.read fd buf 0 4096 >>= fun n ->
      let req  = Bytes.sub_string buf 0 n in
      let line = first_line req in
      let response = if is_get_bicom line then http_ok_html html else http_not_found in
      let rbytes = Bytes.of_string response in
      Lwt_unix.write fd rbytes 0 (Bytes.length rbytes) >>= fun _ ->
      Lwt.return ())
    (fun () -> Lwt_unix.close fd)

let start_html_server html port =
  let open Lwt.Infix in
  let addr = Unix.ADDR_INET (Unix.inet_addr_loopback, port) in
  let server_fd = Lwt_unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Lwt_unix.setsockopt server_fd Unix.SO_REUSEADDR true;
  Lwt_unix.bind server_fd addr >>= fun () ->
  Lwt_unix.listen server_fd 128;
  Printf.printf "Alignment viewer running on http://localhost:%d/bicom\n%!" port;
  let rec loop () =
    Lwt_unix.accept server_fd >>= fun (client_fd, _) ->
    Lwt.async (fun () -> handle_html_client html client_fd);
    loop ()
  in
  loop ()
