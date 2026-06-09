let bicommand_to_string bicom =
  let buf = Buffer.create 256 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_margin fmt 80;
  Pretty.pp_bicommand fmt bicom;
  Format.pp_print_flush fmt ();
  Buffer.contents buf
