(* Terminal display width for the incidence renderer.  Malformed UTF-8 bytes
   count as one cell so diagnostics remain printable. *)

let codepoints text =
  let length = String.length text in
  let rec loop offset output =
    if offset >= length then List.rev output
    else
      let first = Char.code text.[offset] in
      let byte_count, prefix =
        if first < 0x80 then (1, first)
        else if first land 0xe0 = 0xc0 && offset + 1 < length then
          (2, first land 0x1f)
        else if first land 0xf0 = 0xe0 && offset + 2 < length then
          (3, first land 0x0f)
        else if first land 0xf8 = 0xf0 && offset + 3 < length then
          (4, first land 0x07)
        else (1, first)
      in
      let codepoint =
        let rec continuation index accumulated =
          if index >= byte_count then accumulated
          else
            continuation (index + 1)
              ((accumulated lsl 6)
              lor (Char.code text.[offset + index] land 0x3f))
        in
        continuation 1 prefix
      in
      loop (offset + byte_count) (codepoint :: output)
  in
  loop 0 []

let in_range codepoint (lower, upper) =
  codepoint >= lower && codepoint <= upper

let zero_width =
  [ (0x0300, 0x036f); (0x0483, 0x0489); (0x0591, 0x05bd);
    (0x0610, 0x061a); (0x064b, 0x065f); (0x0670, 0x0670);
    (0x06d6, 0x06dc); (0x0e31, 0x0e31); (0x0e34, 0x0e3a);
    (0x0e47, 0x0e4e); (0x200b, 0x200f); (0x2028, 0x202e);
    (0x20d0, 0x20f0); (0xfe00, 0xfe0f); (0xfe20, 0xfe2f);
    (0xfeff, 0xfeff) ]

let wide =
  [ (0x1100, 0x115f); (0x2e80, 0x303e); (0x3041, 0x33ff);
    (0x3400, 0x4dbf); (0x4e00, 0x9fff); (0xa000, 0xa4cf);
    (0xa960, 0xa97f); (0xac00, 0xd7a3); (0xf900, 0xfaff);
    (0xfe10, 0xfe19); (0xfe30, 0xfe6f); (0xff00, 0xff60);
    (0xffe0, 0xffe6); (0x16fe0, 0x16fe4); (0x17000, 0x18aff);
    (0x1b000, 0x1b12f); (0x1f004, 0x1f004); (0x1f0cf, 0x1f0cf);
    (0x1f18e, 0x1f18e); (0x1f191, 0x1f19a); (0x1f200, 0x1f320);
    (0x1f32d, 0x1f335); (0x1f337, 0x1f37c); (0x1f37e, 0x1f393);
    (0x1f3a0, 0x1f3ca); (0x1f3cf, 0x1f3d3); (0x1f3e0, 0x1f3f0);
    (0x1f3f4, 0x1f3f4); (0x1f3f8, 0x1f43e); (0x1f440, 0x1f440);
    (0x1f442, 0x1f4fc); (0x1f4ff, 0x1f53d); (0x1f54b, 0x1f54e);
    (0x1f550, 0x1f567); (0x1f5a4, 0x1f5a4); (0x1f5fb, 0x1f64f);
    (0x1f680, 0x1f6c5); (0x1f6cc, 0x1f6cc); (0x1f6d0, 0x1f6d2);
    (0x1f6eb, 0x1f6ec); (0x1f6f4, 0x1f6fc); (0x1f7e0, 0x1f7eb);
    (0x1f90c, 0x1f93a); (0x1f93c, 0x1f945); (0x1f947, 0x1f9ff);
    (0x1fa70, 0x1faff); (0x20000, 0x2fffd); (0x30000, 0x3fffd) ]

let character_width codepoint =
  if codepoint = 0 || List.exists (in_range codepoint) zero_width then 0
  else if List.exists (in_range codepoint) wide then 2
  else 1

let width text =
  List.fold_left
    (fun total codepoint -> total + character_width codepoint)
    0 (codepoints text)

let left_pad text target =
  String.make (max 0 (target - width text)) ' ' ^ text
