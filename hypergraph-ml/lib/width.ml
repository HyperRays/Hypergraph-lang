(* Terminal display width, UAX #11.

   Rows align by how many CELLS a string occupies, not how many characters it
   has: "日本橋" is three characters and six cells, so measuring by character
   count skews every column to its right. Padding has to use the same measure,
   which is why the renderer builds its own padding rather than using a
   width-directed format.

   Two classes stay imperfect here, as they do in any implementation, because
   terminals themselves disagree: UAX #11 'ambiguous' characters such as Greek
   and Cyrillic, where this takes the narrow reading, and ZWJ emoji sequences,
   which measure per scalar rather than per rendered glyph. *)

(* Codepoints of a UTF-8 string. Malformed bytes count as one each rather than
   raising: this measures text for display, and refusing to print is worse than
   printing it slightly wrong. *)
let codepoints s =
  let n = String.length s in
  let rec go i acc =
    if i >= n then List.rev acc
    else
      let c = Char.code s.[i] in
      let len, cp =
        if c < 0x80 then (1, c)
        else if c land 0xE0 = 0xC0 && i + 1 < n then (2, c land 0x1F)
        else if c land 0xF0 = 0xE0 && i + 2 < n then (3, c land 0x0F)
        else if c land 0xF8 = 0xF0 && i + 3 < n then (4, c land 0x07)
        else (1, c)
      in
      let cp =
        if len = 1 then cp
        else
          let rec cont k acc =
            if k >= len then acc
            else cont (k + 1) ((acc lsl 6) lor (Char.code s.[i + k] land 0x3F))
          in
          cont 1 cp
      in
      go (i + len) (cp :: acc)
  in
  go 0 []

let in_range cp (lo, hi) = cp >= lo && cp <= hi

(* Combining marks and format characters occupy no cell of their own. *)
let zero_width =
  [ (0x0300, 0x036F); (0x0483, 0x0489); (0x0591, 0x05BD); (0x0610, 0x061A);
    (0x064B, 0x065F); (0x0670, 0x0670); (0x06D6, 0x06DC); (0x0E31, 0x0E31);
    (0x0E34, 0x0E3A); (0x0E47, 0x0E4E); (0x200B, 0x200F); (0x2028, 0x202E);
    (0x20D0, 0x20F0); (0xFE00, 0xFE0F); (0xFE20, 0xFE2F); (0xFEFF, 0xFEFF) ]

(* East Asian Wide and Fullwidth. *)
let wide =
  [ (0x1100, 0x115F); (0x2E80, 0x303E); (0x3041, 0x33FF); (0x3400, 0x4DBF);
    (0x4E00, 0x9FFF); (0xA000, 0xA4CF); (0xA960, 0xA97F); (0xAC00, 0xD7A3);
    (0xF900, 0xFAFF); (0xFE10, 0xFE19); (0xFE30, 0xFE6F); (0xFF00, 0xFF60);
    (0xFFE0, 0xFFE6); (0x16FE0, 0x16FE4); (0x17000, 0x18AFF);
    (0x1B000, 0x1B12F); (0x1F004, 0x1F004); (0x1F0CF, 0x1F0CF);
    (0x1F18E, 0x1F18E); (0x1F191, 0x1F19A); (0x1F200, 0x1F320);
    (0x1F32D, 0x1F335); (0x1F337, 0x1F37C); (0x1F37E, 0x1F393);
    (0x1F3A0, 0x1F3CA); (0x1F3CF, 0x1F3D3); (0x1F3E0, 0x1F3F0);
    (0x1F3F4, 0x1F3F4); (0x1F3F8, 0x1F43E); (0x1F440, 0x1F440);
    (0x1F442, 0x1F4FC); (0x1F4FF, 0x1F53D); (0x1F54B, 0x1F54E);
    (0x1F550, 0x1F567); (0x1F5A4, 0x1F5A4); (0x1F5FB, 0x1F64F);
    (0x1F680, 0x1F6C5); (0x1F6CC, 0x1F6CC); (0x1F6D0, 0x1F6D2);
    (0x1F6EB, 0x1F6EC); (0x1F6F4, 0x1F6FC); (0x1F7E0, 0x1F7EB);
    (0x1F90C, 0x1F93A); (0x1F93C, 0x1F945); (0x1F947, 0x1F9FF);
    (0x1FA70, 0x1FAFF); (0x20000, 0x2FFFD); (0x30000, 0x3FFFD) ]

let char_width cp =
  if cp = 0 then 0
  else if List.exists (in_range cp) zero_width then 0
  else if List.exists (in_range cp) wide then 2
  else 1

let width s = List.fold_left (fun n cp -> n + char_width cp) 0 (codepoints s)

(* Right-align to a display width. Padding must use the same measure the width
   was derived from, or measuring correctly buys nothing. *)
let rpad s w = String.make (max 0 (w - width s)) ' ' ^ s
