module Spec.Adler32

open FStar.Mul

open FStar.HyperStack.ST

module C = LowStar.ConstBuffer

module U8 = FStar.UInt8

module U32 = FStar.UInt32

module S = FStar.Seq



(*
A = 1 + D1 + D2 + ... + Dn (mod 65521)

B = (1 + D1) + (1 + D1 + D2) + ... + (1 + D1 + D2 + ... + Dn) (mod 65521)
  = n×D1 + (n−1)×D2 + (n−2)×D3 + ... + Dn + n (mod 65521)

Adler32(D) = B × 65536 + A
*)

noextract
let rec sum_plus_one (data: S.seq U8.t) : Tot nat (decreases (S.length data)) =
  match S.length data with
  | 0 -> 1
  | _ -> (U8.v (S.head data)) + sum_plus_one (S.tail data)

noextract
let rec weighted_sum_plus_len (data: S.seq U8.t) : Tot nat (decreases (S.length data)) =
  match S.length data with
  | 0 -> 0
  | _ -> 1 + ((S.length data) * (U8.v (S.head data))) + weighted_sum_plus_len (S.tail data)

noextract
let adler32 (data: S.seq U8.t) : Tot nat =
  let a:nat = sum_plus_one (data) % 65521 in
  let b:nat = weighted_sum_plus_len (data) % 65521 in
  (b * (pow2 16)) + a

#push-options "--max_fuel 20 --z3rlimit 20"

noextract
let test1_spec_adler32 () : unit =
  let test_data:S.seq U8.t =
    S.seq_of_list [U8.uint_to_t 4; U8.uint_to_t 1; U8.uint_to_t 6; U8.uint_to_t 3; U8.uint_to_t 10]
  in
  assert (weighted_sum_plus_len test_data == 63);
  assert (sum_plus_one test_data == 25);
  assert (adler32 test_data == 4128793); // 4128793 = 63 * (2^16) + 25
  ()

#pop-options

noextract
let test2_spec_adler32 () : unit =
  let test_data:S.seq U8.t = S.seq_of_list [] in
  assert (weighted_sum_plus_len test_data == 0);
  assert (sum_plus_one test_data == 1);
  assert (adler32 test_data == 1); // 1 = 0 * (2^16) + 1
  ()

noextract
let test3_spec_adler32 () : unit =
  let test_data:S.seq U8.t = S.seq_of_list [U8.uint_to_t 1] in
  assert (weighted_sum_plus_len test_data == 2);
  assert (sum_plus_one test_data == 2);
  assert (adler32 test_data == 131074); // 131074 = 2 * (2^16) + 2
  ()