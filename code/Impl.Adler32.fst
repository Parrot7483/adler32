module Impl.Adler32

open FStar.Mul

open FStar.HyperStack.ST

module B = LowStar.Buffer

module C = LowStar.ConstBuffer

module S = FStar.Seq

module HS = FStar.HyperStack

module U8 = FStar.UInt8

module U32 = FStar.UInt32

module SPEC = Spec.Adler32

noextract inline_for_extraction
let cast (d: U8.t) : U32.t = FStar.Int.Cast.uint8_to_uint32 d

#push-options "--query_stats --max_fuel 5000 --max_ifuel 5000 --z3rlimit 600"

val adler32 (data: C.const_buffer U8.t) (len: U32.t) : Stack U32.t
  (requires fun (h0: HS.mem) -> C.live h0 data /\ C.length data = U32.v len)
  (ensures fun (h0: HS.mem) (x: U32.t) (h1: HS.mem) ->
    C.live h0 data /\ C.live h1 data /\
    (*U32.v x == Spec.Adler32.adler32(C.as_seq h0 data) /\*)
    True)

let adler32 data len =
  let open LowStar.BufferOps in
  let open U32 in
  push_frame ();
  let a:B.buffer U32.t = B.alloca 1ul 1ul in
  let b:B.buffer U32.t = B.alloca 0ul 1ul in
  let inv (h: HS.mem) (i: nat) : Type0 =
    let a_nat = U32.v (B.get h a 0) in
    let b_nat = U32.v (B.get h b 0) in
    i <= U32.v len /\ B.live h a /\ B.live h b /\ C.live h data /\ a_nat < 65521 /\ b_nat < 65521 /\
    // a_nat == Spec.Adler32.sum_plus_one (S.slice (C.as_seq h data) 0 i) % 65521 /\
    // b_nat == Spec.Adler32.weighted_sum_plus_len (S.slice (C.as_seq h data) 0 i) % 65521 /\
    // b_nat * (pow2 16 ) + a_nat == Spec.Adler32.adler32 (S.slice (C.as_seq h data) 0 i) /\
    True
  in
  let body (i: U32.t{U32.v 0ul <= U32.v i /\ U32.v i < U32.v len})
      : Stack unit
        (requires fun h -> inv h (U32.v i))
        (ensures fun h0 _ h1 -> (inv h0 (U32.v i) /\ inv h1 ((U32.v i) + 1))) =
    a.(0ul) <- (a.(0ul) +^ cast (C.index data i)) %^ 65521ul;
    b.(0ul) <- (b.(0ul) +^ a.(0ul)) %^ 65521ul
  in
  C.Loops.for 0ul len inv body;
  let return:U32.t = U32.logor (U32.shift_left b.(0ul) 16ul) a.(0ul) in
  pop_frame ();
  return

#pop-options