module Impl.Adler32

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module N = FStar.Pervasives.Native
module P = LowStar.Printf
module U32 = FStar.UInt32

open FStar.HyperStack.ST
open LowStar.BufferOps
open LowStar.Buffer

let square1 (x: U32.t): Stack U32.t (fun _ -> True) (fun _ _ _ -> True) =
  FStar.UInt32.( x *%^ x )

let square2 (x: U32.t): Stack U32.t (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let b = alloca 0ul 1ul in
  pop_frame ();
  FStar.UInt32.( x *%^ x )

let adler32 (data: buffer U8.t) (len: U32.t) : U32.t =
  let a = 1ul in
  let b = 0ul in

  a 

let main (): St Int32.t =
  push_frame ();
  P.(printf "Hello, World!\n" done);
  pop_frame ();
  0l
